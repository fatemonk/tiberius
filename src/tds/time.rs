//! Date and time handling.
//!
//! When using the `tds73` feature flag together with SQL Server 2008 or later,
//! the following [`chrono`] mappings to and from the database are available:
//!
//! - `Time` -> [`NaiveTime`]
//! - `Date` -> [`NaiveDate`]
//! - `DateTime` -> [`NaiveDateTime`]
//! - `DateTime2` -> [`NaiveDateTime`]
//! - `SmallDateTime` -> [`NaiveDateTime`]
//! - `DateTimeOffset` -> [`DateTime`]
//!
//! With SQL Server 2005 and the `tds73` feature flag disabled, the mapping is
//! different:
//!
//! - `DateTime` -> [`NaiveDateTime`]
//! - `SmallDateTime` -> [`NaiveDateTime`]
//!
//! [`chrono`]: chrono/index.html
//! [`NaiveTime`]: chrono/struct.NaiveTime.html
//! [`NaiveDate`]: chrono/struct.NaiveDate.html
//! [`NaiveDateTime`]: chrono/struct.NaiveDateTime.html
//! [`DateTime`]: chrono/struct.DateTime.html

pub mod chrono;

use crate::{tds::codec::Encode, SqlReadBytes};
#[cfg(feature = "tds73")]
use byteorder::{ByteOrder, LittleEndian};
use bytes::{BufMut, BytesMut};
#[cfg(feature = "tds73")]
use futures::io::AsyncReadExt;
use serde::{Serialize, Serializer};
use std::time::{UNIX_EPOCH, Duration};

const DAYS_BETWEEN_1_AND_1970: u32 = 719162;
const DAYS_BETWEEN_1900_AND_1970: i32 = 25567;
const SECONDS_IN_HOUR: i32 = 60 * 60;
const SECONDS_IN_DAY: i32 = 24 * SECONDS_IN_HOUR;

/// A presentation of `datetime` type in the server.
///
/// # Warning
///
/// It isn't recommended to use this type directly. For dealing with `datetime`,
/// use the `chrono` feature of this crate and its `NaiveDateTime` type.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DateTime {
    days: i32,
    seconds_fragments: u32,
}

impl DateTime {
    /// Construct a new `DateTime` instance.
    pub fn new(days: i32, seconds_fragments: u32) -> Self {
        Self {
            days,
            seconds_fragments,
        }
    }

    /// Days since 1st of January, 1900 (including the negative range until 1st
    /// of January, 1753).
    pub fn days(self) -> i32 {
        self.days
    }

    /// 1/300 of a second, so a value of 300 equals 1 second (since midnight).
    pub fn seconds_fragments(self) -> u32 {
        self.seconds_fragments
    }

    pub(crate) async fn decode<R>(src: &mut R) -> crate::Result<Self>
    where
        R: SqlReadBytes + Unpin,
    {
        Ok(Self {
            days: src.read_i32_le().await?,
            seconds_fragments: src.read_u32_le().await?,
        })
    }

    pub fn timestamp(self) -> u64 {
        let days = self.days - DAYS_BETWEEN_1900_AND_1970;
        let days_in_seconds = days * SECONDS_IN_DAY;
        (days_in_seconds as f64 + ((self.seconds_fragments as f64) / 300.0)) as u64
    }
}

impl Encode<BytesMut> for DateTime {
    fn encode(self, dst: &mut BytesMut) -> crate::Result<()> {
        dst.put_i32_le(self.days);
        dst.put_u32_le(self.seconds_fragments);

        Ok(())
    }
}

impl Serialize for DateTime {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let timestamp = UNIX_EPOCH + Duration::from_secs(self.timestamp());
        let datetime = chrono::DateTime::<chrono::Utc>::from(timestamp);
        serializer.serialize_str(&datetime.format("%Y-%m-%dT%H:%M:%S").to_string())
    }
}

/// A presentation of `smalldatetime` type in the server.
///
/// # Warning
///
/// It isn't recommended to use this type directly. For dealing with
/// `smalldatetime`, use the `chrono` feature of this crate and its
/// `NaiveDateTime` type.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SmallDateTime {
    days: u16,
    seconds_fragments: u16,
}

impl SmallDateTime {
    /// Construct a new `SmallDateTime` instance.
    pub fn new(days: u16, seconds_fragments: u16) -> Self {
        Self {
            days,
            seconds_fragments,
        }
    }
    /// Days since 1st of January, 1900.
    pub fn days(self) -> u16 {
        self.days
    }

    /// 1/300 of a second, so a value of 300 equals 1 second (since midnight)
    pub fn seconds_fragments(self) -> u16 {
        self.seconds_fragments
    }

    pub(crate) async fn decode<R>(src: &mut R) -> crate::Result<Self>
    where
        R: SqlReadBytes + Unpin,
    {
        Ok(Self {
            days: src.read_u16_le().await?,
            seconds_fragments: src.read_u16_le().await?,
        })
    }

    pub fn timestamp(self) -> u64 {
        let days = self.days as i32 - DAYS_BETWEEN_1900_AND_1970;
        let days_in_seconds = days * SECONDS_IN_DAY;
        (days_in_seconds as f64 * ((self.seconds_fragments as f64) / 300.0)) as u64
    }
}

impl Encode<BytesMut> for SmallDateTime {
    fn encode(self, dst: &mut BytesMut) -> crate::Result<()> {
        dst.put_u16_le(self.days);
        dst.put_u16_le(self.seconds_fragments);

        Ok(())
    }
}

impl Serialize for SmallDateTime {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let timestamp = UNIX_EPOCH + Duration::from_secs(self.timestamp());
        let datetime = chrono::DateTime::<chrono::Utc>::from(timestamp);
        serializer.serialize_str(&datetime.format("%Y-%m-%dT%H:%M:%S").to_string())
    }
}

/// A presentation of `date` type in the server.
///
/// # Warning
///
/// It isn't recommended to use this type directly. If you want to deal with
/// `date`, use the chrono feature of this crate and its `NaiveDate` type.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[cfg(feature = "tds73")]
pub struct Date(u32);

#[cfg(feature = "tds73")]
impl Date {
    #[inline]
    /// Construct a new `Date`
    ///
    /// # Panics
    /// max value of 3 bytes (`u32::max_value() > 8`)
    pub fn new(days: u32) -> Date {
        assert_eq!(days >> 24, 0);
        Date(days)
    }

    #[inline]
    /// The number of days from 1st of January, year 1.
    pub fn days(self) -> u32 {
        self.0
    }

    pub(crate) async fn decode<R>(src: &mut R) -> crate::Result<Self>
    where
        R: SqlReadBytes + Unpin,
    {
        let mut bytes = [0u8; 4];
        src.read_exact(&mut bytes[..3]).await?;
        Ok(Self::new(LittleEndian::read_u32(&bytes)))
    }

    pub fn timestamp(self) -> u64 {
        let days = self.0 - DAYS_BETWEEN_1_AND_1970;
        (days * (SECONDS_IN_DAY as u32)) as u64
    }

    pub fn repr(self) -> String {
        let timestamp = UNIX_EPOCH + Duration::from_secs(self.timestamp());
        let datetime = chrono::DateTime::<chrono::Utc>::from(timestamp);
        datetime.format("%Y-%m-%d").to_string()
    }
}

#[cfg(feature = "tds73")]
impl Encode<BytesMut> for Date {
    fn encode(self, dst: &mut BytesMut) -> crate::Result<()> {
        let mut tmp = [0u8; 4];
        LittleEndian::write_u32(&mut tmp, self.days());
        assert_eq!(tmp[3], 0);
        dst.extend_from_slice(&tmp[0..3]);

        Ok(())
    }
}

impl Serialize for Date {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.repr())
    }
}

/// A presentation of `time` type in the server.
///
/// # Warning
///
/// It isn't recommended to use this type directly. If you want to deal with
/// `time`, use the chrono feature of this crate and its `NaiveTime` type.
#[derive(Copy, Clone, Debug)]
#[cfg(feature = "tds73")]
pub struct Time {
    increments: u64,
    scale: u8,
}

#[cfg(feature = "tds73")]
impl PartialEq for Time {
    fn eq(&self, t: &Time) -> bool {
        self.increments as f64 / 10f64.powi(self.scale as i32)
            == t.increments as f64 / 10f64.powi(t.scale as i32)
    }
}

#[cfg(feature = "tds73")]
impl Time {
    /// Construct a new `Time`
    pub fn new(increments: u64, scale: u8) -> Self {
        Self { increments, scale }
    }

    #[inline]
    /// Number of 10^-n second increments since midnight, where `n` is defined
    /// in [`scale`].
    ///
    /// [`scale`]: #method.scale
    pub fn increments(self) -> u64 {
        self.increments
    }

    #[inline]
    /// The accuracy of the increments.
    pub fn scale(self) -> u8 {
        self.scale
    }

    #[inline]
    /// Length of the field in number of bytes.
    pub(crate) fn len(self) -> crate::Result<u8> {
        Ok(match self.scale {
            0..=2 => 3,
            3..=4 => 4,
            5..=7 => 5,
            _ => {
                return Err(crate::Error::Protocol(
                    format!("timen: invalid scale {}", self.scale).into(),
                ))
            }
        })
    }

    pub(crate) async fn decode<R>(src: &mut R, n: usize, rlen: usize) -> crate::Result<Time>
    where
        R: SqlReadBytes + Unpin,
    {
        let val = match (n, rlen) {
            (0..=2, 3) => src.read_u16_le().await? as u64 | (src.read_u8().await? as u64) << 16,
            (3..=4, 4) => src.read_u32_le().await? as u64,
            (5..=7, 5) => src.read_u32_le().await? as u64 | (src.read_u8().await? as u64) << 32,
            _ => {
                return Err(crate::Error::Protocol(
                    format!("timen: invalid length {}", n).into(),
                ))
            }
        };

        Ok(Time {
            increments: val,
            scale: n as u8,
        })
    }

    pub fn repr(self) -> String {
        let total_seconds = self.increments as f64 / 10f64.powi(self.scale as i32);
        let hours = total_seconds as i32 / SECONDS_IN_HOUR;
        let hours_in_seconds = hours * SECONDS_IN_HOUR;
        let minutes = (total_seconds as i32 - hours_in_seconds) / 60;
        let seconds = total_seconds as i32 - hours_in_seconds - (minutes * 60);
        format!("{:02}:{:02}:{:02}", hours, minutes, seconds)
    }
}

#[cfg(feature = "tds73")]
impl Encode<BytesMut> for Time {
    fn encode(self, dst: &mut BytesMut) -> crate::Result<()> {
        match self.len()? {
            3 => {
                assert_eq!(self.increments >> 24, 0);
                dst.put_u16_le(self.increments as u16);
                dst.put_u8((self.increments >> 16) as u8);
            }
            4 => {
                assert_eq!(self.increments >> 32, 0);
                dst.put_u32_le(self.increments as u32);
            }
            5 => {
                assert_eq!(self.increments >> 40, 0);
                dst.put_u32_le(self.increments as u32);
                dst.put_u8((self.increments >> 32) as u8);
            }
            _ => unreachable!(),
        }

        Ok(())
    }
}

impl Serialize for Time {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.repr())
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg(feature = "tds73")]
/// A presentation of `datetime2` type in the server.
///
/// # Warning
///
/// It isn't recommended to use this type directly. For dealing with
/// `datetime2`, use the `chrono` feature of this crate and its `NaiveDateTime`
/// type.
pub struct DateTime2 {
    date: Date,
    time: Time,
}

#[cfg(feature = "tds73")]
impl DateTime2 {
    /// Construct a new `DateTime2` from the date and time components.
    pub fn new(date: Date, time: Time) -> Self {
        Self { date, time }
    }

    /// The date component.
    pub fn date(self) -> Date {
        self.date
    }

    /// The time component.
    pub fn time(self) -> Time {
        self.time
    }

    pub(crate) async fn decode<R>(src: &mut R, n: usize, rlen: usize) -> crate::Result<Self>
    where
        R: SqlReadBytes + Unpin,
    {
        let time = Time::decode(src, n, rlen as usize).await?;

        let mut bytes = [0u8; 4];
        src.read_exact(&mut bytes[..3]).await?;
        let date = Date::new(LittleEndian::read_u32(&bytes));

        Ok(Self::new(date, time))
    }

    pub fn repr(self) -> String {
        format!("{}T{}", self.date().repr(), self.time().repr())
    }
}

#[cfg(feature = "tds73")]
impl Encode<BytesMut> for DateTime2 {
    fn encode(self, dst: &mut BytesMut) -> crate::Result<()> {
        self.time.encode(dst)?;

        let mut tmp = [0u8; 4];
        LittleEndian::write_u32(&mut tmp, self.date.days());
        assert_eq!(tmp[3], 0);
        dst.extend_from_slice(&tmp[0..3]);

        Ok(())
    }
}

impl Serialize for DateTime2 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.repr())
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg(feature = "tds73")]
/// A presentation of `datetimeoffset` type in the server.
///
/// # Warning
///
/// It isn't recommended to use this type directly. For dealing with
/// `datetimeoffset`, use the `chrono` feature of this crate and its `DateTime`
/// type with the correct timezone.
pub struct DateTimeOffset {
    datetime2: DateTime2,
    offset: i16,
}

#[cfg(feature = "tds73")]
impl DateTimeOffset {
    /// Construct a new `DateTimeOffset` from a `datetime2`, offset marking
    /// number of minutes from UTC.
    pub fn new(datetime2: DateTime2, offset: i16) -> Self {
        Self { datetime2, offset }
    }

    /// The date and time part.
    pub fn datetime2(self) -> DateTime2 {
        self.datetime2
    }

    /// Number of minutes from UTC.
    pub fn offset(self) -> i16 {
        self.offset
    }

    pub(crate) async fn decode<R>(src: &mut R, n: usize) -> crate::Result<Self>
    where
        R: SqlReadBytes + Unpin,
    {
        let rlen = src.read_u8().await? - 5;
        let datetime2 = DateTime2::decode(src, n, rlen as usize).await?;
        let offset = src.read_i16_le().await?;

        Ok(Self { datetime2, offset })
    }
}

#[cfg(feature = "tds73")]
impl Encode<BytesMut> for DateTimeOffset {
    fn encode(self, dst: &mut BytesMut) -> crate::Result<()> {
        self.datetime2.encode(dst)?;
        dst.put_i16_le(self.offset);

        Ok(())
    }
}

impl Serialize for DateTimeOffset {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // TODO: Fix serialization to include offset
        serializer.serialize_str(&self.datetime2().repr())
    }
}
