/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.FixedLengthCRCFrames

@[expose] public section

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.FixedLengthCRCFrames

namespace CSLibExtTest.Coding.FixedLengthCRCFrames

/-- CRC-3 check register of payload `101` is `0b100`. -/
example : finalRegister 3 crc3Taps [true, false, true] = 0b100#3 :=
  (crc3Frame_example).1

/-- Encoded CRC-3 frame for `101` is accepted and returns `101`. -/
example :
    (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true]) [true, false, true] :=
  (crc3Frame_example).2

/-- Payload `01` round-trips with its leading zero. -/
example :
    (frameParser 2 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [false, true]) [false, true] :=
  encodedFrame_translates_to_payload 2 3 crc3Taps [false, true] rfl

/-- The empty payload round-trips at declared length `0`. -/
example :
    (frameParser 0 3 crc3Taps).Translates (encodeFrame 3 crc3Taps []) [] :=
  encodedFrame_emptyPayload_translates 3 crc3Taps

/-- Two consecutive copies of payload `101` round-trip in order. -/
example :
    (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [true, false, true])
      ([true, false, true] ++ [true, false, true]) :=
  twoConsecutiveFrames_translate 3 3 crc3Taps [true, false, true]
    [true, false, true] rfl rfl

/-- A clean body has zero CRC remainder. -/
example :
    runRegister 3 crc3Taps (encodedBody 3 crc3Taps [true, false, true]) = 0#3 :=
  runRegister_encodedBody_eq_zero 3 crc3Taps [true, false, true]

end CSLibExtTest.Coding.FixedLengthCRCFrames
