/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.FixedLengthCRCFrames
public import CSLibExtTest.Coding.UnreflectedSerialCRC

@[expose] public section

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.FixedLengthCRCFrames
open CSLibExtTest.Coding.UnreflectedSerialCRC

namespace CSLibExtTest.Coding.FixedLengthCRCFrames

/-- CRC-3 fixture: payload `101` at declared length `3` has check
register `0b100`, and its encoded frame is accepted and returns the
payload. -/
theorem crc3Frame_example :
    finalRegister 3 crc3Taps [true, false, true] = 0b100#3 ∧
      (frameParser 3 3 crc3Taps).Translates
        (encodeFrame 3 crc3Taps [true, false, true])
        [true, false, true] := by
  constructor
  · decide
  · exact encodedFrame_translates_to_payload 3 3 crc3Taps [true, false, true] rfl

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

/-- The parser state space is finite. -/
example : Finite (ParserState 3 3) := inferInstance

/-- Wrong length, short: a five-bit body at `l + r = 6` ends failed. -/
example :
    ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false, true, true, false].map FrameToken.bit ++
        [FrameToken.endTok])).phase = ParserPhase.failed := by
  decide

/-- Wrong length, long: a nine-bit body, past the saturation point of the
count, ends failed. -/
example :
    ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start ::
        [true, false, true, true, false, false, false, false, false].map
          FrameToken.bit ++ [FrameToken.endTok])).phase = ParserPhase.failed := by
  decide

/-- A five-bit body at `l + r = 6` is rejected for every output. -/
example (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false, true, true, false].map FrameToken.bit ++
        [FrameToken.endTok]) out :=
  wrongLengthBody_rejected 3 3 crc3Taps [] [true, false, true, true, false] (by decide) out

/-- Nonzero remainder: payload `101` with check bits `000` has remainder
`0b100`, ends failed, and still emits its first three bits. -/
example :
    runRegister 3 crc3Taps [true, false, true, false, false, false] = 0b100#3 ∧
      ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start :: [true, false, true, false, false, false].map
          FrameToken.bit ++ [FrameToken.endTok])).phase = ParserPhase.failed ∧
      (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
        (FrameToken.start :: [true, false, true, false, false, false].map
          FrameToken.bit ++ [FrameToken.endTok]) = [true, false, true] := by
  decide

/-- Payload `101` with check bits `000` is rejected for every output. -/
example (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false, true, false, false, false].map
        FrameToken.bit ++ [FrameToken.endTok]) out :=
  nonzeroRemainderBody_rejected 3 3 crc3Taps [true, false, true, false, false, false]
    (by decide) out

/-- The nonzero-remainder rejection needs no length hypothesis: a four-bit body with nonzero
remainder is rejected too. -/
example (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false, false, false].map FrameToken.bit ++
        [FrameToken.endTok]) out :=
  nonzeroRemainderBody_rejected 3 3 crc3Taps [true, false, false, false] (by decide) out

/-- A completed but rejected frame, the body `101000` above, followed by the clean frame of
`011`: the stream is accepted, because acceptance depends on the final frame alone, and the
output keeps the three bits the rejected frame emitted before the clean payload. This
instantiates `translates_iff_zero_remainder_body` with the rejected frame as the prefix. -/
example :
    (frameParser 3 3 crc3Taps).Translates
      ((FrameToken.start :: [true, false, true, false, false, false].map FrameToken.bit ++
          [FrameToken.endTok]) ++ encodeFrame 3 crc3Taps [false, true, true])
      [true, false, true, false, true, true] :=
  (translates_iff_zero_remainder_body 3 3 crc3Taps _ _).mpr
    ⟨FrameToken.start :: [true, false, true, false, false, false].map FrameToken.bit ++
        [FrameToken.endTok],
      encodedBody 3 crc3Taps [false, true, true], by decide,
      runRegister_encodedBody_eq_zero 3 crc3Taps [false, true, true], rfl, by decide⟩

/-- The same stream, run directly: the parser ends accepted, and its output is the rejected
frame's three emitted bits followed by the clean payload `011`. -/
example :
    ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      ((FrameToken.start :: [true, false, true, false, false, false].map FrameToken.bit ++
          [FrameToken.endTok]) ++ encodeFrame 3 crc3Taps [false, true, true])).phase =
        ParserPhase.done ∧
      (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
        ((FrameToken.start :: [true, false, true, false, false, false].map FrameToken.bit ++
            [FrameToken.endTok]) ++ encodeFrame 3 crc3Taps [false, true, true]) =
        [true, false, true, false, true, true] := by
  decide

/-- A wrong-length final frame after a clean frame is rejected: the earlier accepted frame does
not save the stream. -/
example (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true] ++
        (FrameToken.start :: [true, false].map FrameToken.bit ++ [FrameToken.endTok])) out :=
  wrongLengthBody_rejected 3 3 crc3Taps _ [true, false] (by decide) out

/-- A `start` after two body bits restarts: the clean frame for `101` is
accepted, and the output is the two emitted bits followed by `101`. -/
example :
    ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [false, true].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [true, false, true])).phase = ParserPhase.done ∧
      (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
        (FrameToken.start :: [false, true].map FrameToken.bit ++
          encodeFrame 3 crc3Taps [true, false, true]) =
        [false, true, true, false, true] := by
  decide

/-- A partial body longer than `l` emits only its first `l` bits before
the restart. -/
example :
    (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [false, true, true, true].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [true, false, true])
      [false, true, true, true, false, true] :=
  startInBody_aborts_and_restarts 3 3 crc3Taps [false, true, true, true]
    [true, false, true] rfl

/-- A bit before any `start` fails the parser, and the next `start`
restarts it: the following clean frame is accepted and returns `101`. -/
example :
    ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.bit true :: encodeFrame 3 crc3Taps [true, false, true])).phase =
        ParserPhase.done ∧
      (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
        (FrameToken.bit true :: encodeFrame 3 crc3Taps [true, false, true]) =
        [true, false, true] := by
  decide

end CSLibExtTest.Coding.FixedLengthCRCFrames
