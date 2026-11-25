/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.FrameLengthDiscipline
public import CSLibExtTest.Coding.UnreflectedSerialCRC

/-!
# Tests for the frame length and termination discipline

Exhaustive kernel checks at `l = 1`, `r = 2`, taps `11` (generator `X ^ 2 + X + 1`), so a
frame body has three bits:

* exactly two of the 1365 token lists of length at most 5 are accepted, the two clean frames,
  so the rejections below are not the trivial "reject everything";
* every token list of length at most 5 without `start` is rejected;
* after a prefix of at most 5 tokens that leaves the parser outside a body, every nonempty
  continuation of at most 3 tokens without `start` is rejected;
* after any prefix of at most 2 tokens, every body of at most 6 bits closed by `endTok` with
  length other than 3 is rejected, and every unclosed body of at most 5 bits is rejected;
* a `start` after any prefix of at most 1 token and an unfinished body of at most 2 bits
  makes acceptance and output follow the continuation of at most 3 tokens;
* from the fresh state, bodies of at most 6 bits give the serial register and the saturating
  count.

The general theorems are then instantiated at the same parameters. The file ends with CRC-3
validation statements at `l = 3`, `r = 3`, taps `011` (generator `X ^ 3 + X + 1`).
-/

@[expose] public section

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.FixedLengthCRCFrames
open CSLibExt.Coding.FrameLengthDiscipline
open CSLibExtTest.Coding.UnreflectedSerialCRC

namespace CSLibExtTest.Coding.FrameLengthDiscipline

/-- Boolean acceptance of a token list at `l = 1`, `r = 2`, taps `11`. -/
def accepts (ts : List FrameToken) : Bool :=
  decide (((frameParser 1 2 0b11#2).runState (frameParser 1 2 0b11#2).start ts).phase =
    ParserPhase.done)

/-- The run on `ts` ends outside a body. -/
def outsideBody (ts : List FrameToken) : Bool :=
  decide (((frameParser 1 2 0b11#2).runState (frameParser 1 2 0b11#2).start ts).phase ≠
    ParserPhase.inBody)

/-- All token lists of length exactly `n`. -/
def tokLists : ℕ → List (List FrameToken)
  | 0 => [[]]
  | n + 1 => (tokLists n).flatMap fun xs =>
      [FrameToken.start :: xs, .bit false :: xs, .bit true :: xs, .endTok :: xs]

/-- All token lists of length at most `n`. -/
def tokListsLE (n : ℕ) : List (List FrameToken) :=
  (List.range (n + 1)).flatMap tokLists

/-- All bit lists of length exactly `n`. -/
def bitLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun xs => [false :: xs, true :: xs]

/-- All bit lists of length at most `n`. -/
def bitListsLE (n : ℕ) : List (List Bool) :=
  (List.range (n + 1)).flatMap bitLists

/-- Exactly the two clean frames are accepted among the token lists of length at most 5. -/
example : ((tokListsLE 5).filter accepts).length = 2 := by
  decide +kernel

/-- The clean frame of payload `1` is accepted. -/
example : accepts (encodeFrame 2 0b11#2 [true]) = true := by
  decide +kernel

/-- Missing `start`: every token list of length at most 5 without `start` is rejected. -/
example :
    (tokListsLE 5).all (fun ts => decide (FrameToken.start ∈ ts) || !accepts ts) = true := by
  decide +kernel

/-- Missing `start` mid-stream: a prefix outside a body followed by a nonempty
continuation without `start` is rejected. -/
example :
    (tokListsLE 5).all (fun pfx => (tokListsLE 3).all fun ts =>
      !outsideBody pfx || ts.isEmpty || decide (FrameToken.start ∈ ts) ||
        !accepts (pfx ++ ts)) = true := by
  decide +kernel

/-- The mid-stream hypothesis holds after a clean frame. -/
example : outsideBody (encodeFrame 2 0b11#2 [true]) = true := by
  decide +kernel

/-- Early and late `endTok`: every body of the wrong length is rejected, past the
saturation point of the count included. -/
example :
    (tokListsLE 2).all (fun pfx => (bitListsLE 6).all fun body =>
      decide (body.length = 3) ||
        !accepts (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++
          [FrameToken.endTok]))) = true := by
  decide +kernel

/-- End of input inside a frame: every unclosed body is rejected. -/
example :
    (tokListsLE 2).all (fun pfx => (bitListsLE 5).all fun body =>
      !accepts (pfx ++ (FrameToken.start :: body.map FrameToken.bit))) = true := by
  decide +kernel

/-- Restart: acceptance and output follow the continuation after the second `start`. -/
example :
    (tokListsLE 1).all (fun pfx => (bitListsLE 2).all fun pb => (tokListsLE 3).all fun rest =>
      let P := frameParser 1 2 0b11#2
      let whole := pfx ++ (FrameToken.start :: pb.map FrameToken.bit) ++
        (FrameToken.start :: rest)
      (accepts whole == accepts (FrameToken.start :: rest)) &&
        (P.runOut P.start whole ==
          P.runOut P.start pfx ++ pb.take 1 ++ P.runOut P.start (FrameToken.start :: rest)))
      = true := by
  decide +kernel

/-- Length counter: from the fresh state, a body leaves the parser inside the body with the
serial register and the saturating count. -/
example :
    (bitListsLE 6).all (fun body =>
      let q := (frameParser 1 2 0b11#2).runState (freshState 1 2) (body.map FrameToken.bit)
      decide (q.phase = ParserPhase.inBody) && decide (q.register = runRegister 2 0b11#2 body) &&
        decide (q.count = satCount 1 2 body.length)) = true := by
  decide +kernel

/-- `start` from an accepted state moves to the fresh state. -/
example :
    (frameParser 1 2 0b11#2).step
        ((frameParser 1 2 0b11#2).runState (frameParser 1 2 0b11#2).start
          (encodeFrame 2 0b11#2 [true]))
        FrameToken.start =
      (freshState 1 2, []) :=
  step_start 1 2 0b11#2 _

/-- A two-bit body closed by `endTok` is rejected after any prefix. -/
example (pfx : List FrameToken) (out : List Bool) :
    ¬ (frameParser 1 2 0b11#2).Translates
      (pfx ++ (FrameToken.start :: [true, true].map FrameToken.bit ++ [FrameToken.endTok]))
      out :=
  rejects_early_end 1 2 0b11#2 pfx [true, true] (by decide) out

/-- A four-bit body closed by `endTok` is rejected after any prefix. -/
example (pfx : List FrameToken) (out : List Bool) :
    ¬ (frameParser 1 2 0b11#2).Translates
      (pfx ++ (FrameToken.start :: [true, true, true, false].map FrameToken.bit ++
        [FrameToken.endTok])) out :=
  rejects_extra_bit 1 2 0b11#2 pfx [true, true, true, false] (by decide) out

/-- The clean body of payload `1`, left unclosed, is rejected. -/
example (out : List Bool) :
    ¬ (frameParser 1 2 0b11#2).Translates
      ([] ++ (FrameToken.start :: [true, true, true].map FrameToken.bit)) out :=
  rejects_end_of_input_in_frame 1 2 0b11#2 [] [true, true, true] out

/-- Bits and `endTok` with no `start` are rejected. -/
example (out : List Bool) :
    ¬ (frameParser 1 2 0b11#2).Translates
      [FrameToken.bit true, FrameToken.bit true, FrameToken.bit true, FrameToken.endTok] out :=
  rejects_of_start_not_mem 1 2 0b11#2 _ (by decide) out

/-- After a clean frame, a stray `endTok` is rejected. -/
example (out : List Bool) :
    ¬ (frameParser 1 2 0b11#2).Translates
      (encodeFrame 2 0b11#2 [true] ++ [FrameToken.endTok]) out :=
  rejects_missing_start_after 1 2 0b11#2 _ _ (by decide +kernel) (by simp) (by decide) out

/-- An unfinished frame `start 1` followed by the clean frame of payload `0` is accepted
with output `1 0`: the restarted frame is accepted, and the bit emitted before the restart
stays in the output. -/
example :
    (frameParser 1 2 0b11#2).Translates
      ([] ++ (FrameToken.start :: [true].map FrameToken.bit) ++
        (FrameToken.start :: ([false, false, false].map FrameToken.bit ++ [FrameToken.endTok])))
      [true, false] := by
  rw [translates_restart_iff]
  refine ⟨[false], ⟨?_, by decide +kernel⟩, by decide +kernel⟩
  change ((frameParser 1 2 0b11#2).runState (frameParser 1 2 0b11#2).start
    (FrameToken.start :: ([false, false, false].map FrameToken.bit ++
      [FrameToken.endTok]))).phase = ParserPhase.done
  decide +kernel

/-! ### Validation statements (CRC-3, `l = 3`, `r = 3`; the clean body of payload `101`
is `101100`) -/

/-- Truncated header: the empty input and a lone `start` are rejected. -/
theorem crc3_truncated_header_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates [] out ∧
      ¬ (frameParser 3 3 crc3Taps).Translates [FrameToken.start] out := by
  constructor
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        []).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        [FrameToken.start]).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)

/-- Truncated body: the payload bits alone, closed by `endTok`, are rejected. -/
theorem crc3_truncated_body_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false, true].map FrameToken.bit ++ [FrameToken.endTok])
      out := by
  intro h
  have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false, true].map FrameToken.bit ++
        [FrameToken.endTok])).phase = ParserPhase.done := h.1
  exact absurd happ (by decide)

/-- Truncated tail: the clean frame without its last check bit, closed by `endTok`, and
the clean frame without its `endTok` (missing `endTok`) are both rejected. -/
theorem crc3_truncated_tail_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
        (FrameToken.start :: [true, false, true, true, false].map FrameToken.bit ++
          [FrameToken.endTok]) out ∧
      ¬ (frameParser 3 3 crc3Taps).Translates
        ((encodeFrame 3 crc3Taps [true, false, true]).dropLast) out := by
  constructor
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start :: [true, false, true, true, false].map FrameToken.bit ++
          [FrameToken.endTok])).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        ((encodeFrame 3 crc3Taps [true, false, true]).dropLast)).phase =
        ParserPhase.done := h.1
    exact absurd happ (by decide)

/-- One extra bit: the clean body followed by one more bit is rejected, whatever the bit. -/
theorem crc3_one_extra_bit_rejected (b : Bool) (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start ::
        (encodedBody 3 crc3Taps [true, false, true] ++ [b]).map FrameToken.bit ++
          [FrameToken.endTok]) out := by
  cases b
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start ::
          (encodedBody 3 crc3Taps [true, false, true] ++ [false]).map FrameToken.bit ++
            [FrameToken.endTok])).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start ::
          (encodedBody 3 crc3Taps [true, false, true] ++ [true]).map FrameToken.bit ++
            [FrameToken.endTok])).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)

/-- A bit outside any frame: a stray bit after an accepted frame is rejected. -/
theorem crc3_stray_bit_after_frame_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true] ++ [FrameToken.bit true]) out := by
  intro h
  have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (encodeFrame 3 crc3Taps [true, false, true] ++ [FrameToken.bit true])).phase =
      ParserPhase.done := h.1
  exact absurd happ (by decide)

/-- Resynchronizing `start`: a frame cut off after two body bits, followed by the clean
frame of `011`, is accepted; the output is the two emitted bits followed by `011`. -/
theorem crc3_resync_start_accepted :
    (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, true, true])
      [true, false, false, true, true] := by
  have hacc : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, true, true])).phase =
      ParserPhase.done := by decide
  have hout : (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, true, true]) =
      [true, false, false, true, true] := by decide
  refine ⟨hacc, ?_⟩
  have hinit : (frameParser 3 3 crc3Taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser 3 3 crc3Taps).finalOut q = [] := fun q => rfl
  rw [hinit, hfinal, List.nil_append, List.append_nil, hout]

/-- Missing `endTok` followed by a new frame: the complete but unclosed clean body of
`101` is discarded by the next `start`, and the following clean frame of `000` is
accepted. -/
theorem crc3_missing_end_then_frame_accepted :
    (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: (encodedBody 3 crc3Taps [true, false, true]).map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, false, false])
      [true, false, true, false, false, false] := by
  have hacc : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start ::
        (encodedBody 3 crc3Taps [true, false, true]).map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, false, false])).phase =
      ParserPhase.done := by decide
  have hout : (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
      (FrameToken.start ::
        (encodedBody 3 crc3Taps [true, false, true]).map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, false, false]) =
      [true, false, true, false, false, false] := by decide
  refine ⟨hacc, ?_⟩
  have hinit : (frameParser 3 3 crc3Taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser 3 3 crc3Taps).finalOut q = [] := fun q => rfl
  rw [hinit, hfinal, List.nil_append, List.append_nil, hout]

/-- Two valid frames, the second with leading zeros, are accepted in order. -/
theorem crc3_two_frames_accepted :
    (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [false, false, true])
      [true, false, true, false, false, true] := by
  have hacc : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [false, false, true])).phase =
      ParserPhase.done := by decide
  have hout : (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [false, false, true]) =
      [true, false, true, false, false, true] := by decide
  refine ⟨hacc, ?_⟩
  have hinit : (frameParser 3 3 crc3Taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser 3 3 crc3Taps).finalOut q = [] := fun q => rfl
  rw [hinit, hfinal, List.nil_append, List.append_nil, hout]

end CSLibExtTest.Coding.FrameLengthDiscipline
