/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.Hamming74

@[expose] public section

/-! # Tests for the Hamming (7,4) code -/

namespace Cslib.CodingTheory.Hamming74Tests

open Cslib.CodingTheory Hamming74

/-- The message `1011` encodes to `0110011`: parity bits `p₁ = 0`, `p₂ = 1`, `p₄ = 0` at
positions 1, 2, 4. -/
example : encode ![1, 0, 1, 1] = ![0, 1, 1, 0, 0, 1, 1] := by decide

/-- Flipping position 5 gives syndrome `101` (least significant bit first), which names
position 5. -/
example : LinearCode.syndrome H ![0, 1, 1, 0, 1, 1, 1] = ![1, 0, 1] := by decide

example : errorPos ![1, 0, 1] = some 4 := by decide

/-- The decoder repairs the flipped bit and the message is recovered. -/
example : decode ![0, 1, 1, 0, 1, 1, 1] = ![0, 1, 1, 0, 0, 1, 1] := by decide

example : message (decode ![0, 1, 1, 0, 1, 1, 1]) = ![1, 0, 1, 1] := by decide

/-- Every single-bit error in every codeword, via the theorem. -/
example (m : Fin 4 → ZMod 2) (i : Fin 7) :
    message (decode (encode m + Pi.single i 1)) = m :=
  message_decode_encode_add_single m i

/-- Two errors exceed the radius: flipping positions 1 and 2 of `0110011` gives syndrome `110`
(least significant bit first, the binary expansion of 3),
so the decoder flips position 3 and lands on a different codeword. -/
example : decode (encode ![1, 0, 1, 1] + ![1, 1, 0, 0, 0, 0, 0]) ≠ encode ![1, 0, 1, 1] := by
  decide

example : LinearCode.syndrome H ![1, 1, 0, 0, 0, 0, 0] = ![1, 1, 0] := by decide

example : errorPos ![1, 1, 0] = some 2 := by decide

example : decode (encode ![1, 0, 1, 1] + ![1, 1, 0, 0, 0, 0, 0]) ∈ code :=
  decode_mem_code _

/-- The code has 16 codewords and minimum distance 3. -/
example : Module.finrank (ZMod 2) code = 4 := finrank_code

example : code.minDist = 3 := minDist_code

/-- `1111111` is the codeword encoding `1111`, so the decoder leaves it alone, and the zero
syndrome names no position. -/
example : encode ![1, 1, 1, 1] = ![1, 1, 1, 1, 1, 1, 1] := by decide

example : decode ![1, 1, 1, 1, 1, 1, 1] = ![1, 1, 1, 1, 1, 1, 1] := by decide

example : errorPos ![0, 0, 0] = none := by decide

/-- Perfection: every word has exactly one codeword within distance 1, and the decoder finds a
nearest codeword. -/
example (y : Fin 7 → ZMod 2) : ∃! c, c ∈ code ∧ hammingDist y c ≤ 1 :=
  existsUnique_hammingDist_le_one y

example (y c : Fin 7 → ZMod 2) (hc : c ∈ code) : hammingDist y (decode y) ≤ hammingDist y c :=
  hammingDist_decode_le y hc

end Cslib.CodingTheory.Hamming74Tests
