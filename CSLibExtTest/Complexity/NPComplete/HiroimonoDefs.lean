/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HiroimonoDefs
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.Hiroimono

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt)

private theorem dec_bitEncode (i : HiroimonoInstance) :
    hiroimonoDec (bitEncode i) = true ↔ WellFormed i ∧ HiroimonoFeasible i := by
  simp [hiroimonoDec, bitDecode_bitEncode]

/-- Stones at `(0, 0)`, `(1, 0)`, `(1, 1)`: pick them up in that order, moving right and then
up (a 90° turn). -/
example :
    hiroimonoDec
      (bitEncode ([((0, 0), (0, 0)), ((1, 0), (0, 0)), ((1, 0), (1, 0))] : HiroimonoInstance)) =
        true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed stones point toInt; decide, [(0, 0), (1, 0), (1, 1)],
    by unfold stones point toInt; decide, ?_⟩
  intro k hk
  have hk2 : k < 2 := by simp at hk; omega
  unfold StrictlyBetween direction stones point toInt
  match k, hk2 with
  | 0, _ => decide +revert
  | 1, _ => decide +revert

/-- Stones at `(0, 0)` and `(1, 1)` share no grid line, so neither order makes a legal move. -/
example :
    hiroimonoDec
      (bitEncode ([((0, 0), (0, 0)), ((1, 0), (1, 0))] : HiroimonoInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, order, hperm, h⟩
  have hmem := List.mem_permutations'.2 hperm
  have hp : (stones [((0, 0), (0, 0)), ((1, 0), (1, 0))]).permutations' =
      [[(0, 0), (1, 1)], [(1, 1), (0, 0)]] := by
    unfold stones point toInt; decide
  rw [hp] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> exact absurd (h 0 (by simp)).1 (by decide)

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := HiroimonoInstance) bits = none) :
    hiroimonoDec bits = false := by
  simp [hiroimonoDec, h]

/-- A lone continuation bit is a truncated stone encoding. -/
example : hiroimonoDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.Hiroimono
