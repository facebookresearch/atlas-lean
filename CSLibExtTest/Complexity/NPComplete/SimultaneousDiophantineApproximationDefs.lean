/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SimultaneousDiophantineApproximationDefs

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousDiophantineApproximation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SimultaneousDiophantineApproximationInstance) :
    simultaneousDiophantineApproximationDec (bitEncode i) = true ↔
      WellFormed i ∧ SimultaneousDiophantineApproximationFeasible i := by
  simp [simultaneousDiophantineApproximationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : simultaneousDiophantineApproximationDec [true] = false := by
  have h : bitDecode (α := SimultaneousDiophantineApproximationInstance) [true] = none := rfl
  simp [simultaneousDiophantineApproximationDec, h]

/-- For `α = 1/2`, `Q = 2` makes `Q α = 1` an integer, within `ε = 1/4`. -/
example : simultaneousDiophantineApproximationDec
    (bitEncode (([((1, 0), 2)], 2, (1, 4)) : SimultaneousDiophantineApproximationInstance)) =
      true := by
  refine (accepts_encoding _).2 ⟨⟨by simp, by simp, by decide, by decide⟩, 2, le_refl _ |>.trans
    (by decide), le_rfl, ?_⟩
  simp only [List.mem_singleton, forall_eq, RatCode.val]
  norm_num

/-- With `N = 1` only `Q = 1` is allowed, and `1/2` is at distance `1/2 > 1/4` from the nearest
integers. -/
example : simultaneousDiophantineApproximationDec
    (bitEncode (([((1, 0), 2)], 1, (1, 4)) : SimultaneousDiophantineApproximationInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, Q, hQ1, hQN, hQ⟩ := (accepts_encoding _).1 h
  obtain rfl : Q = 1 := le_antisymm hQN hQ1
  have h1 := hQ _ (List.mem_singleton_self _)
  simp only [RatCode.val, round_eq] at h1
  norm_num at h1

/-- A rational with denominator `0` is malformed. -/
example : simultaneousDiophantineApproximationDec
    (bitEncode (([((1, 0), 0)], 1, (1, 4)) : SimultaneousDiophantineApproximationInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.1 _ (List.mem_singleton_self _)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.SimultaneousDiophantineApproximation
