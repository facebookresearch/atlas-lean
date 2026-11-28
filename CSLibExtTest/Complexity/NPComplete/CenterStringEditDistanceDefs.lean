/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CenterStringEditDistanceDefs

namespace MetaMathlibExt.Complexity.NPComplete.CenterStringEditDistance

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Algorithms.Lean (EditStep editDistance editDistance_eq_zero_iff editDistance_minimal
  editDistance_self)

/-- Binary strings `01` and `11` with bound `1`. -/
private abbrev yes : CenterStringEditDistanceInstance := (2, [[0, 1], [1, 1]], 1)

/-- The same strings with bound `0`: a center would have to equal both. -/
private abbrev no : CenterStringEditDistanceInstance := (2, [[0, 1], [1, 1]], 0)

/-- One substitution turns `01` into `11`. -/
private theorem dist_01_11 : (editDistance [0, 1] [1, 1]).ret.distance ≤ 1 :=
  editDistance_minimal [0, 1] [1, 1] [.substitute 0 1, .keep 1] rfl

/-- The decision problem accepts `yes`, with center `01`. -/
example : centerStringEditDistanceDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : CenterStringEditDistanceFeasible yes := by
    refine ⟨[0, 1], by decide, ?_⟩
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simp [editDistance_self]
    · exact dist_01_11
  simp [centerStringEditDistanceDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ centerStringEditDistanceDec (bitEncode no) = false := by
  have hf : ¬ CenterStringEditDistanceFeasible no := by
    rintro ⟨t, -, h⟩
    have h1 := (editDistance_eq_zero_iff t [0, 1]).1 (Nat.le_zero.1 (h [0, 1] (by simp)))
    have h2 := (editDistance_eq_zero_iff t [1, 1]).1 (Nat.le_zero.1 (h [1, 1] (by simp)))
    exact absurd (h1.symm.trans h2) (by decide)
  exact ⟨by unfold WellFormed; decide,
    by simp [centerStringEditDistanceDec, bitDecode_bitEncode, hf]⟩

/-- An empty list of strings is malformed, although the empty center is vacuously feasible. -/
example :
    CenterStringEditDistanceFeasible ((2, [], 0) : CenterStringEditDistanceInstance) ∧
      centerStringEditDistanceDec
        (bitEncode ((2, [], 0) : CenterStringEditDistanceInstance)) = false := by
  have hw : ¬ WellFormed ((2, [], 0) : CenterStringEditDistanceInstance) := by
    unfold WellFormed; decide
  exact ⟨⟨[], by simp, by simp⟩, by simp [centerStringEditDistanceDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : centerStringEditDistanceDec [true] = false := by
  have h : bitDecode (α := CenterStringEditDistanceInstance) [true] = none := rfl
  simp [centerStringEditDistanceDec, h]

end MetaMathlibExt.Complexity.NPComplete.CenterStringEditDistance
