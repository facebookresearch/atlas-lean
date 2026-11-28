/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HittingSetSizeTwoDefs

namespace MetaMathlibExt.Complexity.NPComplete.HittingSetSizeTwo

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.HittingSet (HittingSetInstance HittingSetFeasible)

private theorem accepts_encoding (i : HittingSetInstance) :
    hittingSetSizeTwoDec (bitEncode i) = true ↔ WellFormed i ∧ HittingSetFeasible i := by
  simp [hittingSetSizeTwoDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := HittingSetInstance) bits = none) :
    hittingSetSizeTwoDec bits = false := by
  simp [hittingSetSizeTwoDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hittingSetSizeTwoDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The pairs `{0, 1}` and `{1, 2}` of a three-element set are both hit by `{1}`. -/
example :
    hittingSetSizeTwoDec (bitEncode ((3, [[0, 1], [1, 2]], 1) : HittingSetInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed HittingSet.WellFormed; decide, {1}, by decide, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨1, by simp, by simp⟩

/-- The disjoint singletons `{0}` and `{1}` cannot both be hit by one element. -/
example :
    hittingSetSizeTwoDec (bitEncode ((2, [[0], [1]], 1) : HittingSetInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, S', hcard, hhit⟩
  change S'.card ≤ 1 at hcard
  obtain ⟨x, hx, hx0⟩ := hhit [0] (by simp)
  obtain ⟨y, hy, hy1⟩ := hhit [1] (by simp)
  have hx' : x = 0 := Fin.ext (by simpa using hx0)
  have hy' : y = 1 := Fin.ext (by simpa using hy1)
  subst hx' hy'
  have : ({0, 1} : Finset (Fin 2)) ⊆ S' := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have := Finset.card_le_card this
  simp at this
  omega

/-- A three-element subset is rejected by the size restriction even though `{0}` hits it. -/
example :
    hittingSetSizeTwoDec (bitEncode ((3, [[0, 1, 2]], 1) : HittingSetInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, h⟩, -⟩
  exact absurd (h [0, 1, 2] (by simp)) (by decide)

/-- The same three-element subset is accepted by unrestricted HITTING SET. -/
example :
    HittingSet.hittingSetDec (bitEncode ((3, [[0, 1, 2]], 1) : HittingSetInstance)) = true := by
  simp only [HittingSet.hittingSetDec, bitDecode_bitEncode, decide_eq_true_eq]
  refine ⟨by unfold HittingSet.WellFormed; decide, {0}, by decide, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  exact ⟨0, by simp, by simp⟩

end MetaMathlibExt.Complexity.NPComplete.HittingSetSizeTwo
