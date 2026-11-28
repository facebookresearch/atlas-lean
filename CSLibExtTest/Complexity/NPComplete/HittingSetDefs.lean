/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HittingSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.HittingSet

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HittingSetInstance) :
    hittingSetDec (bitEncode i) = true ↔ WellFormed i ∧ HittingSetFeasible i := by
  simp [hittingSetDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := HittingSetInstance) bits = none) :
    hittingSetDec bits = false := by
  simp [hittingSetDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hittingSetDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The subsets `{0, 1}` and `{1, 2}` of a three-element set are both hit by `{1}`. -/
example :
    hittingSetDec (bitEncode ((3, [[0, 1], [1, 2]], 1) : HittingSetInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {1}, by decide, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨1, by simp, by simp⟩

/-- The disjoint subsets `{0}` and `{1}` cannot both be hit by one element. -/
example :
    hittingSetDec (bitEncode ((2, [[0], [1]], 1) : HittingSetInstance)) = false := by
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

/-- A zero bound is malformed even though the empty collection needs no hitting element. -/
example :
    hittingSetDec (bitEncode ((2, [], 0) : HittingSetInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, h, -⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.HittingSet
