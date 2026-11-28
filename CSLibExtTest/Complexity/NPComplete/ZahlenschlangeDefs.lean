/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ZahlenschlangeDefs

namespace MetaMathlibExt.Complexity.NPComplete.Zahlenschlange

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ZahlenschlangeInstance) :
    zahlenschlangeDec (bitEncode i) = true ↔ WellFormed i ∧ ZahlenschlangeFeasible i := by
  simp [zahlenschlangeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : zahlenschlangeDec [true] = false := by
  have h : bitDecode (α := ZahlenschlangeInstance) [true] = none := rfl
  simp [zahlenschlangeDec, h]

private theorem adj₁ : (gridGraph ((2, [[1, 2], [2, 3]]) : ZahlenschlangeInstance)).Adj
    (⟨0, by decide⟩, ⟨0, by decide⟩) (⟨0, by decide⟩, ⟨1, by decide⟩) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]

private theorem adj₂ : (gridGraph ((2, [[1, 2], [2, 3]]) : ZahlenschlangeInstance)).Adj
    (⟨0, by decide⟩, ⟨1, by decide⟩) (⟨1, by decide⟩, ⟨1, by decide⟩) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]

/-- In the grid `1 2 / 2 3` the path right then down reads `1, 2, 3`: every number of the grid
once, although `2` occurs twice in the grid. -/
example : zahlenschlangeDec (bitEncode ((2, [[1, 2], [2, 3]]) : ZahlenschlangeInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, _, _, rfl, rfl, rfl, rfl, .cons adj₁ (.cons adj₂ .nil), ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    decide
  · unfold number
    decide

/-- In the grid `1 2 / 3 1` both ends of every path hold `1`, so `1` is read twice. -/
example : zahlenschlangeDec (bitEncode ((2, [[1, 2], [3, 1]]) : ZahlenschlangeInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩, ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩, rfl, rfl, ht₁', ht₂', p, -, hcount⟩
  simp only at ht₁' ht₂'
  have hne : ((⟨0, hs₁⟩, ⟨0, hs₂⟩) : Cell ((2, [[1, 2], [3, 1]]) : ZahlenschlangeInstance)) ≠
      (⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩) := by
    simp only [ne_eq, Prod.mk.injEq, Fin.mk.injEq, not_and]
    simp at ht₁'
    omega
  have h := hcount (⟨0, hs₁⟩, ⟨0, hs₂⟩)
  rw [← p.cons_tail_support, List.countP_cons_of_pos (by simp)] at h
  obtain ⟨rfl, rfl⟩ : t₁ = 1 ∧ t₂ = 1 := by simp at ht₁'; omega
  have htail : 0 < p.support.tail.countP fun v =>
      decide (number _ v = number ((2, [[1, 2], [3, 1]]) : ZahlenschlangeInstance)
        (⟨0, hs₁⟩, ⟨0, hs₂⟩)) :=
    List.countP_pos_iff.2 ⟨_, p.end_mem_tail_support_of_ne hne, by simp [number]⟩
  omega

/-- The rejected instance is well formed, so the rejection comes from the repeated number. -/
example : WellFormed ((2, [[1, 2], [3, 1]]) : ZahlenschlangeInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.Zahlenschlange
