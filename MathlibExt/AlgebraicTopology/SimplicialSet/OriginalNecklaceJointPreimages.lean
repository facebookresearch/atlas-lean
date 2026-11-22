/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadCoverage

/-!
# Every target joint has an original source joint preimage

A complete endpoint-preserving native necklace map cannot jump across a
target joint within any whole original source bead. The ordered finite
joint sets therefore supply a source joint over every target joint,
without surjectivity or an exact joint-image equation as a hypothesis.
-/

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- EVERY original target joint is hit by an original source joint of the SAME whole native map. -/
theorem target_joint_preimage {T U : Data} (f : T ⟶ U) (j : Fin (U.dimension + 1)) (hj : j ∈ U.joints) :
    ∃ i ∈ T.joints, f.operator.toOrderHom i = j := by
  classical
  let R := T.joints.filter (fun i => j ≤ f.operator.toOrderHom i)
  have hR : R.Nonempty := ⟨Fin.last T.dimension,
    Finset.mem_filter.mpr ⟨T.target_joint, f.target.symm ▸ Fin.le_last j⟩⟩
  let b := R.min' hR
  have hb := Finset.mem_filter.mp (R.min'_mem hR)
  by_cases hfb : f.operator.toOrderHom b = j
  · exact ⟨b, hb.1, hfb⟩
  have hjb : j < f.operator.toOrderHom b := lt_of_le_of_ne hb.2 (Ne.symm hfb)
  have hb0 : b ≠ 0 := by
    intro h
    have he : f.operator.toOrderHom b = 0 := h ▸ f.source
    exact (not_lt_of_ge (Fin.zero_le j)) (hjb.trans_eq he)
  let L := T.joints.filter (fun i => i < b)
  have hL : L.Nonempty := ⟨0,
    Finset.mem_filter.mpr ⟨T.source_joint, lt_of_le_of_ne (Fin.zero_le b) (Ne.symm hb0)⟩⟩
  let a := L.max' hL
  have ha := Finset.mem_filter.mp (L.max'_mem hL)
  have hfa : f.operator.toOrderHom a < j := by
    by_contra h
    have haR : a ∈ R := Finset.mem_filter.mpr ⟨ha.1, not_lt.mp h⟩
    exact (not_le_of_gt ha.2) (R.min'_le a haR)
  have hab : IsBead T a b := ⟨ha.1, hb.1, ha.2, fun k hk => by
    by_cases hkb : k < b
    · exact Or.inl (L.le_max' k (Finset.mem_filter.mpr ⟨hk, hkb⟩))
    · exact Or.inr (not_lt.mp hkb)⟩
  let s : (Δ[length a b] : SSet.{0}) _⦋length a b⦌ := SSet.yonedaEquiv (𝟙 _)
  have hs := f.lands (op ⦋length a b⦌) (bead_interval_mem hab s)
  rcases (mem_complex_iff U.joints _).mp hs j hj with h | h
  · have ht := h (Fin.last (length a b))
    change f.operator.toOrderHom (embedding a b hab.positive.le (Fin.last (length a b))) ≤ j at ht
    rw [embedding_last] at ht
    exact False.elim ((not_le_of_gt hjb) ht)
  · have ht := h 0
    change j ≤ f.operator.toOrderHom (embedding a b hab.positive.le 0) at ht
    rw [embedding_zero] at ht
    exact False.elim ((not_le_of_gt hfa) ht)

end SSet.OriginalNecklace
