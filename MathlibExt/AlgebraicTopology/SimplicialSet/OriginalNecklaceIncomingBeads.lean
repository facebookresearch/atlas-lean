/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadImages
import Mathlib.Data.Finset.Max

/-!
# Actual incoming whole beads of original necklace surjections

Exact original joint images and the SAME full native simplex containment
give an incoming original bead for every positive target bead. Both
original endpoint images are proved from the actual source joints.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

/-- Every full original target bead has an actual incoming positive source bead. -/
theorem exists_incoming_bead {T U : Data} (f : T ⟶ U)
    (hj : ∀ j, j ∈ U.joints ↔ ∃ i ∈ T.joints, f.operator.toOrderHom i = j)
    {a b : Fin (U.dimension + 1)} (h : IsBead U a b) :
    ∃ c d : Fin (T.dimension + 1), IsBead T c d ∧
      f.operator.toOrderHom c = a ∧ f.operator.toOrderHom d = b := by
  classical
  obtain ⟨ca, hca, hfca⟩ := (hj a).mp h.source
  obtain ⟨cb, hcb, hfcb⟩ := (hj b).mp h.target
  let L := T.joints.filter (fun i => f.operator.toOrderHom i ≤ a)
  have hL : L.Nonempty := ⟨ca, Finset.mem_filter.mpr ⟨hca, hfca.le⟩⟩
  let c := L.max' hL
  have hc := Finset.mem_filter.mp (L.max'_mem hL)
  have hfc : f.operator.toOrderHom c = a := by
    have hca' := L.le_max' ca (Finset.mem_filter.mpr ⟨hca, hfca.le⟩)
    exact le_antisymm hc.2 (hfca.symm.le.trans (f.operator.toOrderHom.monotone hca'))
  have hccb : c < cb := by
    by_contra hccb
    have he := f.operator.toOrderHom.monotone (not_lt.mp hccb)
    rw [hfc, hfcb] at he
    exact (not_le_of_gt h.positive) he
  let R := T.joints.filter (fun i => c < i)
  have hR : R.Nonempty := ⟨cb, Finset.mem_filter.mpr ⟨hcb, hccb⟩⟩
  let d := R.min' hR
  have hd := Finset.mem_filter.mp (R.min'_mem hR)
  have hcd : IsBead T c d :=
    ⟨hc.1, hd.1, hd.2, fun j hjT => by
      by_cases hjc : j ≤ c
      · exact Or.inl hjc
      · exact Or.inr (R.min'_le j (Finset.mem_filter.mpr ⟨hjT, not_le.mp hjc⟩))⟩
  have hfcd : f.operator.toOrderHom c < f.operator.toOrderHom d := by
    apply lt_of_le_of_ne (f.operator.toOrderHom.monotone hd.2.le)
    intro he
    have hdL : d ∈ L := Finset.mem_filter.mpr ⟨hd.1, he.symm.le.trans hfc.le⟩
    exact (not_le_of_gt hd.2) (L.le_max' d hdL)
  have hjmap : ∀ i ∈ T.joints, f.operator.toOrderHom i ∈ U.joints :=
    fun i hi => (hj _).mpr ⟨i, hi, rfl⟩
  have himage := bead_image f hcd hjmap hfcd
  rw [hfc] at himage
  have hdb : f.operator.toOrderHom d = b := by
    have hbd := (h.consecutive (f.operator.toOrderHom d) himage.target).resolve_left
      (not_le_of_gt himage.positive)
    have hdb := (himage.consecutive b h.target).resolve_left (not_le_of_gt h.positive)
    exact le_antisymm hdb hbd
  exact ⟨c, d, hcd, hfc, hdb⟩

end SSet.OriginalNecklace
