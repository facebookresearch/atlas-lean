/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulWalkVerticalBound



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section




theorem exists_fkRectFaithfulWalk_verticalExtremaSubwalk
    {x y : Site 2} (V : (hypercubicLattice 2).Walk x y) :
    ∃ (lower upper : Int) (bottom top : Site 2),
      ∃ W : (hypercubicLattice 2).Walk bottom top,
        bottom 1 = lower ∧ top 1 = upper ∧
        (∀ z ∈ V.support, lower ≤ z 1 ∧ z 1 ≤ upper) ∧
        (∀ z ∈ W.support, z ∈ V.support) := by
  let S : Finset (Site 2) := V.support.toFinset
  have hS : S.Nonempty := ⟨x, by simp [S]⟩
  let rows : Finset Int := S.image (fun z => z 1)
  have hrows : rows.Nonempty := hS.image (fun z => z 1)
  let lower : Int := rows.min' hrows
  let upper : Int := rows.max' hrows
  have hlowerMem : lower ∈ rows := by
    exact rows.min'_mem hrows
  have hupperMem : upper ∈ rows := by
    exact rows.max'_mem hrows
  obtain ⟨bottom, hbottomS, hbottomRow⟩ := Finset.mem_image.mp hlowerMem
  obtain ⟨top, htopS, htopRow⟩ := Finset.mem_image.mp hupperMem
  have hbottomSupport : bottom ∈ V.support := by
    simpa [S] using hbottomS
  have htopSupport : top ∈ V.support := by
    simpa [S] using htopS
  let bottom' : {z : Site 2 // z ∈ V.support} :=
    ⟨bottom, hbottomSupport⟩
  let top' : {z : Site 2 // z ∈ V.support} :=
    ⟨top, htopSupport⟩
  obtain ⟨W'⟩ :=
    V.connected_induce_support.preconnected bottom' top'
  let inclusion :
      (hypercubicLattice 2).induce {z : Site 2 | z ∈ V.support} ↪g
        hypercubicLattice 2 :=
    SimpleGraph.Embedding.induce {z : Site 2 | z ∈ V.support}
  let W := W'.map inclusion.toHom
  change (hypercubicLattice 2).Walk bottom top at W
  refine ⟨lower, upper, bottom, top, W, ?_, ?_, ?_, ?_⟩
  · exact hbottomRow
  · exact htopRow
  · intro z hz
    have hzS : z ∈ S := by simpa [S] using hz
    have hzRows : z 1 ∈ rows := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
    exact ⟨rows.min'_le (z 1) hzRows, rows.le_max' (z 1) hzRows⟩
  · intro z hz
    change z ∈ (W'.map inclusion.toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact z'.property

end

end StatMech.FrontierD
