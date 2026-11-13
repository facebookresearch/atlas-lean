/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulShearEmbedding
import Code.FrontierD.FKRectRefinedDualPrimalPointDisjoint



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section



theorem FKRectIntegralSquareDartPath.ne_nil_of_ne
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (hpq : p ≠ q) :
    l ≠ [] := by
  intro hl
  subst l
  cases h
  exact hpq rfl



theorem FKRectIntegralSquareDartPath.exists_faithfulShearWalk_of_ne_nil
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (hl : l ≠ []) :
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q),
      ∀ z ∈ V.support,
        ∃ d ∈ l, ∃ r ∈ fkRectFaithfulShearDartRoute d,
          z = fkRectPairSite r := by
  obtain ⟨V, hV⟩ := h.exists_faithfulShearWalk
  refine ⟨V, ?_⟩
  intro z hz
  rcases hV z hz with hstart | hroute
  · cases h with
    | nil => exact (hl rfl).elim
    | @cons d q r k hend tail =>
        refine ⟨d, by simp, fkRectFaithfulShearPair d.1, ?_, ?_⟩
        · rcases d with ⟨a, mu⟩
          fin_cases mu <;> simp [fkRectFaithfulShearDartRoute]
        · simpa [fkRectFaithfulShearPoint] using hstart
  · exact hroute



theorem exists_fkRectFaithfulShearWalks_supportDisjoint_of_openBlocks
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    (hF : ∀ e, e ∈ F ↔ omega e = true)
    {p q a b : Int × Int}
    {l k : List FKRectIntegralSquareDart}
    (hlpath : FKRectIntegralSquareDartPath p q l)
    (hkpath : FKRectIntegralSquareDartPath a b k)
    (hlblocks : FKRectRefinedDualOpenEdgeBlocks R omega l)
    (hkblocks : FKRectRefinedOpenEdgeBlocks R F k)
    (hlne : l ≠ []) (hkne : k ≠ []) :
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q),
      ∃ W : (hypercubicLattice 2).Walk
          (fkRectFaithfulShearPoint a) (fkRectFaithfulShearPoint b),
        ∀ z, z ∈ V.support → z ∈ W.support → False := by
  obtain ⟨V, hV⟩ :=
    hlpath.exists_faithfulShearWalk_of_ne_nil hlne
  obtain ⟨W, hW⟩ :=
    hkpath.exists_faithfulShearWalk_of_ne_nil hkne
  refine ⟨V, W, ?_⟩
  intro z hzV hzW
  obtain ⟨d, hdl, r, hr, hzVr⟩ := hV z hzV
  obtain ⟨e, hek, s, hs, hzWs⟩ := hW z hzW
  have hincident :=
    fkRectIntegralSquareDartsIncident_of_faithfulRouteSite d e r s hr hs
      (hzVr.symm.trans hzWs)
  exact (hlblocks.not_incident_of_mem_edgeBlocks
    R omega F hF hkblocks hdl hek) hincident

end

end StatMech.FrontierD
