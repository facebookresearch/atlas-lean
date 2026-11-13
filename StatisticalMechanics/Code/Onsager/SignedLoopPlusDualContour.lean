/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopLowTempPlus
import Code.Lattice.PeierlsContourClose2
import Code.Ising.KWGeometricDual












open Finset SimpleGraph Set

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section



theorem ons_fvCutEdges_eq_crossEdges_minusSet
    {d : Nat} (B : Finset (Sym2 (Site d)))
    (config : ConfigSpace (Site d))
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet) :
    ons_fvCutEdges B config = crossEdges (minusSet config) B := by
  classical
  ext e
  unfold ons_fvCutEdges crossEdges
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro heB
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : (hypercubicLattice d).Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (hB s(x, y) heB)
      rw [crosses_mk, bond_mk]
      cases hx : config x <;> cases hy : config y <;>
        norm_num [spin, minusSet, hx, hy]



def ons_plusDualContour (n : Nat)
    (tau : {x // x ∈ box 2 n} → Bool) : Finset (Sym2 (Site 2)) :=
  (ons_fvCutEdges (bondFinsetTouch 2 n) (glue (plusField 2) tau)).image
    flankFacesSym



theorem coe_ons_plusDualContour_eq_faceBoundaryGraph_edgeSet
    (n : Nat) (tau : {x // x ∈ box 2 n} → Bool) :
    (↑(ons_plusDualContour n tau) : Set (Sym2 (Site 2))) =
      (faceBoundaryGraph (minusSet (glue (plusField 2) tau))).edgeSet := by
  classical
  let config := glue (plusField 2) tau
  let K := minusSet config
  have hKbox : K ⊆ box 2 n := minusSet_glue_plus_subset_box tau
  have hcut : ons_fvCutEdges (bondFinsetTouch 2 n) config =
      crossEdges K (bondFinsetTouch 2 n) := by
    exact ons_fvCutEdges_eq_crossEdges_minusSet
      (bondFinsetTouch 2 n) config
      (bondFinsetTouch_subset_edgeSet n)
  ext dualEdge
  constructor
  · intro hdual
    rw [Finset.mem_coe, ons_plusDualContour, Finset.mem_image] at hdual
    obtain ⟨primalEdge, hprimal, rfl⟩ := hdual
    rw [hcut] at hprimal
    have hboundary : primalEdge ∈ boundaryEdgeSet K := by
      rw [← coe_crossEdges_eq_boundaryEdgeSet hKbox]
      exact hprimal
    exact (flankFacesSym_mem_edgeSet hboundary).1
  · intro hdual
    have hboundary : symPrimalSym dualEdge ∈ boundaryEdgeSet K :=
      symPrimalSym_mem_boundaryEdgeSet hdual
    have hprimal : symPrimalSym dualEdge ∈
        crossEdges K (bondFinsetTouch 2 n) := by
      rw [← Finset.mem_coe, coe_crossEdges_eq_boundaryEdgeSet hKbox]
      exact hboundary
    rw [Finset.mem_coe, ons_plusDualContour, Finset.mem_image]
    refine ⟨symPrimalSym dualEdge, ?_, ?_⟩
    · rw [hcut]
      exact hprimal
    · induction dualEdge using Sym2.inductionOn with
      | _ f g =>
          have hfg : (hypercubicLattice 2).Adj f g :=
            (SimpleGraph.mem_edgeSet _).mp hdual |>.1
          rw [symPrimalSym_mk]
          exact flankFacesSym_symPrimal hfg

private theorem kwg_incidentMod2_iff_mem_incidenceSet_of_mem_edge
    (H : SimpleGraph (Site 2)) {edge : Sym2 (Site 2)} {f : Site 2}
    (hedge : edge ∈ H.edgeSet) :
    kwg_incidentMod2 f edge ↔ edge ∈ H.incidenceSet f := by
  induction edge using Sym2.inductionOn with
  | _ x y =>
      have hxy : H.Adj x y := (SimpleGraph.mem_edgeSet H).mp hedge
      rw [kwg_incidentMod2_mk, H.mk'_mem_incidenceSet_iff]
      constructor
      · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact ⟨hxy, Or.inl rfl⟩
        · exact ⟨hxy, Or.inr rfl⟩
      · rintro ⟨_, rfl | rfl⟩
        · exact Or.inl ⟨rfl, hxy.ne.symm⟩
        · exact Or.inr ⟨rfl, hxy.ne⟩





theorem ons_plusDualContour_isEven
    (n : Nat) (tau : {x // x ∈ box 2 n} → Bool) :
    kwg_IsEven (fun edge : Sym2 (Site 2) ↦ edge)
      (ons_plusDualContour n tau) := by
  classical
  let K := minusSet (glue (plusField 2) tau)
  let H := faceBoundaryGraph K
  intro f
  have hedgeSet : (↑(ons_plusDualContour n tau) : Set (Sym2 (Site 2))) =
      H.edgeSet :=
    coe_ons_plusDualContour_eq_faceBoundaryGraph_edgeSet n tau
  have hfilter :
      (ons_plusDualContour n tau).filter
          (fun edge ↦ kwg_incidentMod2 f edge) =
        H.incidenceFinset f := by
    ext edge
    rw [Finset.mem_filter, H.mem_incidenceFinset]
    constructor
    · rintro ⟨hedge, hinc⟩
      have hedgeH : edge ∈ H.edgeSet := by
        rw [← hedgeSet]
        exact hedge
      exact (kwg_incidentMod2_iff_mem_incidenceSet_of_mem_edge
        H hedgeH).mp hinc
    · intro hinc
      have hedgeH : edge ∈ H.edgeSet := H.incidenceSet_subset f hinc
      refine ⟨?_, (kwg_incidentMod2_iff_mem_incidenceSet_of_mem_edge
        H hedgeH).mpr hinc⟩
      have hedgeF : edge ∈ (↑(ons_plusDualContour n tau) :
          Set (Sym2 (Site 2))) := by
        rw [hedgeSet]
        exact hedgeH
      exact hedgeF
  change Even ((ons_plusDualContour n tau).filter
    (fun edge ↦ kwg_incidentMod2 f edge)).card
  rw [hfilter, H.card_incidenceFinset_eq_degree]
  exact degree_faceBoundaryGraph_even K f

end

end StatMech.Onsager
