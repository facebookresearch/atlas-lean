/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















import Mathlib
import Code.Walls.bfaforestassemble
import Code.Walls.bararmray
import Code.Walls.bc106separated
import Code.Walls.bc64coarseembed

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}










theorem bsd_boxes_disjoint {L : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hx : bc106_SeparatedCoarseTrif ω L x) (hy : bc106_SeparatedCoarseTrif ω L y) (hne : x ≠ y) :
    Disjoint (bc61_boxAround d L x) (bc61_boxAround d L y) :=
  bc106_boxes_disjoint hx hy hne














theorem bsd_deg3_free_per_trif {L : ℕ} {x : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hx : bc106_SeparatedCoarseTrif ω L x) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩ :=
  bc73_disjointBoxes_deg3 (bc106_gnTrif_of_separated hx)















theorem bsd_arm_tips_of_separated (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
    ∃ t : Fin 3 → Site d,
      (∀ i, t i ∈ vertexBoundary d R) ∧
      (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (t i)) ∧
      (∀ i, t i ≠ x) ∧
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (t i) (t j)) := by
  classical
  have htip : ∀ i, ∃ t, (bc67_contractedLattice ω L x).Reachable (arm i) t ∧
      t ∈ vertexBoundary d R := by
    intro i
    obtain ⟨r, hr0, hinj, hadjr, hreachr⟩ :=
      bar_armRay_of_infiniteComponent ω L x (arm i) (harminf i)
    have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k =>
      ((bc67_contractedLattice_le ω L x) (hadjr k)).1
    have h0box : r 0 ∈ box d R := by rw [hr0]; exact harmbox i
    obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
    exact ⟨r k, hreachr k, hk⟩
  choose tip htipreach htipbdry using htip
  refine ⟨tip, htipbdry, htipreach, ?_, ?_⟩
  · 
    intro i hti
    have hr := htipreach i
    rw [hti] at hr
    exact harmne i (bar_center_reach_eq ω L hr.symm)
  · 
    intro i j hij
    exact bar_armSep_of_rays ω L x (htipreach i) (htipreach j) (harmsep i j hij)
















theorem bsd_bc69_of_separated_singleStar_route (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxsep : bc106_SeparatedCoarseTrif ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j))
    (hroute : ∀ a : Fin 3 → Site d,
      (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) →
      (∀ i, a i ∈ vertexBoundary d R) →
      ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
    bc69_Gn_globalForest ω L R :=
  bgc_globalForest_of_trifForestData ω L R
    (bar_trifForestData_of_arms_route ω L R hR arm hxbox
      (bc106_gnTrif_of_separated hxsep) hsingle harmbox harmne harminf harmsep hroute)























theorem bsd_collapse_survives (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc64_arms_can_share_boundary L












theorem bsd_bk_of_bc69_forall (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc69_Gn_globalForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bfa_bk_of_bc69Forest p hp1 hp0 hdata













































theorem bsd_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x y : Site d),
      bc106_SeparatedCoarseTrif ω L x → bc106_SeparatedCoarseTrif ω L y → x ≠ y →
      Disjoint (bc61_boxAround d L x) (bc61_boxAround d L y)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d),
      bc106_SeparatedCoarseTrif ω L x →
      ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S)
        (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj),
        3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (x : Site d) (arm : Fin 3 → Site d),
      x ∈ box d R → bc106_SeparatedCoarseTrif ω L x →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) →
      (∀ i, arm i ∈ box d R) → (∀ i, arm i ≠ x) →
      (∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite) →
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) →
      (∀ a : Fin 3 → Site d,
        (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) →
        (∀ i, a i ∈ vertexBoundary d R) →
        ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) →
      bc69_Gn_globalForest ω L R) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L x y hx hy hne; exact bsd_boxes_disjoint hx hy hne
  · intro ω L x hx; exact bsd_deg3_free_per_trif hx
  · intro ω L R hR x arm hxbox hxsep hsingle harmbox harmne harminf harmsep hroute
    exact bsd_bc69_of_separated_singleStar_route ω L R hR arm hxbox hxsep hsingle
      harmbox harmne harminf harmsep hroute
  · intro L; exact bsd_collapse_survives L

end StatMech.Walls
