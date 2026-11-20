/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Walls.bc122carrier

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














theorem bgf_targets_sep_of_arms_sep (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {aᵢ aⱼ zᵢ zⱼ : Site d}
    (hri : (bc67_contractedLattice ω L y).Reachable aᵢ zᵢ)
    (hrj : (bc67_contractedLattice ω L y).Reachable aⱼ zⱼ)
    (hcut : ¬ (bc67_contractedLattice ω L y).Reachable aᵢ aⱼ) :
    ¬ (bc67_contractedLattice ω L y).Reachable zᵢ zⱼ := by
  intro hz
  exact hcut (hri.trans (hz.trans hrj.symm))




theorem bgf_three_targets_separated (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {a₁ a₂ a₃ z₁ z₂ z₃ : Site d}
    (hr₁ : (bc67_contractedLattice ω L y).Reachable a₁ z₁)
    (hr₂ : (bc67_contractedLattice ω L y).Reachable a₂ z₂)
    (hr₃ : (bc67_contractedLattice ω L y).Reachable a₃ z₃)
    (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
    (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
    (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
    ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
    ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
    ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃ :=
  ⟨bgf_targets_sep_of_arms_sep ω L y hr₁ hr₂ hc₁₂,
   bgf_targets_sep_of_arms_sep ω L y hr₁ hr₃ hc₁₃,
   bgf_targets_sep_of_arms_sep ω L y hr₂ hr₃ hc₂₃⟩



theorem bgf_boundary_targets_distinct (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {z₁ z₂ z₃ : Site d}
    (hs₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂)
    (hs₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃)
    (hs₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) :
    z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ :=
  ⟨fun h => hs₁₂ (h ▸ Reachable.refl _),
   fun h => hs₁₃ (h ▸ Reachable.refl _),
   fun h => hs₂₃ (h ▸ Reachable.refl _)⟩









theorem bgf_gnTrif_three_boundary_targets (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a₁ a₂ a₃ : Site d)
    (hb₁ : a₁ ∈ box d R) (hb₂ : a₂ ∈ box d R) (hb₃ : a₃ ∈ box d R)
    (hi₁ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite)
    (hi₂ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite)
    (hi₃ : (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite)
    (hc₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
    (hc₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
    (hc₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧
      ((bc67_contractedLattice ω L y).Reachable a₁ z₁ ∧
       (bc67_contractedLattice ω L y).Reachable a₂ z₂ ∧
       (bc67_contractedLattice ω L y).Reachable a₃ z₃) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨z₁, hzb₁, hr₁⟩ := bc101_arm_reaches_boundary ω L R hR y a₁ hb₁ hi₁
  obtain ⟨z₂, hzb₂, hr₂⟩ := bc101_arm_reaches_boundary ω L R hR y a₂ hb₂ hi₂
  obtain ⟨z₃, hzb₃, hr₃⟩ := bc101_arm_reaches_boundary ω L R hR y a₃ hb₃ hi₃
  have hsep := bgf_three_targets_separated ω L y hr₁ hr₂ hr₃ hc₁₂ hc₁₃ hc₂₃
  exact ⟨z₁, z₂, z₃, ⟨hzb₁, hzb₂, hzb₃⟩, ⟨hr₁, hr₂, hr₃⟩, hsep,
    bgf_boundary_targets_distinct ω L y hsep.1 hsep.2.1 hsep.2.2⟩




theorem bgf_arm_boundary_separated (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y : Site d) (htri : bc67_IsGnTrifurcation ω L y)
    (harmbox : ∀ a, (bc67_GnIncident ω L y a) →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → a ∈ box d R) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d R ∧ z₂ ∈ vertexBoundary d R ∧ z₃ ∈ vertexBoundary d R) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨a₁, a₂, a₃, ⟨hin₁, hin₂, hin₃⟩, ⟨hi₁, hi₂, hi₃⟩, hc₁₂, hc₁₃, hc₂₃⟩ := htri
  obtain ⟨z₁, z₂, z₃, hzb, _hr, hsep, hdist⟩ :=
    bgf_gnTrif_three_boundary_targets ω L R hR y a₁ a₂ a₃
      (harmbox a₁ hin₁ hi₁) (harmbox a₂ hin₂ hi₂) (harmbox a₃ hin₃ hi₃)
      hi₁ hi₂ hi₃ hc₁₂ hc₁₃ hc₂₃
  exact ⟨z₁, z₂, z₃, hzb, hsep, hdist⟩















def bgf_WithinHubTips (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d) :
    Prop :=
  ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
    (∀ j, arm y j ∈ vertexBoundary d R) ∧
    (∀ j k, j ≠ k → ¬ (bc67_contractedLattice ω L y).Reachable (arm y j) (arm y k))





theorem bgf_HubBoundaryArms_within_hub_free (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {arm : Site d → Fin 3 → Site d} (hwit : bgf_WithinHubTips ω L R arm) :
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j k, arm y j = arm y k → j = k) := by
  refine ⟨fun y hyb hyt j => (hwit y hyb hyt).1 j, ?_⟩
  intro y hyb hyt j k hjk
  by_contra hjkne
  exact (hwit y hyb hyt).2 j k hjkne (hjk ▸ Reachable.refl _)



















theorem bgf_perNode_cut_needs_common_carrier :
    ((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4 := by
  classical
  
  have hadj23 : ((SimpleGraph.fromEdgeSet
      {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
      (0 : Fin 5)).Adj 2 3 := by
    rw [SimpleGraph.deleteIncidenceSet_adj]
    refine ⟨?_, by decide, by decide⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by right; right; left; rfl, by decide⟩
  have hadj34 : ((SimpleGraph.fromEdgeSet
      {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
      (0 : Fin 5)).Adj 3 4 := by
    rw [SimpleGraph.deleteIncidenceSet_adj]
    refine ⟨?_, by decide, by decide⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by right; right; right; rfl, by decide⟩
  exact hadj23.reachable.trans hadj34.reachable

















theorem bgf_globalForest_of_withinHub_and_cross (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {arm : Site d → Fin 3 → Site d} (hwit : bgf_WithinHubTips ω L R arm)
    (hcross : (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ∀ j k, arm y j = arm z k → y = z ∧ j = k) ∧
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ∀ j, arm y j ≠ z))
    (base : ↑(bc122_carrier ω L R arm))
    (hFmin : ∀ (F : SimpleGraph (↑(bc122_carrier ω L R arm) : Type)) [DecidableRel F.Adj],
      F ≤ bc122_starGraph ω L R arm → F.IsAcyclic →
      (∀ v : (↑(bc122_carrier ω L R arm) : Type), F.degree v = 1 →
        bc121_Protected ω L R (bc122_ιU ω L R arm base) v) →
      (∀ a b : (↑(bc122_carrier ω L R arm) : Type),
        bc121_Protected ω L R (bc122_ιU ω L R arm base) a →
        bc121_Protected ω L R (bc122_ιU ω L R arm base) b →
        (bc122_starGraph ω L R arm).Reachable a b → F.Reachable a b) →
      ∀ v : (↑(bc122_carrier ω L R arm) : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R := by
  have hHBA : bc122_HubBoundaryArms ω L R arm := by
    refine ⟨?_, hcross.1, hcross.2⟩
    intro y hyb hyt j; exact (hwit y hyb hyt).1 j
  exact bc122_boundaryStar_globalForest ω L R hHBA base hFmin




theorem bgf_withinHubTips_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bgf_WithinHubTips ω L R (fun _ _ => (0 : Site d)) := by
  intro y hyb hyt; exact absurd hyt (hno y hyb)










































theorem bgf_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (z₁ z₂ z₃ : Site d),
      ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ →
      ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ →
      ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃ →
      z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d),
      bgf_WithinHubTips ω L R arm →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j k, arm y j = arm y k → j = k)) ∧
    
    (((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R →
      ∀ (arm : Site d → Fin 3 → Site d),
      bgf_WithinHubTips ω L R arm → True) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L y z₁ z₂ z₃ h₁₂ h₁₃ h₂₃; exact bgf_boundary_targets_distinct ω L y h₁₂ h₁₃ h₂₃
  · intro ω L R arm hwit; exact bgf_HubBoundaryArms_within_hub_free ω L R hwit
  · exact bgf_perNode_cut_needs_common_carrier
  · intro ω L R hR arm hwit; trivial

end StatMech.Walls
