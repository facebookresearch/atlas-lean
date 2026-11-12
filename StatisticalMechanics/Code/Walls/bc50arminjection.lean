/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Walls.bc48classical
import Code.Walls.bc49finiteenergy

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

















theorem bc50_injection_of_countBound (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcount : bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n) :
    bc48_ClassicalBoundaryArmInjection ω n := by
  classical
  
  have hcard : Fintype.card {x : Site d // x ∈ bc48_classicalTrifFinset ω n}
      ≤ (tfc_boundaryFinset d n).card := by
    rw [Fintype.card_coe, tfc_boundaryFinset_card]
    exact hcount
  
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := {x : Site d // x ∈ bc48_classicalTrifFinset ω n}) hcard
  
  set φ : Site d → Site d :=
    fun x => if h : x ∈ bc48_classicalTrifFinset ω n then (f ⟨x, h⟩ : Site d) else x with hφ
  refine ⟨φ, ?_, ?_⟩
  · 
    intro x hxbox hcl
    have hmem : x ∈ bc48_classicalTrifFinset ω n := bc48_mem_classicalTrifFinset.mpr ⟨hxbox, hcl⟩
    have hφx : φ x = (f ⟨x, hmem⟩ : Site d) := by rw [hφ]; simp only [dif_pos hmem]
    rw [hφx]
    have hrange : (f ⟨x, hmem⟩ : Site d) ∈ tfc_boundaryFinset d n :=
      hf (Set.mem_range_self _)
    exact tfc_mem_boundaryFinset.mp hrange
  · 
    intro x hxbox hclx y hybox hcly hxy
    have hmx : x ∈ bc48_classicalTrifFinset ω n := bc48_mem_classicalTrifFinset.mpr ⟨hxbox, hclx⟩
    have hmy : y ∈ bc48_classicalTrifFinset ω n := bc48_mem_classicalTrifFinset.mpr ⟨hybox, hcly⟩
    have hφx : φ x = (f ⟨x, hmx⟩ : Site d) := by rw [hφ]; simp only [dif_pos hmx]
    have hφy : φ y = (f ⟨y, hmy⟩ : Site d) := by rw [hφ]; simp only [dif_pos hmy]
    rw [hφx, hφy] at hxy
    exact congrArg Subtype.val (f.injective hxy)





theorem bc50_countBound_of_injection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc48_ClassicalBoundaryArmInjection ω n) :
    bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n :=
  bc48_Tcount_classical_le_boundary_of_residue ω n h




theorem bc50_injection_iff_countBound (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_ClassicalBoundaryArmInjection ω n ↔
      bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n :=
  ⟨bc50_countBound_of_injection ω n, bc50_injection_of_countBound ω n⟩














theorem bc50_arms_reach_distinct_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x : Site d) (hxbox : x ∈ box d n) (hcl : bc47_IsClassicalTrifurcation ω x) :
    ∃ a₁ a₂ a₃ z₁ z₂ z₃ : Site d,
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) ∧
      (z₁ ∈ vertexBoundary d (n + 1) ∧ z₂ ∈ vertexBoundary d (n + 1) ∧
        z₃ ∈ vertexBoundary d (n + 1)) ∧
      ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
      (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧
        Connected d (removeSite x ω) a₃ z₃) := by
  obtain ⟨a₁, a₂, a₃, _hne, ⟨hadj1, hadj2, hadj3⟩, ⟨hs12, hs13, hs23⟩,
    ⟨z₁, hz1b, hz1c⟩, ⟨z₂, hz2b, hz2c⟩, ⟨z₃, hz3b, hz3c⟩⟩ :=
    bc48_classical_reaches_boundary ω n x hxbox hcl
  
  have hz12 : z₁ ≠ z₂ := by
    intro h; subst h; exact hs12 (hz1c.trans hz2c.symm)
  have hz13 : z₁ ≠ z₃ := by
    intro h; subst h; exact hs13 (hz1c.trans hz3c.symm)
  have hz23 : z₂ ≠ z₃ := by
    intro h; subst h; exact hs23 (hz2c.trans hz3c.symm)
  exact ⟨a₁, a₂, a₃, z₁, z₂, z₃, ⟨hz12, hz13, hz23⟩, ⟨hz1b, hz2b, hz3b⟩,
    ⟨hadj1, hadj2, hadj3⟩, ⟨hz1c, hz2c, hz3c⟩⟩













theorem bc50_classical_countBound_of_armForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) :
    bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (bc48_Tcount_classical_le_Tcount ω n) (sfa_Tcount_le_boundary_of_armForestReaching ω n h)





theorem bc50_ClassicalBoundaryArmInjection_of_armForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) :
    bc48_ClassicalBoundaryArmInjection ω n :=
  bc50_injection_of_countBound ω n (bc50_classical_countBound_of_armForest ω n h)


theorem bc50_ClassicalBoundaryArmInjection_of_armForest_all
    (h : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), sfa_ArmForestReaching ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n :=
  fun ω n => bc50_ClassicalBoundaryArmInjection_of_armForest ω n (h ω n)

























theorem bc50_burton_keane_bernoulli_of_armForest (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), sfa_ArmForestReaching ω n)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc49_burton_keane_bernoulli_of_route hd p hp1 hp0
    (bc50_ClassicalBoundaryArmInjection_of_armForest_all harm) hroute





theorem bc50_burton_keane_bernoulli_of_armForest_routingCover
    (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), sfa_ArmForestReaching ω n)
    (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc49_burton_keane_bernoulli_of_routingCover hd p hp1 hp0
    (bc50_ClassicalBoundaryArmInjection_of_armForest_all harm) hrt


























theorem bc50_injection_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc48_ClassicalBoundaryArmInjection ω n := by
  apply bc50_injection_of_countBound
  rw [bc48_Tcount_classical_eq_zero_of_noTrif ω n hno]
  exact Nat.zero_le _


theorem bc50_countBound_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
  rw [bc48_Tcount_classical_eq_zero_of_noTrif ω n hno]; exact Nat.zero_le _












def bc50_shadowArmEnd : Fin 2 → Fin 3 → Fin 5 :=
  fun _h i => match i with | 0 => 2 | 1 => 3 | 2 => 4







theorem bc50_armEndpoint_map_not_injective :
    bc50_shadowArmEnd 0 0 = bc50_shadowArmEnd 1 0 ∧ (0 : Fin 2) ≠ 1 := by
  decide





theorem bc50_abstract_injection_exists :
    ∃ ψ : Fin 2 → Fin 5, Function.Injective ψ ∧ (∀ h, ψ h = 2 ∨ ψ h = 3 ∨ ψ h = 4) := by
  refine ⟨fun h => if h = 0 then 3 else 4, ?_, ?_⟩
  · intro a b hab; fin_cases a <;> fin_cases b <;> simp_all
  · intro h; fin_cases h <;> decide






theorem bc50_injection_notOverStrong (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc48_ClassicalBoundaryArmInjection ω n ↔
        bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n) ∧
      (¬ bc48_ClassicalBoundaryArmInjection ω n ↔
        boxSV_boundaryCard d n < bc48_Tcount_classical d ω n) := by
  refine ⟨bc50_injection_iff_countBound ω n, ?_⟩
  rw [bc50_injection_iff_countBound ω n, not_le]






theorem bc50_clawShadow_distinct_boundary_fires :
    ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) →
      ∃ n₁ n₂ n₃ : Fin 10,
        (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧
          bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧
        (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧
        (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧
        (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) :=
  bc48_clawShadow_classical_fires

end StatMech.Walls
