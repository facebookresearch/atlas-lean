/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.BKForestLib
import Code.Walls.bc26forest
import Code.Walls.bc37armadj
import Code.Walls.bc38acyclic
import Code.Walls.bc39spanning
import Code.Walls.bc40funnel

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem bc41_not_connected_removeSite_cutSite (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : x ≠ y) : ¬ Connected d (removeSite y ω) x y := by
  rintro ⟨w⟩
  have hy_notin : y ∉ w.support := arc_walk_avoids_x hxy w
  exact hy_notin w.end_mem_support































theorem bc41_rootSideComparable_allPar_false (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hne : x₀ ≠ y₀) (hconn : Connected d ω x₀ y₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc40_RootSideComparable ω n rank par := by
  intro hroot_side
  
  set rank : Site d → ℕ ×ₗ ℕ := fun z => toLex (if z = y₀ then 1 else 0, 0) with hrank
  set par : Site d → Site d := fun _ => y₀ with hpar
  have hlt : rank x₀ < rank y₀ := by
    simp only [hrank, if_neg hne, if_pos]
    exact stt_lex_lt_fst (by norm_num)
  
  have hforced : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    hroot_side rank par x₀ hx0box htri0 y₀ hy0box htriy0 hne hconn hlt hne
  simp only [hpar] at hforced
  exact bc41_not_connected_removeSite_cutSite ω hne hforced


























def bc41_RootSideComparableArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    bc37_ArmAdjacent ω n y (par y) →
    Connected d (removeSite y ω) x (par y)

set_option linter.unusedVariables false in







theorem bc41_rootSideComparableArm_not_trapped_at_self (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) {y₀ : Site d} :
    bc37_ArmAdjacent ω n y₀ ((fun _ => y₀) y₀) → False := by
  intro hadj
  exact bc37_armAdjacent_irrefl ω n y₀ hadj



















theorem bc41_armRealisation_of_cutGeometryFixed'_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc41_RootSideComparableArm ω n rank par) :
    bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  have hrs : Connected d (removeSite y ω) x (par y) :=
    hroot_side rank par x hxbox htri y hybox htriy hxy hconn hlt hxne hpadj
  exact hfun x hxy hrs



theorem bc41_parentFunneling_of_cutGeometryFixed'_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc41_RootSideComparableArm ω n rank par) :
    bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n (bc39_armAdjSpanning ω n)
    (bc41_armRealisation_of_cutGeometryFixed'_arm ω n hgeo hroot_side)


theorem bc41_selfDownArm_of_cutGeometryFixed'_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc41_RootSideComparableArm ω n rank par) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc41_parentFunneling_of_cutGeometryFixed'_arm ω n hgeo hroot_side)








theorem bc41_burton_keane_bernoulli_of_cutGeometryFixed'_arm (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootSideComparableArm ω n rank par)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc41_selfDownArm_of_cutGeometryFixed'_arm ω n (hgeo ω n hn) (hroot_side ω n hn))
    htrif


























def bc41_RootWardAvoidingWalk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    bc37_ArmAdjacent ω n y (par y) →
    ∃ p : (openSubgraph d ω).Walk x (par y), ∀ v ∈ p.support, v ≠ y






theorem bc41_rootSideComparableArm_of_rootWardAvoidingWalk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hwalk : bc41_RootWardAvoidingWalk ω n rank par) :
    bc41_RootSideComparableArm ω n rank par := by
  intro x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  obtain ⟨p, hp⟩ := hwalk x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  have hconn_cut : Connected d (removeSites {y} ω) x (par y) := by
    apply bc39_connected_removeSites_of_walk_avoids {y} ω p
    intro v hv
    rw [Finset.mem_singleton]
    exact hp v hv
  rwa [daep_removeSites_singleton] at hconn_cut







theorem bc41_burton_keane_bernoulli_of_rootWardAvoidingWalk (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
    (hwalk : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootWardAvoidingWalk ω n rank par)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc41_burton_keane_bernoulli_of_cutGeometryFixed'_arm hd p hp1 hp0 hgeo
    (fun ω n hn rank par =>
      bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par (hwalk ω n hn rank par))
    htrif











theorem bc41_rootWardAvoidingWalk_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc41_RootWardAvoidingWalk ω n rank par := by
  intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem bc41_rootSideComparableArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc41_RootSideComparableArm ω n rank par :=
  bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par
    (bc41_rootWardAvoidingWalk_of_noTrif ω n rank par hno)

set_option linter.unusedVariables false in













theorem bc41_rootWardAvoidingWalk_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (rank : Site d → ℕ ×ₗ ℕ)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    bc41_RootWardAvoidingWalk ω n rank (fun _ => x₀) := by
  intro x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  
  simp only at hxpar hadj
  
  rcases htwo x hxbox htri with hx | hx
  · 
    exact absurd hx hxpar
  · 
    rcases htwo y hybox htriy with hy | hy
    · 
      rw [hy] at hadj
      exact absurd hadj (bc37_armAdjacent_irrefl ω n x₀)
    · 
      rw [hx, hy] at hxy
      exact absurd rfl hxy



theorem bc41_rootSideComparableArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (rank : Site d → ℕ ×ₗ ℕ)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    bc41_RootSideComparableArm ω n rank (fun _ => x₀) :=
  bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank (fun _ => x₀)
    (bc41_rootWardAvoidingWalk_of_twoTrif ω n rank htwo hx0y0)

















theorem bc41_cutGeometryFixed'_downArm_guard_vacuous (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d, ¬ Connected d (removeSite t ω) (b t) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, hself, _hfun⟩ := hclauses t s htbox htri hadj
  
  exact ⟨b, hself⟩








theorem bc41_cutGeometryFixed'_no_downArm_trap (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d,
      (∀ x, x ≠ t → Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) ∧
      ¬ Connected d (removeSite t ω) (b t) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  exact ⟨b, hfun, hself⟩

end StatMech.Walls
