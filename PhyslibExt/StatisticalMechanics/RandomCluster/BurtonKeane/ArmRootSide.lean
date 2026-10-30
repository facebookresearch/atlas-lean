/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel

/-!
# Root-side comparability along arms

Root-side comparability over all parents fails; its arm form and root-ward avoiding walks, with the
weakened cut geometry, give arm realisation and parent funnelling.

## i. Overview

A site is never connected to `y` after `y` is removed, so root-side comparability over all parents
fails. The arm form `bc41_RootSideComparableArm` restricts to arm-adjacent parents, and
`bc41_RootWardAvoidingWalk` asks for an open walk to the parent avoiding `y`. Either, with
`bc40_ArmCutGeometryFixed'`, gives arm realisation and parent funnelling. Both hold with no
trifurcation or two trifurcations.

The configuration-wide form of these conditions, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`bc41_not_forall_cutGeometryFixed'_arm`, `bc41_not_forall_rootWardAvoidingWalk`). The Burton–Keane
theorems that assumed them were removed as vacuous.

## ii. Key results

- `bc41_parentFunneling_of_cutGeometryFixed'_arm` : parent funnelling from the arm form.
- `bc41_rootSideComparableArm_of_rootWardAvoidingWalk` : the arm form from root-ward walks.

## iii. Table of contents

- A. Comparability over all parents fails
- B. The arm form
- C. Root-ward avoiding walks
- D. Examples
- E. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Comparability over all parents fails -/

lemma bc41_not_connected_removeSite_cutSite (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : x ≠ y) : ¬ Connected d (removeSite y ω) x y := by
  rintro ⟨w⟩
  have hy_notin : y ∉ w.support := arc_walk_avoids_x hxy w
  exact hy_notin w.end_mem_support

lemma bc41_rootSideComparable_allPar_false (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hne : x₀ ≠ y₀) (hconn : Connected d ω x₀ y₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc40_RootSideComparable ω n rank par := by
  intro hroot_side
  set rank : Site d → ℕ ×ₗ ℕ := fun z => toLex (if z = y₀ then 1 else 0, 0) with hrank
  set par : Site d → Site d := fun _ => y₀ with hpar
  have hlt : rank x₀ < rank y₀ := by
    simp only [hrank, ite_eq_right hne, ite_eq_left]
    exact stt_lex_lt_fst (by norm_num)
  have hforced : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    hroot_side rank par x₀ hx0box htri0 y₀ hy0box htriy0 hne hconn hlt hne
  simp only [hpar] at hforced
  exact bc41_not_connected_removeSite_cutSite ω hne hforced

/-! ## B. The arm form -/

/-- Root-side comparability restricted to arm-adjacent parents. -/
def bc41_RootSideComparableArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    bc37_ArmAdjacent ω n y (par y) →
    Connected d (removeSite y ω) x (par y)

set_option linter.unusedVariables false in
lemma bc41_rootSideComparableArm_not_trapped_at_self (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) {y₀ : Site d} :
    bc37_ArmAdjacent ω n y₀ ((fun _ => y₀) y₀) → False := by
  intro hadj
  exact bc37_armAdjacent_irrefl ω n y₀ hadj

lemma bc41_armRealisation_of_cutGeometryFixed'_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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

lemma bc41_parentFunneling_of_cutGeometryFixed'_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc41_RootSideComparableArm ω n rank par) :
    bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n (bc39_armAdjSpanning ω n)
    (bc41_armRealisation_of_cutGeometryFixed'_arm ω n hgeo hroot_side)

lemma bc41_selfDownArm_of_cutGeometryFixed'_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      bc41_RootSideComparableArm ω n rank par) :
    bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc41_parentFunneling_of_cutGeometryFixed'_arm ω n hgeo hroot_side)

/-! ## C. Root-ward avoiding walks -/

/-- Root-ward avoiding walks: for connected trifurcations, an open walk from the lower one to the
parent
of the higher one avoiding the higher one. -/
def bc41_RootWardAvoidingWalk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    bc37_ArmAdjacent ω n y (par y) →
    ∃ p : (openSubgraph d ω).Walk x (par y), ∀ v ∈ p.support, v ≠ y

lemma bc41_rootSideComparableArm_of_rootWardAvoidingWalk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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

/-! ## D. Examples -/

lemma bc41_rootWardAvoidingWalk_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc41_RootWardAvoidingWalk ω n rank par := by
  intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma bc41_rootSideComparableArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc41_RootSideComparableArm ω n rank par :=
  bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par
    (bc41_rootWardAvoidingWalk_of_noTrif ω n rank par hno)

set_option linter.unusedVariables false in
lemma bc41_rootWardAvoidingWalk_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (rank : Site d → ℕ ×ₗ ℕ)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    bc41_RootWardAvoidingWalk ω n rank (fun _ => x₀) := by
  intro x hxbox htri y hybox htriy hxy hconn hlt hxpar hadj
  simp only at hxpar hadj
  rcases htwo x hxbox htri with hx | hx
  · exact absurd hx hxpar
  · rcases htwo y hybox htriy with hy | hy
    · rw [hy] at hadj
      exact absurd hadj (bc37_armAdjacent_irrefl ω n x₀)
    · rw [hx, hy] at hxy
      exact absurd rfl hxy

lemma bc41_rootSideComparableArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (rank : Site d → ℕ ×ₗ ℕ)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hx0y0 : x₀ ≠ y₀) :
    bc41_RootSideComparableArm ω n rank (fun _ => x₀) :=
  bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank (fun _ => x₀)
    (bc41_rootWardAvoidingWalk_of_twoTrif ω n rank htwo hx0y0)

lemma bc41_cutGeometryFixed'_downArm_guard_vacuous (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d, ¬ Connected d (removeSite t ω) (b t) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, hself, _hfun⟩ := hclauses t s htbox htri hadj
  exact ⟨b, hself⟩

lemma bc41_cutGeometryFixed'_no_downArm_trap (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc40_ArmCutGeometryFixed' ω n)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) :
    ∃ b : Site d → Site d,
      (∀ x, x ≠ t → Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) ∧
      ¬ Connected d (removeSite t ω) (b t) s := by
  obtain ⟨b, _hdata, hclauses⟩ := hgeo
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  exact ⟨b, hfun, hself⟩

/-! ## E. Unsatisfiability of the configuration-wide conditions -/

/-- `bc40_ArmCutGeometryFixed'` and `bc41_RootSideComparableArm` for every configuration and every
box
of radius `n ≥ 1` are impossible when `d ≥ 1`: this implies the configuration-wide bound
`Tcount ≤ |∂Λₙ|`, which `tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc41_not_forall_cutGeometryFixed'_arm (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc40_ArmCutGeometryFixed' ω n ∧
        ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
            bc41_RootSideComparableArm ω n rank par :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc36_Tcount_le_boundary_of_selfDownArm ω n hn
      (bc41_selfDownArm_of_cutGeometryFixed'_arm ω n (h ω n hn).1 (h ω n hn).2)

/-- `bc40_ArmCutGeometryFixed'` and `bc41_RootWardAvoidingWalk` for every configuration and every
box of
radius `n ≥ 1` are impossible when `d ≥ 1`: this implies the configuration-wide bound
`Tcount ≤ |∂Λₙ|`, which `tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma bc41_not_forall_rootWardAvoidingWalk (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc40_ArmCutGeometryFixed' ω n ∧
        ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
            bc41_RootWardAvoidingWalk ω n rank par :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    bc36_Tcount_le_boundary_of_selfDownArm ω n hn
      (bc41_selfDownArm_of_cutGeometryFixed'_arm ω n (h ω n hn).1
        fun rank par => bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par
          ((h ω n hn).2 rank par))

end StatMech.Walls
