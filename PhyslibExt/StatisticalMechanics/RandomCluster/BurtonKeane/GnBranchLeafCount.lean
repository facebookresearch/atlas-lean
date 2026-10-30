/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FiberForestSpanningTree
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount

/-!
# Branch and leaf counts on a fibre of the contracted lattice

On a fibre of contracted boxes the spanning forest has no more branch vertices than leaves, so an
injective leaf-to-boundary map bounds the fibre's trifurcation count.

## i. Overview

For a fibre `c` of the contracted lattice (boxes with the same residue) and a finite carrier `S`,
the spanning forest `bc75_spanForest` has branch vertices `bc80_branchFinset` and leaves
`bc80_leafFinset`. The branch–leaf inequality bounds `bc80_GnTrifCount` by the number of leaves, and
an injective leaf-to-boundary map bounds it by `|∂B_R|`. The set `bc80_gapSet` records fibre
trifurcations that are not branch vertices; when it is empty the coarse count is bounded by the
branch count.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc80_branch_le_leaf` : branch vertices are at most leaves
- `bc80_GnTrifCount_le_boundary` : the fibre count is at most the boundary size
- `bc80_fiber_le_boundary_via_branch` : fibre trifurcation data bound the fibre size
- `bc80_status` : the statements together

## iii. Table of contents

- A. Definitions
- B. Results
- C. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


/-! ## A. Definitions -/

open Classical in
/-- Leaves of the fibre spanning forest. -/
noncomputable def bc80_leafFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] : Finset (↑S : Type) :=
  Finset.univ.filter (fun v => (bc75_spanForest ω L R c S).degree v = 1)


open Classical in
/-- Vertices of degree at least three of the fibre spanning forest. -/
noncomputable def bc80_branchFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] : Finset (↑S : Type) :=
  Finset.univ.filter (fun v => 3 ≤ (bc75_spanForest ω L R c S).degree v)

/-- The number of branch vertices of the fibre spanning forest. -/
noncomputable def bc80_GnTrifCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] : ℕ :=
  (bc80_branchFinset ω L R c S).card


/-! ## B. Results -/

open Classical in
lemma bc80_branch_le_leaf (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card := by
  classical
  have hacyc : (bc75_spanForest ω L R c S).IsAcyclic := bc75_spanForest_acyclic ω L R c S
  have hkey := flc2_forest_internal_le_leaves (bc75_spanForest ω L R c S) hacyc hmin
  simpa only [bc80_branchFinset, bc80_leafFinset] using hkey


open Classical in
lemma bc80_GnTrifCount_le_leaf (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    bc80_GnTrifCount ω L R c S ≤ (bc80_leafFinset ω L R c S).card :=
  bc80_branch_le_leaf ω L R c S hmin


open Classical in
/-- The leaves of the fibre spanning forest map injectively into the boundary of `B_R`. -/
def bc80_LeafBoundaryInj (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] : Prop :=
  ∃ lamL : (↑S : Type) → Site d,
    (∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 → lamL v ∈ vertexBoundary d R) ∧
    Set.InjOn lamL (univ.filter (fun v => (bc75_spanForest ω L R c S).degree v = 1))


open Classical in
lemma bc80_leaf_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    (bc80_leafFinset ω L R c S).card ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨lamL, hmap, hinj⟩ := hleaf
  have hkey := flc2_leaf_card_le_boundary (bc75_spanForest ω L R c S) R lamL hmap hinj
  simpa only [bc80_leafFinset] using hkey


open Classical in
lemma bc80_branch_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    (bc80_branchFinset ω L R c S).card ≤ boxSV_boundaryCard d R :=
  le_trans (bc80_branch_le_leaf ω L R c S hmin) (bc80_leaf_le_boundary ω L R c S hleaf)


open Classical in
lemma bc80_GnTrifCount_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard d R :=
  bc80_branch_le_boundary ω L R c S hmin hleaf


open Classical in
lemma bc80_coarseTrif_mem_branch_of_gnCut (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : y ∈ S) {v₁ v₂ v₃ : (↑S : Type)}
    (hadj₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₁)
    (hadj₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₂)
    (hadj₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₃)
    (hcut₁₂ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩)
    (hcut₁₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩)
    (hcut₂₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩) :
    (⟨y, hyS⟩ : (↑S : Type)) ∈ bc80_branchFinset ω L R c S := by
  classical
  rw [bc80_branchFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    bc75_deg3_in_spanForest_of_gnCut ω L R c hyS hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃⟩


open Classical in
lemma bc80_coarseCount_le_branch_on_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
    (htriData : ∀ y (hy : y ∈ bc73_fiber ω L R c),
      ∃ (v₁ v₂ v₃ : (↑S : Type))
        (h₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₁)
        (h₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₂)
        (h₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₃),
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩)) :
    (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
  classical
  set ι : Site d → (↑S : Type) := fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩
    else Classical.arbitrary (↑S : Type) with hι
  refine Finset.card_le_card_of_injOn ι ?_ ?_
  · intro y hy
    have hy' : y ∈ bc73_fiber ω L R c := hy
    have hιeq : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dite_eq_left hy']
    rw [hιeq]
    obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, hc₁₂, hc₁₃, hc₂₃⟩ := htriData y hy'
    exact bc80_coarseTrif_mem_branch_of_gnCut ω L R c S (hyS y hy') h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · intro y hy z hz hyz
    have hy' : y ∈ bc73_fiber ω L R c := hy
    have hz' : z ∈ bc73_fiber ω L R c := hz
    have hιy : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dite_eq_left hy']
    have hιz : ι z = ⟨z, hyS z hz'⟩ := by simp only [hι, dite_eq_left hz']
    rw [hιy, hιz] at hyz
    exact congrArg Subtype.val hyz


open Classical in
lemma bc80_coarseCount_le_branch_of_gnData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)),
      (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleaf⟩ := h
  have : Nonempty (↑S : Type) := hSne
  exact ⟨S, hSfin, bc80_coarseCount_le_branch_on_carrier ω L R c S hyS htriData⟩


open Classical in
lemma bc80_leafBoundaryInj_of_gnData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hleafmap : ∀ v : (↑S : Type),
      (bc75_spanForest ω L R c S).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    bc80_LeafBoundaryInj ω L R c S := by
  classical
  refine ⟨Subtype.val, hleafmap, ?_⟩
  intro a _ b _ hab
  exact Subtype.ext hab


open Classical in
lemma bc80_fiber_le_boundary_via_branch (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleafmap⟩ := h
  have : Nonempty (↑S : Type) := hSne
  have hfb : (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card :=
    bc80_coarseCount_le_branch_on_carrier ω L R c S hyS htriData
  have hbb : (bc80_branchFinset ω L R c S).card ≤ boxSV_boundaryCard d R :=
    bc80_branch_le_boundary ω L R c S hmin (bc80_leafBoundaryInj_of_gnData ω L R c S hleafmap)
  exact le_trans hfb hbb


open Classical in
/-- Fibre trifurcations that are not branch vertices of the fibre spanning forest. -/
noncomputable def bc80_gapSet (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S) : Finset (Site d) := by
  classical
  exact (bc73_fiber ω L R c).filter
    (fun y => if hy : y ∈ bc73_fiber ω L R c
              then (⟨y, hyS y hy⟩ : (↑S : Type)) ∉ bc80_branchFinset ω L R c S
              else False)


open Classical in
lemma bc80_mem_gapSet (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S) (y : Site d) :
    y ∈ bc80_gapSet ω L R c S hyS ↔
      ∃ hy : y ∈ bc73_fiber ω L R c,
        (⟨y, hyS y hy⟩ : (↑S : Type)) ∉ bc80_branchFinset ω L R c S := by
  classical
  rw [bc80_gapSet, Finset.mem_filter]
  constructor
  · rintro ⟨hy, hcond⟩
    rw [dite_eq_left hy] at hcond
    exact ⟨hy, hcond⟩
  · rintro ⟨hy, hbr⟩
    exact ⟨hy, by rw [dite_eq_left hy]; exact hbr⟩


open Classical in
lemma bc80_coarseCount_le_branch_of_gap_empty (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
    (hgap : bc80_gapSet ω L R c S hyS = ∅) :
    (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
  classical
  rcases (bc73_fiber ω L R c).eq_empty_or_nonempty with hemp | hne
  · rw [hemp]; simp
  · have : Nonempty (↑S : Type) := ⟨⟨hne.choose, hyS hne.choose hne.choose_spec⟩⟩
    set ι : Site d → (↑S : Type) := fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩
      else Classical.arbitrary (↑S : Type) with hι
    refine Finset.card_le_card_of_injOn ι ?_ ?_
    · intro y hy
      have hy' : y ∈ bc73_fiber ω L R c := hy
      have hιeq : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dite_eq_left hy']
      rw [hιeq]
      by_contra hbr
      have : y ∈ bc80_gapSet ω L R c S hyS :=
        (bc80_mem_gapSet ω L R c S hyS y).mpr ⟨hy', hbr⟩
      rw [hgap] at this; exact absurd this (Finset.notMem_empty y)
    · intro y hy z hz hyz
      have hy' : y ∈ bc73_fiber ω L R c := hy
      have hz' : z ∈ bc73_fiber ω L R c := hz
      have hιy : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dite_eq_left hy']
      have hιz : ι z = ⟨z, hyS z hz'⟩ := by simp only [hι, dite_eq_left hz']
      rw [hιy, hιz] at hyz
      exact congrArg Subtype.val hyz


open Classical in
lemma bc80_upperLines_emptyFiber_fiber_bound {L R : ℕ} (hR : 1 ≤ R)
    (c : Fin 2 → Fin (2 * L + 1)) (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
    (bc73_fiber bc60_upperLines L R c).card ≤ boxSV_boundaryCard 2 R :=
  bc80_fiber_le_boundary_via_branch bc60_upperLines L R c
    (bc75_upperLines_emptyFiber_gnTrifData hR c hempty)

lemma bc80_upperLines_ambient_coarseTrif {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines hL

/-! ## C. Summary -/

open Classical in
lemma bc80_status :
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
      (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)),
      (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) →
      (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
      (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)),
      (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) →
      bc80_LeafBoundaryInj ω L R c S →
      bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard 2 R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R c S _ _ hmin
    exact bc80_branch_le_leaf ω L R c S (fun v => by convert hmin v using 2)
  · intro ω L R c S _ _ hmin hleaf
    exact bc80_GnTrifCount_le_boundary ω L R c S (fun v => by convert hmin v using 2) hleaf
  · intro ω L R c h; exact bc80_fiber_le_boundary_via_branch ω L R c h
  · intro L hL; exact bc80_upperLines_ambient_coarseTrif hL

end StatMech.Walls
