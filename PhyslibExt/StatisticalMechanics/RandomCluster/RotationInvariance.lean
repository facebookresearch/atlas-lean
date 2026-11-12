/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreSandwich
/-!
# Rotation invariance of `q = 2` FK edge densities on `ℤ^d`

All nearest-neighbour edges of `ℤ^d` have the same free, and the same wired, `q = 2`
infinite-volume edge density.

## i. Overview

Coordinate permutations and coordinate reflections of `ℤ^d` are box symmetries, so they preserve
the free and wired `q = 2` edge densities (`fkTI_free_density_shift_inv`). Translations preserve
the densities as well (`bdp_freeEdgeDensity_translation_inv`). Every nearest-neighbour edge
`{x, y}` can be translated to `{0, y - x}`, where `y - x = ±e_j` is a signed unit vector; a
reflection turns `-e_j` into `e_j` and a transposition of coordinates turns `e_j` into `e_0`.
Hence every edge of `ℤ^d` has the density of the reference edge `{0, e_0}`.

This discharges the rotation residues `ocs_FreeRotationResidue` and `ocs_WiredRotationResidue` for
genuine lattice edges `e'`. The residues for pairs `e'` that are not lattice edges are not
discharged.

## ii. Key results

- `rot_permBoxSym` : coordinate permutations as box symmetries.
- `rot_free_density_boxSym`, `rot_wired_density_boxSym` : box symmetries preserve the densities
  of edges of `ℤ^d`.
- `rot_free_edge_const`, `rot_wired_edge_const` : every lattice edge has the density of the
  reference edge `{0, e_0}`.
- `rot_freeRotationResidue`, `rot_wiredRotationResidue` : the rotation residues for lattice
  edges.

## iii. Table of contents

- A. Coordinate permutations
- B. Densities of edges of `ℤ^d` under box symmetries
- C. Recentering by translation
- D. Unit edges at the origin
- E. All lattice edges have the same density
- F. Rotation residues and uniqueness

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.3.
- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, 2017.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}

/-!
## A. Coordinate permutations
-/

/-- The permutation of `ℤ^d` permuting coordinates by `π`: `(x ∘ π⁻¹)_i = x_{π⁻¹ i}`. -/
def rot_permEquiv (d : ℕ) (π : Equiv.Perm (Fin d)) : Site d ≃ Site d where
  toFun := fun x i => x (π.symm i)
  invFun := fun x i => x (π i)
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

@[simp] lemma rot_permEquiv_apply (d : ℕ) (π : Equiv.Perm (Fin d)) (x : Site d) (i : Fin d) :
    rot_permEquiv d π x i = x (π.symm i) := rfl

/-- A coordinate permutation as a box symmetry. -/
def rot_permBoxSym (d : ℕ) (π : Equiv.Perm (Fin d)) : BoxSym d where
  τ := rot_permEquiv d π
  adj := by
    intro x y
    simp only [hypercubicLattice_adj, rot_permEquiv_apply]
    rw [← Equiv.sum_comp π.symm (fun i => (x i - y i).natAbs)]
  box_mem := by
    intro n x
    simp only [mem_box, rot_permEquiv_apply]
    refine ⟨fun h i => ?_, fun h i => h (π.symm i)⟩
    have := h (π i); simpa using this

/-!
## B. Densities of edges of `ℤ^d` under box symmetries
-/
lemma rot_lift_edgeIncl (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) :
    edgeIncl d N (Sym2.map (S.lift N) eb) = Sym2.map S.τ (edgeIncl d N eb) := by
  unfold edgeIncl
  rw [Sym2.map_map, Sym2.map_map]
  apply Sym2.map_congr
  intro z _
  exact BoxSym.lift_val S N z

lemma rot_site_mem_box (x : Site d) :
    x ∈ box d (Finset.univ.sup (fun i => (x i).natAbs)) :=
  fun i => Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

/-- Box symmetries preserve the free `q = 2` density of any edge of `ℤ^d`. -/
lemma rot_free_density_boxSym (S : BoxSym d) (e : Sym2 (Site d))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (Sym2.map S.τ e) p = freeEdgeDensity d 2 e p := by
  induction e with
  | h x y =>
    obtain ⟨N, hxN, hyN⟩ : ∃ N, x ∈ box d N ∧ y ∈ box d N :=
      ⟨max (Finset.univ.sup (fun i => (x i).natAbs))
            (Finset.univ.sup (fun i => (y i).natAbs)),
        fun i => le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _),
        fun i => le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)⟩
    set eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N)) with heb
    have hincl : edgeIncl d N eb = s(x, y) := by
      unfold edgeIncl; rw [heb, Sym2.map_mk]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkTI_free_density_shift_inv S N eb hp hp1).symm

/-- Box symmetries preserve the wired `q = 2` density of any edge of `ℤ^d`. -/
lemma rot_wired_density_boxSym (S : BoxSym d) (e : Sym2 (Site d))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (Sym2.map S.τ e) p = wiredEdgeDensity d 2 e p := by
  induction e with
  | h x y =>
    obtain ⟨N, hxN, hyN⟩ : ∃ N, x ∈ box d N ∧ y ∈ box d N :=
      ⟨max (Finset.univ.sup (fun i => (x i).natAbs))
            (Finset.univ.sup (fun i => (y i).natAbs)),
        fun i => le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _),
        fun i => le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)⟩
    set eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N)) with heb
    have hincl : edgeIncl d N eb = s(x, y) := by
      unfold edgeIncl; rw [heb, Sym2.map_mk]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkTI_wired_density_shift_inv S N eb hp hp1).symm

/-!
## C. Recentering by translation
-/
lemma rot_free_density_recentre (x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  rw [bdp_freeEdgeDensity_translation_inv hp hp1 (Multiplicative.ofAdd x) (s(x, y))]
  congr 1
  change s((Multiplicative.ofAdd x)⁻¹ • x, (Multiplicative.ofAdd x)⁻¹ • y) = s((0 : Site d), y - x)
  have h1 : (Multiplicative.ofAdd x)⁻¹ • x = (0 : Site d) := by
    change -x + x = 0; rw [neg_add_cancel]
  have h2 : (Multiplicative.ofAdd x)⁻¹ • y = y - x := by
    change -x + y = y - x; abel
  rw [h1, h2]

lemma rot_wired_density_recentre (x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  rw [bdp_wiredEdgeDensity_translation_inv hp hp1 (Multiplicative.ofAdd x) (s(x, y))]
  congr 1
  change s((Multiplicative.ofAdd x)⁻¹ • x, (Multiplicative.ofAdd x)⁻¹ • y) = s((0 : Site d), y - x)
  have h1 : (Multiplicative.ofAdd x)⁻¹ • x = (0 : Site d) := by
    change -x + x = 0; rw [neg_add_cancel]
  have h2 : (Multiplicative.ofAdd x)⁻¹ • y = y - x := by
    change -x + y = y - x; abel
  rw [h1, h2]

/-!
## D. Unit edges at the origin
-/
lemma rot_candMap_apply (j : Fin d) (b : Bool) (i : Fin d) :
    candMap d (0 : Site d) (j, b) i = (if i = j then (if b then 1 else -1) else 0) := by
  change Function.update (0 : Site d) j ((0 : Site d) j + (if b then 1 else -1)) i = _
  by_cases h : i = j
  · subst h; rw [Function.update_self]; simp
  · rw [Function.update_of_ne h]; simp [h]

lemma rot_boxSym_fixes_zero (S : BoxSym d) : S.τ (0 : Site d) = 0 := by
  have h0 : S.τ (0 : Site d) ∈ box d 0 := (S.box_mem 0 0).mpr (fun i => by simp)
  funext i
  have hi : (S.τ (0 : Site d) i).natAbs ≤ 0 := h0 i
  have : (S.τ (0 : Site d) i).natAbs = 0 := Nat.le_zero.mp hi
  simpa using Int.natAbs_eq_zero.mp this

lemma rot_signFlip_neg_to_pos (j : Fin d) :
    (fkTI_signFlip d j).τ (candMap d (0 : Site d) (j, false))
      = candMap d (0 : Site d) (j, true) := by
  funext i
  change (if i = j then -(candMap d (0 : Site d) (j, false) i)
      else candMap d (0 : Site d) (j, false) i)
      = candMap d (0 : Site d) (j, true) i
  rw [rot_candMap_apply, rot_candMap_apply]
  by_cases h : i = j <;> simp [h]

lemma rot_permEquiv_axis_to_zero (j : Fin d) (hd : 0 < d) :
    rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true))
      = candMap d (0 : Site d) (⟨0, hd⟩, true) := by
  funext i
  change (candMap d (0 : Site d) (j, true)) ((Equiv.swap (⟨0, hd⟩ : Fin d) j).symm i)
      = candMap d (0 : Site d) (⟨0, hd⟩, true) i
  rw [rot_candMap_apply, rot_candMap_apply, Equiv.symm_swap]
  have hiff : ((Equiv.swap (⟨0, hd⟩ : Fin d) j) i = j) ↔ (i = ⟨0, hd⟩) := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  by_cases h : (Equiv.swap (⟨0, hd⟩ : Fin d) j) i = j
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mpr hc))]

/-- The reference edge `{0, e_0}` of `ℤ^d`. -/
def rot_refUnitEdge (d : ℕ) (hd : 0 < d) : Sym2 (Site d) :=
  s((0 : Site d), candMap d (0 : Site d) (⟨0, hd⟩, true))

lemma rot_map_centred_edge (S : BoxSym d) (w : Site d) :
    Sym2.map S.τ (s((0 : Site d), w) : Sym2 (Site d)) = s((0 : Site d), S.τ w) := by
  rw [Sym2.map_mk, rot_boxSym_fixes_zero S]

/-- Every unit edge `{0, ±e_j}` has the free density of `{0, e_0}`. -/
lemma rot_free_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  have hpos : freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d 2
          (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← rot_free_density_boxSym (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← rot_free_density_boxSym (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1,
      rot_map_centred_edge]
  change freeEdgeDensity d 2 (s((0 : Site d),
        rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl

/-- Every unit edge `{0, ±e_j}` has the wired density of `{0, e_0}`. -/
lemma rot_wired_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  have hpos :
      wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
        = wiredEdgeDensity d 2
          (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← rot_wired_density_boxSym (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← rot_wired_density_boxSym (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1,
      rot_map_centred_edge]
  change wiredEdgeDensity d 2 (s((0 : Site d),
        rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl

/-!
## E. All lattice edges have the same density
-/

/-- The difference of adjacent sites is a signed unit vector. See also `ocs_edge_dir_candMap`,
the same statement for vertices of a box. -/
lemma rot_edge_dir (x y : Site d) (hadj : (hypercubicLattice d).Adj x y) :
    ∃ p : Fin d × Bool, y - x = candMap d (0 : Site d) p := by
  change NearestNeighbour d x y at hadj
  rw [nearestNeighbour_iff_shift] at hadj
  obtain ⟨j, s, hs, hys⟩ := hadj
  refine ⟨(j, decide (s = 1)), ?_⟩
  funext i
  change y i - x i = candMap d (0 : Site d) (j, decide (s = 1)) i
  rw [rot_candMap_apply, hys]
  change (Function.update x j (x j + s)) i - x i = _
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]
    rcases hs with rfl | rfl <;> simp
  · rw [Function.update_of_ne hi]; simp [hi]

/-- Every nearest-neighbour edge of `ℤ^d` has the free `q = 2` density of `{0, e_0}`. -/
lemma rot_free_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [rot_free_density_recentre x y hp hp1, hdir]
  exact rot_free_centred_unit_const hd j b hp hp1

/-- Every nearest-neighbour edge of `ℤ^d` has the wired `q = 2` density of `{0, e_0}`. -/
lemma rot_wired_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [rot_wired_density_recentre x y hp hp1, hdir]
  exact rot_wired_centred_unit_const hd j b hp hp1

lemma rot_free_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d m eb) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    change freeEdgeDensity d 2 (s((u : Site d), (v : Site d)) : Sym2 (Site d)) p = _
    exact rot_free_edge_const hd (u : Site d) (v : Site d) heb hp hp1

lemma rot_wired_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d m eb) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    change wiredEdgeDensity d 2 (s((u : Site d), (v : Site d)) : Sym2 (Site d)) p = _
    exact rot_wired_edge_const hd (u : Site d) (v : Site d) heb hp hp1

/-!
## F. Rotation residues and uniqueness
-/

/-- The free rotation residue holds for every lattice edge `e'` of the box `Λ_N`. -/
lemma rot_freeRotationResidue (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_FreeRotationResidue (d := d) N e' t := by
  intro m eb heb
  rw [rot_free_box_edge_const hd m eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t),
      rot_free_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

/-- The wired rotation residue holds for every lattice edge `e'` of the box `Λ_N`. -/
lemma rot_wiredRotationResidue (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_WiredRotationResidue (d := d) N e' t := by
  intro m eb heb
  rw [rot_wired_box_edge_const hd m eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t),
      rot_wired_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

end FK

end StatMech
