/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvariance
/-!
# Translations and orbit constancy of `q = 2` FK edge densities

Translations of `ℤ^d`, boxes containing an edge and its translate, and reductions of
translation invariance of the `q = 2` edge densities to decay of finite-volume marginals.

## i. Overview

The free and wired `q = 2` infinite-volume edge densities `φ^0_p(e open)` and `φ^1_p(e open)` are
limits of edge marginals on the centered boxes `Λ_n = [-n, n]^d`. A translation `x ↦ x + v` is
a graph automorphism of `ℤ^d` but does not preserve the boxes, so box symmetry arguments do not
apply to it directly. This file records:

- for a box symmetry `S`, the edge density is constant on each orbit of `S`, and box averages
  of the open-edge count over an orbit compare with the density of one orbit representative;
- if the difference of the finite-volume marginals of two box edges tends to zero along the
  boxes, the two edges have the same infinite-volume density; in particular an edge and its
  translate have the same density when their marginals merge in this sense.

The decay hypotheses are discharged elsewhere: the unconditional statements are
`bdp_freeEdgeDensity_translation_inv` and `bdp_wiredEdgeDensity_translation_inv`.

## ii. Key results

- `fktc_translate` : translation by `v` as a permutation of `ℤ^d`.
- `fktc_edge_and_translate_in_box` : an edge and its translate lie in a common box.
- `fktc_wired_box_density_const_of_orbit` : edge densities are constant on orbits of a box
  symmetry.
- `fktc_wired_density_eq_of_marg_decay` : merging finite-volume marginals give equal densities.
- `fktc_density_translation_inv` : translation invariance of both densities under the merging
  hypothesis.
- `fktc_wired_density_eq_const_orbit` : box averages of the open-edge count against the
  density of an orbit representative.

## iii. Table of contents

- A. Translations of `ℤ^d`
- B. Constancy along orbits of box symmetries
- C. Equal densities from merging marginals
- D. Box averages over orbits

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.3.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}

/-!
## A. Translations of `ℤ^d`
-/

/-- Translation `x ↦ x + v` as a permutation of `ℤ^d`. -/
def fktc_translate (v : Site d) : Site d ≃ Site d where
  toFun := fun x => x + v
  invFun := fun x => x - v
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

@[simp] lemma fktc_translate_apply (v x : Site d) : fktc_translate v x = x + v := rfl

lemma fktc_translate_adj (v : Site d) (x y : Site d) :
    (hypercubicLattice d).Adj (fktc_translate v x) (fktc_translate v y)
      ↔ (hypercubicLattice d).Adj x y := by
  simp only [hypercubicLattice_adj, fktc_translate_apply]
  have hcoord : ∀ i : Fin d, ((x + v) i - (y + v) i).natAbs = (x i - y i).natAbs := by
    intro i
    have : (x + v) i - (y + v) i = x i - y i := by
      simp only [Pi.add_apply]; ring
    rw [this]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]

/-- Translation by a unit vector does not preserve the centered boxes, so it is not a `BoxSym`. -/
lemma fktc_translate_not_box_mem (j : Fin d) :
    ¬ (∀ n x, fktc_translate (fun i => if i = j then (1:ℤ) else 0) x ∈ box d n
        ↔ x ∈ box d n) := by
  intro h
  have hbase : (fun _ : Fin d => (0:ℤ)) ∈ box d 0 := by
    intro i; simp
  have := (h 0 (fun _ => 0)).mpr hbase
  rw [mem_box] at this
  have hj := this j
  simp only [fktc_translate_apply, Pi.add_apply] at hj
  norm_num at hj

/-- A site and its translate lie in a common centered box. -/
lemma fktc_point_and_translate_in_box (v x : Site d) :
    ∃ N, x ∈ box d N ∧ fktc_translate v x ∈ box d N := by
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs ⊔ ((x + v) i).natAbs), ?_, ?_⟩
  · intro i
    refine le_trans le_sup_left
      (Finset.le_sup (f := fun i => (x i).natAbs ⊔ ((x + v) i).natAbs) (Finset.mem_univ i))
  · intro i
    change ((x + v) i).natAbs ≤ _
    refine le_trans le_sup_right
      (Finset.le_sup (f := fun i => (x i).natAbs ⊔ ((x + v) i).natAbs) (Finset.mem_univ i))

/-- The endpoints of an edge and of its translate lie in a common centered box. -/
lemma fktc_edge_and_translate_in_box (v x y : Site d) :
    ∃ N, x ∈ box d N ∧ y ∈ box d N ∧
      fktc_translate v x ∈ box d N ∧ fktc_translate v y ∈ box d N := by
  refine ⟨Finset.univ.sup
      (fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs),
    ?_, ?_, ?_, ?_⟩
  · intro i
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_trans le_sup_left (le_trans le_sup_left le_sup_left)
  · intro i
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_trans le_sup_right (le_trans le_sup_left le_sup_left)
  · intro i
    change ((x + v) i).natAbs ≤ _
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_trans le_sup_right le_sup_left
  · intro i
    change ((y + v) i).natAbs ≤ _
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_sup_right

/-- The pair `{x, y}` as an element of `Sym2 Λ_N`, for sites `x, y ∈ Λ_N`. -/
def fktc_boxEdge {N : ℕ} {x y : Site d} (hx : x ∈ box d N) (hy : y ∈ box d N) :
    Sym2 (boxVerts d N) :=
  s(⟨x, hx⟩, ⟨y, hy⟩)

lemma fktc_edgeIncl_boxEdge {N : ℕ} {x y : Site d} (hx : x ∈ box d N) (hy : y ∈ box d N) :
    edgeIncl d N (fktc_boxEdge hx hy) = s(x, y) := by
  unfold edgeIncl fktc_boxEdge
  rw [Sym2.map_mk]

/-!
## B. Constancy along orbits of box symmetries
-/

/-- The wired edge density is constant on each orbit of a box symmetry. -/
lemma fktc_wired_box_density_const_of_orbit (S : BoxSym d) (N : ℕ)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    ∀ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hstep : ∀ k : ℕ, wiredEdgeDensity d 2 (edgeIncl d N ((Sym2.map (S.lift N))^[k] eb₀)) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply,
          ← fkTI_wired_density_shift_inv S N ((Sym2.map (S.lift N))^[k] eb₀) hp hp1, ih]
  intro eb heb
  obtain ⟨k, hk⟩ := horb eb heb
  rw [hk, hstep k]

/-- The free edge density is constant on each orbit of a box symmetry. -/
lemma fktc_free_box_density_const_of_orbit (S : BoxSym d) (N : ℕ)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    ∀ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hstep : ∀ k : ℕ, freeEdgeDensity d 2 (edgeIncl d N ((Sym2.map (S.lift N))^[k] eb₀)) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply,
          ← fkTI_free_density_shift_inv S N ((Sym2.map (S.lift N))^[k] eb₀) hp hp1, ih]
  intro eb heb
  obtain ⟨k, hk⟩ := horb eb heb
  rw [hk, hstep k]

/-!
## C. Equal densities from merging marginals
-/

/-- If the wired marginals of two box edges on `Λ_{N+k}` differ by a quantity tending to zero,
the two edges have the same wired density. -/
lemma fktc_wired_density_eq_of_marg_decay (N : ℕ) (eb eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdecay : Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  have hlim : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      - wiredEdgeDensity d 2 (edgeIncl d N eb') p = 0 := by
    refine tendsto_nhds_unique
      ((dfi_wired_density_eq_limit N eb hp hp1).sub (dfi_wired_density_eq_limit N eb' hp hp1))
      hdecay
  linarith [hlim]

/-- If the free marginals of two box edges on `Λ_{N+k}` differ by a quantity tending to zero, the
two edges have the same free density. -/
lemma fktc_free_density_eq_of_marg_decay (N : ℕ) (eb eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdecay : Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb') p := by
  have hlim : freeEdgeDensity d 2 (edgeIncl d N eb) p
      - freeEdgeDensity d 2 (edgeIncl d N eb') p = 0 := by
    refine tendsto_nhds_unique
      ((dfi_free_density_eq_limit N eb hp hp1).sub (dfi_free_density_eq_limit N eb' hp hp1))
      hdecay
  linarith [hlim]

/-- An edge and its translate have the same wired density if their wired marginals merge along
the boxes. See also `bdp_wiredEdgeDensity_translation_inv`, which proves the conclusion without
the merging hypothesis. -/
lemma fktc_wired_density_translation_inv (v x y : Site d) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hcof : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 s(x, y) p
      = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
  obtain ⟨N, hx, hy, hx', hy', hdecay⟩ := hcof
  have h1 : s(x, y) = edgeIncl d N (fktc_boxEdge hx hy) := (fktc_edgeIncl_boxEdge hx hy).symm
  have h2 : s(fktc_translate v x, fktc_translate v y)
      = edgeIncl d N (fktc_boxEdge hx' hy') := (fktc_edgeIncl_boxEdge hx' hy').symm
  rw [h1, h2]
  exact fktc_wired_density_eq_of_marg_decay N (fktc_boxEdge hx hy) (fktc_boxEdge hx' hy')
    hp hp1 hdecay

/-- An edge and its translate have the same free density if their free marginals merge along the
boxes. See also `bdp_freeEdgeDensity_translation_inv`, which proves the conclusion without the
merging hypothesis. -/
lemma fktc_free_density_translation_inv (v x y : Site d) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hcof : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    freeEdgeDensity d 2 s(x, y) p
      = freeEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
  obtain ⟨N, hx, hy, hx', hy', hdecay⟩ := hcof
  have h1 : s(x, y) = edgeIncl d N (fktc_boxEdge hx hy) := (fktc_edgeIncl_boxEdge hx hy).symm
  have h2 : s(fktc_translate v x, fktc_translate v y)
      = edgeIncl d N (fktc_boxEdge hx' hy') := (fktc_edgeIncl_boxEdge hx' hy').symm
  rw [h1, h2]
  exact fktc_free_density_eq_of_marg_decay N (fktc_boxEdge hx hy) (fktc_boxEdge hx' hy')
    hp hp1 hdecay

/-- Translation invariance of the free and wired densities of an edge under the merging
hypotheses of `fktc_wired_density_translation_inv` and `fktc_free_density_translation_inv`. -/
lemma fktc_density_translation_inv (v x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcofW : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0))
    (hcofF : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 s(x, y) p
        = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p
      ∧ freeEdgeDensity d 2 s(x, y) p
        = freeEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p :=
  ⟨fktc_wired_density_translation_inv v x y hp hp1 hcofW,
    fktc_free_density_translation_inv v x y hp hp1 hcofF⟩

/-!
## D. Box averages over orbits
-/

/-- If the wired density is constant on a set `EB` of box edges, `|EB|` times that density is at
most the expected number of open edges of `EB` under the wired measure on any larger box. -/
lemma fktc_wired_density_eq_const (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  have hsum : (∑ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_wired N n hNn EB hp hp1

/-- If the free density is constant on a set `EB` of box edges, the expected number of open edges
of `EB` under the free measure on any larger box is at most `|EB|` times that density. -/
lemma fktc_free_density_eq_const (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hsum : (∑ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_free N n hNn EB hp hp1

/-- `fktc_wired_density_eq_const` for a set of edges contained in one orbit of a box symmetry. -/
lemma fktc_wired_density_eq_const_orbit (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω :=
  fktc_wired_density_eq_const N n hNn EB eb₀
    (fktc_wired_box_density_const_of_orbit S N EB eb₀ hp hp1 horb) hp hp1

/-- `fktc_free_density_eq_const` for a set of edges contained in one orbit of a box symmetry. -/
lemma fktc_free_density_eq_const_orbit (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p :=
  fktc_free_density_eq_const N n hNn EB eb₀
    (fktc_free_box_density_const_of_orbit S N EB eb₀ hp hp1 horb) hp hp1

end FK

end StatMech
