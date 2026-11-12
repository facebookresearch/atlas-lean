/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryInfluenceDecay
/-!
# The off-centre carrier for wired `q = 2` FK marginals

The wired marginal of a box edge on the translated box `v + Λ_{N+k}` equals the centered one, so
the off-centre carrier vanishes identically.

## i. Overview

For a box edge `e ∈ Λ_N` and a shift `v ∈ ℤ^d`, compare the wired FK marginal of `e` in the
centered box `Λ_{N+k}` with the wired marginal of `e + v` in the translated box `v + Λ_{N+k}`.
By translation covariance of the finite-volume measures (`fbd_centred_eq_translated_wired`) the
two are equal for every `k`. Hence the *off-centre carrier* `fbd_offCentreCarrier`, their
difference, is zero, the translated marginals converge to the wired density of `e`, and the
carrier hypothesis of `fbd_wired_density_eq_of_offCentreCarrier` holds unconditionally. The file
also records that the free density is below every translated wired marginal, and that free and
wired densities agree off a countable set of `p` under the secant comparison hypothesis.

## ii. Key results

- `occ_translated_tendsto_wiredDensity` : translated wired marginals converge to the wired
  density.
- `occ_translated_between_iv` : the free density is at most every translated wired marginal.
- `occ_free_eq_wired_off_countable` : free and wired densities agree off a countable set, under
  the secant hypothesis.
- `occ_offCentreCarrier_eq_zero`, `occ_offCentreCarrier` : the off-centre carrier vanishes.
- `occ_wired_density_eq_of_translation_cofinal` : equal wired densities from equality of the
  translated and centered marginals.

## iii. Table of contents

- A. Translated wired marginals
- B. Free and wired densities
- C. The off-centre carrier

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.3 and §5.
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
## A. Translated wired marginals
-/

/-- The wired marginals of the translated edge `e + v` in `v + Λ_{N+k}` converge to the wired
`q = 2` density of `e`. -/
lemma occ_translated_tendsto_wiredDensity (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N + k) v) (fvs_transBoxBoundary d (N + k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N + k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')))
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb') p)) := by
  refine (dfi_wired_density_eq_limit N eb' hp hp1).congr (fun k => ?_)
  exact fbd_centred_eq_translated_wired (N + k) v (innerEdgeLE d (Nat.le_add_right N k) eb')

/-- The free `q = 2` density of `e` is at most the wired marginal of `e + v` in `v + Λ_{N+k}`. -/
lemma occ_translated_between_iv (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    freeEdgeDensity d 2 (edgeIncl d N eb') p
        ≤ edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N + k) v) (fvs_transBoxBoundary d (N + k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N + k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) := by
  rw [← fbd_centred_eq_translated_wired (N + k) v (innerEdgeLE d (Nat.le_add_right N k) eb')]
  calc freeEdgeDensity d 2 (edgeIncl d N eb') p
      ≤ wiredEdgeDensity d 2 (edgeIncl d N eb') p :=
        freeEdgeDensity_q2_le_wiredEdgeDensity d N eb' hp hp1
    _ ≤ edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb') :=
        dfi_wired_per_edge_ge N (N + k) (Nat.le_add_right N k) eb' hp hp1

/-!
## B. Free and wired densities
-/

/-- Under the secant comparison `wired(p') ≤ free(p)` for `p' < p`, the free and wired densities
of a box edge agree for all `p ∈ (0, 1)` outside a countable set, namely the discontinuities of
the monotone wired density. -/
lemma occ_free_eq_wired_off_countable (N : ℕ) (eb' : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ p' ∈ Ioo (0 : ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb') p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb') p) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ p ∈ Ioo (0 : ℝ) 1, p ∉ S →
      freeEdgeDensity d 2 (edgeIncl d N eb') p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  refine ⟨{p : ℝ | p ∈ Ioo (0 : ℝ) 1 ∧
      ¬ ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb')) (Ioo (0 : ℝ) 1) p},
    doc_countable_density_discont d N eb', ?_⟩
  intro p hpmem hpS
  have hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb')) (Ioo (0 : ℝ) 1) p := by
    by_contra hc; exact hpS ⟨hpmem, hc⟩
  exact doc_free_eq_wired_at_continuity d N eb' hsecant hpmem hcont

/-!
## C. The off-centre carrier
-/

/-- The off-centre carrier vanishes for every `k`, by translation covariance of the wired box
measures. -/
lemma occ_offCentreCarrier_eq_zero (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N))
    (p q : ℝ) (k : ℕ) :
    fbd_offCentreCarrier N v eb' p q k = 0 := by
  unfold fbd_offCentreCarrier
  rw [← fbd_centred_eq_translated_wired (N + k) v (innerEdgeLE d (Nat.le_add_right N k) eb'),
    sub_self]

/-- The off-centre carrier tends to zero, for every `p`. -/
lemma occ_offCentreCarrier (N : ℕ) (v : Site d) (eb' : Sym2 (boxVerts d N)) (p : ℝ) :
    Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0) := by
  have hzero : fbd_offCentreCarrier N v eb' p 2 = fun _ => (0 : ℝ) := by
    funext k; exact occ_offCentreCarrier_eq_zero N v eb' p 2 k
  rw [hzero]
  exact tendsto_const_nhds

/-- If for every `k` the wired marginal of `e' + v` in `v + Λ_{N+k}` equals the wired marginal of
`e` in `Λ_{N+k}`, then `e` and `e'` have the same wired density. -/
lemma occ_wired_density_eq_of_translation_cofinal (N : ℕ) (v : Site d)
    (eb eb' : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ k,
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N + k) v) (fvs_transBoxBoundary d (N + k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N + k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))
          = edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p :=
  fbd_wired_density_eq_of_offCentreCarrier N v eb eb' hp hp1
    (occ_offCentreCarrier N v eb' p) htrans

end FK

end StatMech
