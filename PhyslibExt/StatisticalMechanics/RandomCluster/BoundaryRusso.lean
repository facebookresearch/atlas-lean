/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC
public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivative

/-!
# Russo formula for the boundary-conditioned random-cluster measure

For the random-cluster measure on `G` with boundary wiring `C`, the `p`-derivative of an event
probability is `(p(1 - p))⁻¹ ∑_{e ∈ E(G)} Cov(𝟙_A, ω_e)`.

## i. Overview

The boundary-conditioned weight is the Bernoulli edge product times `q^{k_C(ω)}`, and only the edge
product depends on `p`; its logarithmic derivative is `∑_e (ω_e - p) / (p(1 - p))`. Differentiating
the numerator and partition function and using the quotient rule writes the derivative of any
expectation as a covariance with the centered edge count, which splits into covariances with the
individual edge indicators.

Both key results are proved unconditionally, under only `0 < p < 1` and `0 < q`.

## ii. Key results

- `hasDerivAt_bcMean` : the `p`-derivative of a boundary-conditioned expectation is a sum of edge
  covariances.
- `hasDerivAt_bcProbOf` : Russo's formula for the `p`-derivative of an event probability.

## iii. Table of contents

- A. Expectations and covariances
- B. Derivatives and covariance identities

## iv. References

- L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.12.
-/

@[expose] public section

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (C : SimpleGraph V) [DecidableRel C.Adj]

/-! ## A. Expectations and covariances -/

/-- The expectation of `g` under the boundary-conditioned random-cluster measure. -/
noncomputable def bcMean (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, g ω * bcProb G C p q ω

/-- The covariance of `f` and `g` under the boundary-conditioned random-cluster measure. -/
noncomputable def bcCov (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  bcMean G C p q (fun ω => f ω * g ω) - bcMean G C p q f * bcMean G C p q g

/-- The unnormalized expectation `∑ ω, g ω * w_C(ω)` for the boundary-conditioned weight. -/
noncomputable def bcNumer (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, g ω * bcWeight G C p q ω

/-- The probability of the event `A` under the boundary-conditioned random-cluster measure. -/
noncomputable def bcProbOf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  bcMean G C p q (A.indicator fun _ => (1 : ℝ))

/-! ## B. Derivatives and covariance identities -/

lemma hasDerivAt_bcWeight {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (q : ℝ)
    (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun p => bcWeight G C p q ω)
      (bcWeight G C p q ω
        * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
  have h := (hasDerivAt_edgeProduct_clean G hp hp1 ω).mul_const
    (q ^ numClustersBC G C ω)
  refine h.congr_deriv ?_
  unfold bcWeight
  ring

lemma hasDerivAt_bcNumer {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (q : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun p => bcNumer G C p q g)
      ((∑ ω, g ω * (bcWeight G C p q ω
        * ∑ e ∈ G.edgeFinset, (coord e ω - p))) / (p * (1 - p))) p := by
  unfold bcNumer
  have hsum : HasDerivAt
      (fun p => ∑ ω, g ω * bcWeight G C p q ω)
      (∑ ω, g ω * (bcWeight G C p q ω
        * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p))))) p := by
    apply HasDerivAt.fun_sum
    intro ω _
    exact (hasDerivAt_bcWeight G C hp hp1 q ω).const_mul (g ω)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [mul_div_assoc, mul_div_assoc]

lemma bcNumer_one (p q : ℝ) : bcNumer G C p q (fun _ => 1) = bcZ G C p q := by
  unfold bcNumer bcZ
  exact Finset.sum_congr rfl fun ω _ => by rw [one_mul]

lemma bcMean_eq_div (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    bcMean G C p q g = bcNumer G C p q g / bcZ G C p q := by
  unfold bcMean bcNumer bcProb
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun ω _ => by rw [mul_div_assoc]

lemma bcMean_add (p q : ℝ) (g h : ConfigSpace (Sym2 V) → ℝ) :
    bcMean G C p q (fun ω => g ω + h ω) =
      bcMean G C p q g + bcMean G C p q h := by
  unfold bcMean
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma bcMean_sum (p q : ℝ) {ι : Type*} (s : Finset ι)
    (g : ι → ConfigSpace (Sym2 V) → ℝ) :
    bcMean G C p q (fun ω => ∑ i ∈ s, g i ω) =
      ∑ i ∈ s, bcMean G C p q (g i) := by
  unfold bcMean
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_mul]

lemma bcMean_const (p q : ℝ) {c : ℝ} (hZ : bcZ G C p q ≠ 0) :
    bcMean G C p q (fun _ => c) = c := by
  unfold bcMean bcProb
  rw [Finset.sum_congr rfl (fun ω _ => by
      change c * (bcWeight G C p q ω / bcZ G C p q) =
        (c * bcWeight G C p q ω) / bcZ G C p q
      exact (mul_div_assoc c _ _).symm),
    ← Finset.sum_div, ← Finset.mul_sum]
  change (c * bcZ G C p q) / bcZ G C p q = c
  rw [mul_div_assoc, div_self hZ, mul_one]

lemma bcMean_const_mul (p q c : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    bcMean G C p q (fun ω => c * g ω) = c * bcMean G C p q g := by
  unfold bcMean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma bcCov_sum_right (p q : ℝ) {ι : Type*} (s : Finset ι)
    (f : ConfigSpace (Sym2 V) → ℝ) (g : ι → ConfigSpace (Sym2 V) → ℝ) :
    bcCov G C p q f (fun ω => ∑ i ∈ s, g i ω) =
      ∑ i ∈ s, bcCov G C p q f (g i) := by
  unfold bcCov
  have hprod : bcMean G C p q (fun ω => f ω * ∑ i ∈ s, g i ω) =
      ∑ i ∈ s, bcMean G C p q (fun ω => f ω * g i ω) := by
    have heq : (fun ω => f ω * ∑ i ∈ s, g i ω) =
        (fun ω => ∑ i ∈ s, (fun i ω => f ω * g i ω) i ω) := by
      funext ω
      rw [Finset.mul_sum]
    rw [heq, bcMean_sum G C p q s]
  rw [hprod, bcMean_sum G C p q s, Finset.mul_sum, ← Finset.sum_sub_distrib]

lemma bcCov_sub_const (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) {c : ℝ}
    (hZ : bcZ G C p q ≠ 0) :
    bcCov G C p q f (fun ω => g ω - c) = bcCov G C p q f g := by
  unfold bcCov
  have hprod : bcMean G C p q (fun ω => f ω * (g ω - c)) =
      bcMean G C p q (fun ω => f ω * g ω) - c * bcMean G C p q f := by
    have heq : (fun ω => f ω * (g ω - c)) =
        (fun ω => f ω * g ω + (-c) * f ω) := by funext ω; ring
    rw [heq, bcMean_add, bcMean_const_mul]
    ring
  have hgc : bcMean G C p q (fun ω => g ω - c) = bcMean G C p q g - c := by
    have heq : (fun ω => g ω - c) = (fun ω => g ω + (fun _ => -c) ω) := by
      funext ω
      ring
    rw [heq, bcMean_add, bcMean_const G C p q hZ]
    ring
  rw [hprod, hgc]
  ring

lemma bcCov_centeredCount (p q : ℝ) (hZ : bcZ G C p q ≠ 0)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    bcCov G C p q g (fun ω => ∑ e ∈ G.edgeFinset, (coord e ω - p)) =
      ∑ e ∈ G.edgeFinset, bcCov G C p q g (coord e) := by
  rw [bcCov_sum_right G C p q G.edgeFinset]
  exact Finset.sum_congr rfl fun e _ => bcCov_sub_const G C p q g (coord e) hZ

/-- The `p`-derivative of the boundary-conditioned expectation of `g` is `(p(1 - p))⁻¹ ∑_{e ∈ E(G)}
Cov(g, ω_e)`. -/
theorem hasDerivAt_bcMean {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℝ} (hq : 0 < q) (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun p => bcMean G C p q g)
      ((∑ e ∈ G.edgeFinset, bcCov G C p q g (coord e)) / (p * (1 - p))) p := by
  have hppos : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hpne : p * (1 - p) ≠ 0 := hppos.ne'
  have hZpos : 0 < bcZ G C p q := bcZ_pos G C hp hp1 hq
  have hZne : bcZ G C p q ≠ 0 := hZpos.ne'
  let K : ConfigSpace (Sym2 V) → ℝ :=
    fun ω => ∑ e ∈ G.edgeFinset, (coord e ω - p)
  have hN : HasDerivAt (fun p => bcNumer G C p q g)
      (bcNumer G C p q (fun ω => g ω * K ω) / (p * (1 - p))) p := by
    refine (hasDerivAt_bcNumer G C hp hp1 q g).congr_deriv ?_
    congr 1
    unfold bcNumer
    exact Finset.sum_congr rfl fun ω _ => by simp only [K]; ring
  have hZd : HasDerivAt (fun p => bcZ G C p q)
      (bcNumer G C p q K / (p * (1 - p))) p := by
    have h := hasDerivAt_bcNumer G C hp hp1 q (fun _ => 1)
    have hfun : (fun p => bcNumer G C p q (fun _ => 1)) =
        (fun p => bcZ G C p q) := by
      funext x
      exact bcNumer_one G C x q
    rw [hfun] at h
    refine h.congr_deriv ?_
    congr 1
    unfold bcNumer
    exact Finset.sum_congr rfl fun ω _ => by simp only [K]; ring
  have hdiv := HasDerivAt.div hN hZd hZne
  have hfun : (fun p => bcMean G C p q g) =
      (fun p => bcNumer G C p q g) / (fun p => bcZ G C p q) := by
    funext x
    exact bcMean_eq_div G C x q g
  rw [hfun]
  refine hdiv.congr_deriv ?_
  have hgK := bcMean_eq_div G C p q (fun ω => g ω * K ω)
  have hK := bcMean_eq_div G C p q K
  have hg := bcMean_eq_div G C p q g
  have hcov : bcCov G C p q g K =
      (bcNumer G C p q (fun ω => g ω * K ω) * bcZ G C p q
        - bcNumer G C p q g * bcNumer G C p q K) / (bcZ G C p q) ^ 2 := by
    unfold bcCov
    rw [hgK, hK, hg]
    field_simp
  rw [← bcCov_centeredCount G C p q hZne g]
  change
    (bcNumer G C p q (fun ω => g ω * K ω) / (p * (1 - p)) * bcZ G C p q
      - bcNumer G C p q g * (bcNumer G C p q K / (p * (1 - p))))
        / bcZ G C p q ^ 2 = bcCov G C p q g K / (p * (1 - p))
  rw [hcov]
  field_simp

/-- Russo's formula: the `p`-derivative of `P(A)` is `(p(1 - p))⁻¹ ∑_{e ∈ E(G)} Cov(𝟙_A, ω_e)`. -/
theorem hasDerivAt_bcProbOf {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {q : ℝ} (hq : 0 < q) (A : Set (ConfigSpace (Sym2 V))) :
    HasDerivAt (fun p => bcProbOf G C p q A)
      ((∑ e ∈ G.edgeFinset,
        bcCov G C p q (A.indicator fun _ => (1 : ℝ)) (coord e)) / (p * (1 - p))) p :=
  hasDerivAt_bcMean G C hp hp1 hq _

end StatMech.FK
