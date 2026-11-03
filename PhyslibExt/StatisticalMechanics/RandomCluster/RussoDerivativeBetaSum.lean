/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivativeBeta
/-!
# Inverse-temperature derivative of the random-cluster measure

The derivative in `β` of a random-cluster expectation, when every edge parameter is
`p_e(β) = 1 - exp (-β J_e)`, as a sum of single-edge covariances.

## i. Overview

With couplings `J_e > 0` and edge parameters `betaParams J β e = 1 - exp (-β J_e)` (the
Edwards–Sokal parametrization of the Potts model at inverse temperature `β`), each weight of
the inhomogeneous random-cluster measure is differentiable in `β` with logarithmic derivative
`betaScore G J β ω = ∑_e (J_e / p_e) (𝟙[e open] - p_e)`. Hence (`hasDerivAt_fkMeanW_beta_sum`)

  `d/dβ φ_β[g] = ∑_{e ∈ E(G)} (J_e / p_e(β)) · Cov_{φ_β}(g, 𝟙[e open])`,

and for an event `A` (`hasDerivAt_fkProbWOf_beta_sum`) the same with `g = 𝟙_A`. This is the
sum over edges of the single-edge formula `hasDerivAt_fkProbWOf_beta`.

## ii. Key results

- `StatMech.FK.betaParams` : the edge parameters `1 - exp (-β J_e)`.
- `StatMech.FK.betaScore` : the logarithmic `β`-derivative of the weights.
- `StatMech.FK.hasDerivAt_fkMeanW_beta_sum` : the `β`-derivative of an expectation.
- `StatMech.FK.hasDerivAt_fkProbWOf_beta_sum` : the `β`-derivative of an event probability.

## iii. Table of contents

- A. Edge parameters as functions of `β`
- B. Derivatives of weights and numerators
- C. Linearity of the covariance
- D. The `β`-derivative formula

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 3.

-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixes the `Fintype (Sym2 V)` instance to `Sym2.instFintype`, so that `G.edgeFinset` below
elaborates to the same term as in the single-edge file. -/
local instance canonicalSym2Fintype : Fintype (Sym2 V) := Sym2.instFintype

/-- The `Fintype G.edgeSet` instance built from `Sym2.instFintype`. -/
local instance canonicalEdgeFintype (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype G.edgeSet :=
  @SimpleGraph.fintypeEdgeSet V G Sym2.instFintype inferInstance

/-!

## A. Edge parameters as functions of `β`

-/

/-- The edge parameters `p_e(β) = 1 - exp (-β J_e)`. -/
noncomputable def betaParams (J : Sym2 V → ℝ) (β : ℝ) : Sym2 V → ℝ :=
  fun e => 1 - Real.exp (-(β * J e))

/-- The logarithmic `β`-derivative of the random-cluster weight under `betaParams`:
`∑_{e ∈ E(G)} (J_e / p_e) (𝟙[e open] - p_e)`. -/
noncomputable def betaScore (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (β : ℝ)
    (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ e ∈ G.edgeFinset,
    (J e / betaParams J β e) * (coord e ω - betaParams J β e)

omit [Fintype V] [DecidableEq V] in
lemma betaParams_pos {J : Sym2 V → ℝ} (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β)
    (e : Sym2 V) : 0 < betaParams J β e := by
  unfold betaParams
  have hβJ : 0 < β * J e := mul_pos hβ (hJ e)
  have hexp : Real.exp (-(β * J e)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβJ)
  linarith

omit [Fintype V] [DecidableEq V] in
lemma betaParams_lt_one (J : Sym2 V → ℝ) (β : ℝ) (e : Sym2 V) :
    betaParams J β e < 1 := by
  unfold betaParams
  have := Real.exp_pos (-(β * J e))
  linarith

omit [Fintype V] [DecidableEq V] in
lemma hasDerivAt_betaFactor (J : Sym2 V → ℝ) (ω : ConfigSpace (Sym2 V))
    (e : Sym2 V) (β : ℝ) :
    HasDerivAt
      (fun b => if ω e then betaParams J b e else 1 - betaParams J b e)
      (if ω e then J e * Real.exp (-(β * J e))
        else -(J e * Real.exp (-(β * J e)))) β := by
  have hp := hasDerivAt_paramOfBeta (J e) β
  by_cases hω : ω e
  · simp only [hω, ite_true]
    simpa [betaParams] using hp
  · simp only [hω]
    convert hp.const_sub (1 : ℝ) using 1 <;> simp [betaParams]

omit [Fintype V] [DecidableEq V] in
lemma betaFactor_deriv_eq_mul_score {J : Sym2 V → ℝ} (hJ : ∀ e, 0 < J e)
    {β : ℝ} (hβ : 0 < β) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    (if ω e then J e * Real.exp (-(β * J e))
      else -(J e * Real.exp (-(β * J e))))
      = (if ω e then betaParams J β e else 1 - betaParams J β e)
        * ((J e / betaParams J β e) * (coord e ω - betaParams J β e)) := by
  have hp : betaParams J β e ≠ 0 := (betaParams_pos hJ hβ e).ne'
  have hone : 1 - betaParams J β e = Real.exp (-(β * J e)) := by
    simp [betaParams]
  cases hω : ω e <;> simp [hω, coord, hone] <;> field_simp

/-!

## B. Derivatives of weights and numerators

-/

omit [DecidableEq V] in
lemma hasDerivAt_edgeProductW_beta (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun b => edgeProductW G (betaParams J b) ω)
      (edgeProductW G (betaParams J β) ω * betaScore G J β ω) β := by
  classical
  have hprod := HasDerivAt.fun_finsetProd
    (u := G.edgeFinset)
    (f := fun e b => if ω e then betaParams J b e else 1 - betaParams J b e)
    (f' := fun e => if ω e then J e * Real.exp (-(β * J e))
      else -(J e * Real.exp (-(β * J e))))
    (x := β) (fun e _ => hasDerivAt_betaFactor J ω e β)
  unfold edgeProductW betaScore
  refine hprod.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr (M := ℝ) (s₁ := G.edgeFinset) (s₂ := G.edgeFinset) rfl ?_
  intro e he
  simp only [smul_eq_mul]
  rw [betaFactor_deriv_eq_mul_score hJ hβ]
  rw [← mul_assoc, Finset.prod_erase_mul _ _ he]

lemma hasDerivAt_fkWeightW_beta (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (q : ℝ)
    (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun b => fkWeightW G (betaParams J b) q ω)
      (fkWeightW G (betaParams J β) q ω * betaScore G J β ω) β := by
  have h := (hasDerivAt_edgeProductW_beta G hJ hβ ω).mul_const
    (q ^ numClusters G ω)
  refine h.congr_deriv ?_
  unfold fkWeightW
  ring

lemma hasDerivAt_fkNumerW_beta (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (q : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun b => fkNumerW G (betaParams J b) q g)
      (fkNumerW G (betaParams J β) q (fun ω => g ω * betaScore G J β ω)) β := by
  unfold fkNumerW
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun ω _ => (hasDerivAt_fkWeightW_beta G hJ hβ q ω).const_mul (g ω))
  refine hsum.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-!

## C. Linearity of the covariance

-/

lemma fkCovW_zero_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    fkCovW G pf q g (fun _ => 0) = 0 := by
  have hzero : fkMeanW G pf q (fun _ : ConfigSpace (Sym2 V) => (0 : ℝ)) = 0 := by
    simpa using fkMeanW_const_mul G pf q 0 (fun _ => (1 : ℝ))
  have hprodzero : fkMeanW G pf q (fun ω => g ω * 0) = 0 := by
    simpa only [mul_zero] using hzero
  unfold fkCovW
  rw [hzero, hprodzero]
  ring

lemma fkCovW_add_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ)
    (g h k : ConfigSpace (Sym2 V) → ℝ) :
    fkCovW G pf q g (fun ω => h ω + k ω) =
      fkCovW G pf q g h + fkCovW G pf q g k := by
  unfold fkCovW
  rw [fkMeanW_add]
  have hprod : (fun ω => g ω * (h ω + k ω)) =
      (fun ω => g ω * h ω + g ω * k ω) := by funext ω; ring
  rw [hprod, fkMeanW_add]
  ring

lemma fkCovW_const_mul_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q c : ℝ)
    (g h : ConfigSpace (Sym2 V) → ℝ) :
    fkCovW G pf q g (fun ω => c * h ω) = c * fkCovW G pf q g h := by
  unfold fkCovW
  rw [fkMeanW_const_mul]
  have hprod : (fun ω => g ω * (c * h ω)) =
      (fun ω => c * (g ω * h ω)) := by funext ω; ring
  rw [hprod, fkMeanW_const_mul]
  ring

lemma fkCovW_finset_sum_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) {ι : Type*} (s : Finset ι)
    (h : ι → ConfigSpace (Sym2 V) → ℝ) :
    fkCovW G pf q g (fun ω => ∑ i ∈ s, h i ω) =
      ∑ i ∈ s, fkCovW G pf q g (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using fkCovW_zero_right G pf q g
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [fkCovW_add_right, ih]

lemma fkCovW_betaScore (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) {q : ℝ} (hq : 0 < q)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    fkCovW G (betaParams J β) q g (betaScore G J β) =
      ∑ e ∈ G.edgeFinset,
        (J e / betaParams J β e) * fkCovW G (betaParams J β) q g (coord e) := by
  have hZ : fkZW G (betaParams J β) q ≠ 0 :=
    fkZW_ne_zero G (betaParams_pos hJ hβ) (betaParams_lt_one J β) hq
  unfold betaScore
  rw [fkCovW_finset_sum_right]
  refine Finset.sum_congr (M := ℝ) (s₁ := G.edgeFinset) (s₂ := G.edgeFinset) rfl ?_
  intro e _
  rw [fkCovW_const_mul_right]
  exact congrArg (fun x => (J e / betaParams J β e) * x)
    (fkCovW_sub_const G (betaParams J β) q g (coord e) hZ)

/-!

## D. The `β`-derivative formula

-/

/-- **Differential formula in `β`** for the random-cluster measure with edge parameters
`1 - exp (-β J_e)`: `d/dβ φ_β[g] = ∑_e (J_e / p_e) Cov(g, 𝟙[e open])`. See G. Grimmett,
*The Random-Cluster Model* (2006), Chapter 3. -/
theorem hasDerivAt_fkMeanW_beta_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) {q : ℝ} (hq : 0 < q)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun b => fkMeanW G (betaParams J b) q g)
      (∑ e ∈ G.edgeFinset,
        (J e / betaParams J β e) * fkCovW G (betaParams J β) q g (coord e)) β := by
  have hN := hasDerivAt_fkNumerW_beta G hJ hβ q g
  have hZraw := hasDerivAt_fkNumerW_beta G hJ hβ q (fun _ => 1)
  have hZ : HasDerivAt (fun b => fkZW G (betaParams J b) q)
      (fkNumerW G (betaParams J β) q (betaScore G J β)) β := by
    have hfun : (fun b => fkNumerW G (betaParams J b) q (fun _ => 1)) =
        (fun b => fkZW G (betaParams J b) q) := by
      funext b; exact fkNumerW_one G (betaParams J b) q
    rw [hfun] at hZraw
    refine hZraw.congr_deriv ?_
    unfold fkNumerW
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hZne : fkZW G (betaParams J β) q ≠ 0 :=
    fkZW_ne_zero G (betaParams_pos hJ hβ) (betaParams_lt_one J β) hq
  have hdiv := hN.div hZ hZne
  have hfun : (fun b => fkMeanW G (betaParams J b) q g) =
      (fun b => fkNumerW G (betaParams J b) q g / fkZW G (betaParams J b) q) := by
    funext b; exact fkMeanW_eq_div G (betaParams J b) q g
  rw [hfun]
  refine hdiv.congr_deriv ?_
  rw [← fkCovW_betaScore G hJ hβ hq g]
  unfold fkCovW
  rw [fkMeanW_eq_div, fkMeanW_eq_div, fkMeanW_eq_div]
  field_simp

lemma hasDerivAt_fkProbWOf_beta_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) {q : ℝ} (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    HasDerivAt (fun b => fkProbWOf G (betaParams J b) q A)
      (∑ e ∈ G.edgeFinset, (J e / (1 - Real.exp (-(β * J e))))
        * fkCovW G (betaParams J β) q (A.indicator (fun _ => (1 : ℝ))) (coord e)) β := by
  simpa [fkProbWOf, betaParams] using
    hasDerivAt_fkMeanW_beta_sum G hJ hβ hq (A.indicator (fun _ => (1 : ℝ)))

end FK
end StatMech
