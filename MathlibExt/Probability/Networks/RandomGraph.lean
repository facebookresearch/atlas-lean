/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Random graphs: exponential families and block models

Exponential-family random graph laws on `SimpleGraph V` for fixed
finite `V`: normalized `PMF`, score and covariance derivatives,
identifiability iff. Stochastic block model: latent labelings,
admissible parameters giving a `PMF`, label swapping leaves the law
unchanged (Allman, Matias and Rhodes 2009, Section 2).

## References

* T. A. B. Snijders, *Markov chain Monte Carlo estimation of exponential random graph models*,
  Journal of Social Structure 3 (2002),
  <https://www.cmu.edu/joss/content/articles/volume3/Snijders.pdf>. Its sufficient statistic `u`
  and log-normalizer `ψ` are `t` and `Real.log (ergmNormalizer t θ)` here. Equation (3) is the
  exponential random graph law. Section 6 gives the moment equation `µ(θ) = u(y)` (eq. (24)),
  the mean as the gradient of `ψ` (eq. (25)) and the covariance as the matrix of derivatives of
  the mean (eq. (26)). Section 4.1 notes that when the number of ties is fixed, the edge
  statistic and its parameter are irrelevant.
* E. S. Allman, C. Matias and J. A. Rhodes, *Identifiability of parameters in latent structure
  models with many observed variables*, Annals of Statistics 37(6A) (2009), 3099–3132,
  <https://arxiv.org/abs/0809.5032>. Section 2 describes label swapping: relabeling the latent
  classes leaves the distribution of the observations unchanged.
-/

open scoped Matrix

namespace MathlibExt.Probability.Networks

@[expose] public section

/-- Normalizing constant `κ(θ)`, i.e. `e^ψ(θ)`. -/
noncomputable def ergmNormalizer {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) : ℝ :=
  ∑ G, Real.exp (θ ⬝ᵥ t G)

/-- The normalizer is strictly positive. -/
theorem ergmNormalizer_pos {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) : 0 < ergmNormalizer t θ := by
  unfold ergmNormalizer
  apply Finset.sum_pos
  · intro G _
    exact Real.exp_pos _
  · exact ⟨⊥, Finset.mem_univ _⟩

/-- Exponential-family random graph law. -/
noncomputable def ergmProb {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (G : SimpleGraph V) : ℝ :=
  Real.exp (θ ⬝ᵥ t G) / ergmNormalizer t θ

/-- Each probability value is strictly positive. -/
theorem ergmProb_pos {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (G : SimpleGraph V) :
    0 < ergmProb t θ G := by
  unfold ergmProb
  exact div_pos (Real.exp_pos _) (ergmNormalizer_pos t θ)

/-- The probabilities sum to one. -/
theorem sum_ergmProb {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) : ∑ G, ergmProb t θ G = 1 := by
  simp only [ergmProb, ← Finset.sum_div]
  have h : (∑ G, Real.exp (θ ⬝ᵥ t G)) = ergmNormalizer t θ := rfl
  rw [h]
  exact div_self (ne_of_gt (ergmNormalizer_pos t θ))

/-- The law as a probability mass function. -/
noncomputable def ergmPMF {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) : PMF (SimpleGraph V) :=
  PMF.ofFintype (fun G => ENNReal.ofReal (ergmProb t θ G)) (by
    have hnn : ∀ G ∈ (Finset.univ : Finset (SimpleGraph V)),
      0 ≤ ergmProb t θ G :=
      fun G _ => le_of_lt (ergmProb_pos t θ G)
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    rw [sum_ergmProb t θ]
    exact ENNReal.ofReal_one)

/-- Evaluation of the PMF version. -/
theorem ergmPMF_apply {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (G : SimpleGraph V) :
    ergmPMF t θ G = ENNReal.ofReal (ergmProb t θ G) := by
  rfl

/-- Real value of the PMF version. -/
theorem toReal_ergmPMF_apply {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (G : SimpleGraph V) :
    (ergmPMF t θ G).toReal = ergmProb t θ G := by
  rw [ergmPMF_apply]
  exact ENNReal.toReal_ofReal (le_of_lt (ergmProb_pos t θ G))

/-- Log-likelihood: the logarithm of the law in Snijders (2002), eq. (3). -/
noncomputable def ergmLogLik {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (y : SimpleGraph V) : ℝ :=
  θ ⬝ᵥ t y - Real.log (ergmNormalizer t θ)

/-- Log-likelihood equals the log probability. -/
theorem ergmLogLik_eq_log_ergmProb {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    (y : SimpleGraph V) :
    ergmLogLik t θ y = Real.log (ergmProb t θ y) := by
  unfold ergmLogLik ergmProb
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt (ergmNormalizer_pos t θ))]
  rw [Real.log_exp]

/-- Mean value `µ(θ)`. -/
noncomputable def ergmMean {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) : ι → ℝ :=
  fun k => ∑ G, ergmProb t θ G * t G k

/-- Observed minus expected; its zero set is the moment equation, Snijders (2002), eq. (24). -/
noncomputable def ergmScore {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (y : SimpleGraph V) : ι → ℝ :=
  t y - ergmMean t θ

/-- Moment equation: score vanishes iff observed equals expected. -/
theorem ergmScore_eq_zero_iff {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (y : SimpleGraph V) :
    ergmScore t θ y = 0 ↔ t y = ergmMean t θ := by
  simp only [ergmScore, sub_eq_zero]

private theorem dot_line {ι : Type*} [Fintype ι]
    (θ v w : ι → ℝ) (s : ℝ) :
    ((θ + s • v) ⬝ᵥ w) = (θ ⬝ᵥ w) + s * (v ⬝ᵥ w) := by
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

private theorem hasDerivAt_dot_line {ι : Type*} [Fintype ι]
    (θ v w : ι → ℝ) :
    HasDerivAt (fun s : ℝ => (θ + s • v) ⬝ᵥ w)
      (v ⬝ᵥ w) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s * (v ⬝ᵥ w))
    (1 * (v ⬝ᵥ w)) 0 :=
    HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (v ⬝ᵥ w)
  have h2 : HasDerivAt (fun s : ℝ => (θ ⬝ᵥ w) + s * (v ⬝ᵥ w))
    (1 * (v ⬝ᵥ w)) 0 :=
    HasDerivAt.const_add (θ ⬝ᵥ w) h1
  rw [one_mul] at h2
  have heq : (fun s : ℝ => (θ + s • v) ⬝ᵥ w) =
    (fun s => (θ ⬝ᵥ w) + s * (v ⬝ᵥ w)) := by
    funext s
    exact dot_line θ v w s
  rw [heq]
  exact h2

private theorem hasDerivAt_exp_dot_line {ι : Type*} [Fintype ι]
    (θ v w : ι → ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp ((θ + s • v) ⬝ᵥ w))
      (Real.exp (θ ⬝ᵥ w) * (v ⬝ᵥ w)) 0 := by
  simpa using HasDerivAt.exp (hasDerivAt_dot_line θ v w)

private theorem hasDerivAt_normalizer_line {V : Type*}
    [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ) :
    HasDerivAt (fun s : ℝ => ergmNormalizer t (θ + s • v))
      (∑ G, Real.exp (θ ⬝ᵥ t G) * (v ⬝ᵥ t G)) 0 := by
  unfold ergmNormalizer
  apply HasDerivAt.fun_sum
  intro G _
  exact hasDerivAt_exp_dot_line θ v (t G)

private theorem hasDerivAt_log_normalizer_line {V : Type*}
    [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ) :
    HasDerivAt
      (fun s : ℝ => Real.log (ergmNormalizer t (θ + s • v)))
      ((∑ G, Real.exp (θ ⬝ᵥ t G) * (v ⬝ᵥ t G)) /
        ergmNormalizer t θ) 0 := by
  have h := hasDerivAt_normalizer_line t θ v
  have hne : ergmNormalizer t (θ + (0 : ℝ) • v) ≠ 0 :=
    ne_of_gt (ergmNormalizer_pos t _)
  simpa using HasDerivAt.log h hne

private theorem dot_mean_eq {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ v : ι → ℝ) :
    (v ⬝ᵥ ergmMean t θ) =
      ∑ G, ergmProb t θ G * (v ⬝ᵥ t G) := by
  unfold ergmMean
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem sum_prob_mul_eq {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    (b : SimpleGraph V → ℝ) :
    (∑ G, ergmProb t θ G * b G) =
      (∑ G, Real.exp (θ ⬝ᵥ t G) * b G) /
        ergmNormalizer t θ := by
  unfold ergmProb
  simp only [div_mul_eq_mul_div]
  rw [← Finset.sum_div]

private theorem dot_mean_eq_div {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ) :
    (v ⬝ᵥ ergmMean t θ) =
      (∑ G, Real.exp (θ ⬝ᵥ t G) * (v ⬝ᵥ t G)) /
        ergmNormalizer t θ := by
  rw [dot_mean_eq, sum_prob_mul_eq]

/-- Directional derivative of the log-likelihood is the score. -/
theorem hasDerivAt_ergmLogLik {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    (y : SimpleGraph V) (v : ι → ℝ) :
    HasDerivAt (fun s : ℝ => ergmLogLik t (θ + s • v) y)
      (v ⬝ᵥ ergmScore t θ y) 0 := by
  unfold ergmLogLik ergmScore
  have h1 : HasDerivAt (fun s : ℝ => (θ + s • v) ⬝ᵥ t y)
    (v ⬝ᵥ t y) 0 :=
    hasDerivAt_dot_line θ v (t y)
  have h2 := hasDerivAt_log_normalizer_line t θ v
  have hsub := HasDerivAt.sub h1 h2
  have hmean : (v ⬝ᵥ ergmMean t θ) =
    (∑ G, Real.exp (θ ⬝ᵥ t G) * (v ⬝ᵥ t G)) /
      ergmNormalizer t θ :=
    dot_mean_eq_div t θ v
  have hdot : (v ⬝ᵥ (t y - ergmMean t θ)) =
    (v ⬝ᵥ t y) - (v ⬝ᵥ ergmMean t θ) :=
    dotProduct_sub v (t y) (ergmMean t θ)
  rw [hdot, hmean]
  exact hsub

private theorem update_eq_add_single {ι : Type*} [DecidableEq ι]
    (θ : ι → ℝ) (k : ι) (s : ℝ) :
    Function.update θ k s =
      θ + (s - θ k) • Pi.single k 1 := by
  funext i
  by_cases h : i = k
  · simp only [h, Function.update_self]
    have h1 : (Pi.single (M := fun _ => ℝ) k 1 k) = 1 :=
      Pi.single_eq_same k 1
    rw [Pi.add_apply, Pi.smul_apply, h1, smul_eq_mul, mul_one]
    ring
  · simp [h]

/-- Coordinate derivative of the log-likelihood: the mean is the gradient of the
log-normalizer, Snijders (2002), eq. (25). -/
theorem hasDerivAt_ergmLogLik_update {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    (y : SimpleGraph V) [DecidableEq ι] (k : ι) :
    HasDerivAt
      (fun s : ℝ => ergmLogLik t (Function.update θ k s) y)
      (ergmScore t θ y k) (θ k) := by
  let v : ι → ℝ := Pi.single k 1
  have hupd : ∀ s : ℝ, Function.update θ k s = θ + (s - θ k) • v :=
    fun s => update_eq_add_single θ k s
  have hdir : HasDerivAt (fun u : ℝ => ergmLogLik t (θ + u • v) y)
    (v ⬝ᵥ ergmScore t θ y) 0 :=
    hasDerivAt_ergmLogLik t θ y v
  have hdir' : HasDerivAt (fun u : ℝ => ergmLogLik t (θ + u • v) y)
    (v ⬝ᵥ ergmScore t θ y) ((fun s : ℝ => s - θ k) (θ k)) := by
    have hthis := hdir
    have h0' : (0:ℝ) = (fun s : ℝ => s - θ k) (θ k) := by simp
    rw [h0'] at hthis
    exact hthis
  have hlin : HasDerivAt (fun s : ℝ => s - θ k) 1 (θ k) := by
    have h1 := HasDerivAt.sub (hasDerivAt_id (θ k)) (hasDerivAt_const (θ k) (θ k))
    rw [sub_zero] at h1
    exact h1
  have hcomp : HasDerivAt ((fun u : ℝ => ergmLogLik t (θ + u • v) y) ∘
      (fun s : ℝ => s - θ k)) ((v ⬝ᵥ ergmScore t θ y) * 1) (θ k) :=
    HasDerivAt.comp (θ k) hdir' hlin
  have hsingle : (v ⬝ᵥ ergmScore t θ y) = ergmScore t θ y k := by
    simp [v, dotProduct, Pi.single_apply]
  have hder : (v ⬝ᵥ ergmScore t θ y) * 1 = ergmScore t θ y k := by
    rw [mul_one, hsingle]
  have heq : ((fun u : ℝ => ergmLogLik t (θ + u • v) y) ∘
    (fun s : ℝ => s - θ k)) =
    (fun s : ℝ => ergmLogLik t (Function.update θ k s) y) := by
    funext s
    simp only [Function.comp_apply]
    rw [hupd s]
  rw [heq, hder] at hcomp
  exact hcomp

/-- Covariance matrix `Σ(θ)`. -/
noncomputable def ergmCov {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] (t : SimpleGraph V → ι → ℝ)
    (θ : ι → ℝ) (j k : ι) : ℝ :=
  ∑ G, ergmProb t θ G * (t G j - ergmMean t θ j) *
    (t G k - ergmMean t θ k)

private theorem hasDerivAt_prob_line {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ)
    (G : SimpleGraph V) :
    HasDerivAt (fun s : ℝ => ergmProb t (θ + s • v) G)
      (ergmProb t θ G *
        ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ))) 0 := by
  have hN := hasDerivAt_exp_dot_line θ v (t G)
  have hD := hasDerivAt_normalizer_line t θ v
  have hne : ergmNormalizer t (θ + (0 : ℝ) • v) ≠ 0 :=
    ne_of_gt (ergmNormalizer_pos t _)
  have hdiv := HasDerivAt.div hN hD hne
  have hmean := dot_mean_eq_div t θ v
  have hDne : ergmNormalizer t θ ≠ 0 :=
    ne_of_gt (ergmNormalizer_pos t θ)
  have hEq : ((Real.exp (θ ⬝ᵥ t G) * (v ⬝ᵥ t G)) *
    ergmNormalizer t θ - Real.exp (θ ⬝ᵥ t G) *
      (∑ H, Real.exp (θ ⬝ᵥ t H) * (v ⬝ᵥ t H))) /
    (ergmNormalizer t θ) ^ 2 =
    (Real.exp (θ ⬝ᵥ t G) / ergmNormalizer t θ) *
      ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) := by
    rw [hmean]
    field_simp
  have hdivS := by simpa only [zero_smul, add_zero] using hdiv
  rw [hEq] at hdivS
  unfold ergmProb
  exact hdivS

private theorem hasDerivAt_mean_line_aux {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ) (j : ι) :
    HasDerivAt (fun s : ℝ => ergmMean t (θ + s • v) j)
      (∑ G, ergmProb t θ G *
        ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) * t G j) 0 := by
  unfold ergmMean
  apply HasDerivAt.fun_sum
  intro G _
  have hP := hasDerivAt_prob_line t θ v G
  have hM := HasDerivAt.mul_const hP (t G j)
  exact hM

private theorem sum_cov_mul_eq {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ) (j : ι) :
    (∑ k, ergmCov t θ j k * v k) =
      ∑ G, ergmProb t θ G * (t G j - ergmMean t θ j) *
        ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) := by
  unfold ergmCov
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G _
  have hdot : (v ⬝ᵥ (t G - ergmMean t θ)) =
    (v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ) :=
    dotProduct_sub v (t G) (ergmMean t θ)
  simp only [dotProduct] at hdot ⊢
  rw [← hdot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.sub_apply]
  ring

private theorem sum_prob_sub_zero {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ v : ι → ℝ) :
    ∑ G, ergmProb t θ G *
        ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) = 0 := by
  have h1 : (∑ G, ergmProb t θ G * (v ⬝ᵥ t G)) =
    (v ⬝ᵥ ergmMean t θ) := (dot_mean_eq t θ v).symm
  have h2 : (∑ G, ergmProb t θ G * (v ⬝ᵥ ergmMean t θ)) =
    (v ⬝ᵥ ergmMean t θ) := by
    rw [← Finset.sum_mul]
    simp [sum_ergmProb]
  have hsub : (∑ G, ergmProb t θ G * ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ))) =
    (∑ G, ergmProb t θ G * (v ⬝ᵥ t G)) -
      (∑ G, ergmProb t θ G * (v ⬝ᵥ ergmMean t θ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro G _
    ring
  rw [hsub, h1, h2, sub_self]

private theorem sum_mean_factor {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ) (j : ι)
    (v : ι → ℝ) :
    (∑ G, ergmProb t θ G *
        ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) * t G j) =
      ∑ G, ergmProb t θ G * (t G j - ergmMean t θ j) *
        ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) := by
  have h0 := sum_prob_sub_zero t θ v
  have hdiff : (∑ G, ergmProb t θ G * ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) *
    t G j) - (∑ G, ergmProb t θ G * (t G j - ergmMean t θ j) *
    ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ))) = 0 := by
    rw [← Finset.sum_sub_distrib]
    have hfac : ∀ G : SimpleGraph V, ergmProb t θ G *
      ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) * t G j -
      ergmProb t θ G * (t G j - ergmMean t θ j) *
      ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) =
      (ergmProb t θ G * ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ))) *
        ergmMean t θ j := by
      intro G
      ring
    simp only [hfac, ← Finset.sum_mul]
    rw [h0, zero_mul]
  exact sub_eq_zero.mp hdiff

/-- Derivative of the mean is the covariance, Snijders (2002), eq. (26). -/
theorem hasDerivAt_ergmMean {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    (v : ι → ℝ) (j : ι) :
    HasDerivAt (fun s : ℝ => ergmMean t (θ + s • v) j)
      (∑ k, ergmCov t θ j k * v k) 0 := by
  have h := hasDerivAt_mean_line_aux t θ v j
  have heq : (∑ G, ergmProb t θ G * ((v ⬝ᵥ t G) - (v ⬝ᵥ ergmMean t θ)) *
    t G j) = (∑ k, ergmCov t θ j k * v k) := by
    rw [sum_mean_factor, ← sum_cov_mul_eq]
  rwa [heq] at h

/-- Derivative of the score; Hessian of log-likelihood is `-Σ(θ)`. -/
theorem hasDerivAt_ergmScore {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    (y : SimpleGraph V) (v : ι → ℝ) (j : ι) :
    HasDerivAt (fun s : ℝ => ergmScore t (θ + s • v) y j)
      (-(∑ k, ergmCov t θ j k * v k)) 0 := by
  have hmean := hasDerivAt_ergmMean t θ v j
  have h := hmean.const_sub (t y j)
  simpa [ergmScore, Pi.sub_apply] using h

/-- A constant-statistic direction is irrelevant. This generalizes Snijders (2002),
Section 4.1, where a fixed number of ties makes the edge parameter irrelevant. -/
theorem ergmProb_add_of_affine {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) (θ : ι → ℝ)
    {v : ι → ℝ} {c : ℝ} (h : ∀ G, v ⬝ᵥ t G = c) :
    ergmProb t (θ + v) = ergmProb t θ := by
  funext G
  have hdot : ∀ H, ((θ + v) ⬝ᵥ t H) = (θ ⬝ᵥ t H) + c := by
    intro H
    rw [add_dotProduct, h H]
  have hexp : ∀ H, Real.exp (((θ + v) ⬝ᵥ t H)) =
    Real.exp (θ ⬝ᵥ t H) * Real.exp c := by
    intro H
    rw [hdot H, Real.exp_add]
  have hsum : (∑ H, Real.exp (((θ + v) ⬝ᵥ t H))) =
      (∑ H, Real.exp (θ ⬝ᵥ t H)) * Real.exp c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun H _ => hexp H)
  unfold ergmProb ergmNormalizer
  rw [hexp G, hsum, mul_div_mul_right _ _ (Real.exp_ne_zero c)]

/-- Identifiability iff no affine dependence. -/
theorem ergmProb_injective_iff {V : Type*} [Fintype V]
    [DecidableEq V] {ι : Type*} [Fintype ι]
    (t : SimpleGraph V → ι → ℝ) :
    Function.Injective (ergmProb t) ↔
      ∀ (v : ι → ℝ) (c : ℝ),
        (∀ G, v ⬝ᵥ t G = c) → v = 0 := by
  constructor
  · intro hinj v c hc
    have hprob : ergmProb t (0 + v) = ergmProb t 0 :=
      ergmProb_add_of_affine t 0 hc
    have h01 : (0 : ι → ℝ) + v = 0 := hinj hprob
    rw [zero_add] at h01
    exact h01
  · intro haff θ1 θ2 h12
    have h1 : ∀ G, Real.log (ergmProb t θ1 G) =
      (θ1 ⬝ᵥ t G) - Real.log (ergmNormalizer t θ1) := by
      intro G
      rw [← ergmLogLik_eq_log_ergmProb]
      rfl
    have h2 : ∀ G, Real.log (ergmProb t θ2 G) =
      (θ2 ⬝ᵥ t G) - Real.log (ergmNormalizer t θ2) := by
      intro G
      rw [← ergmLogLik_eq_log_ergmProb]
      rfl
    have hconst : ∀ G, (θ1 - θ2) ⬝ᵥ t G =
      Real.log (ergmNormalizer t θ1) -
        Real.log (ergmNormalizer t θ2) := by
      intro G
      rw [sub_dotProduct]
      have hG := congrArg Real.log (congrFun h12 G)
      rw [h1 G, h2 G] at hG
      linarith
    have hv0 : θ1 - θ2 = 0 :=
      haff _ _ hconst
    exact sub_eq_zero.mp hv0

/-! ## Stochastic block model and label swapping

The graph weight below sums over latent labelings; permuting the class
labels leaves the weight unchanged (Allman, Matias and Rhodes 2009, Section 2).
Admissible parameters (positive mixing proportions summing to one,
symmetric affinities in `[0,1]`) make the weight a probability law,
exposed as a `PMF` with nonnegativity and normalization.
-/

/-- Admissible block-model parameters: positive `p` summing to one,
symmetric `W` in `[0,1]`. -/
def SBMAdmissible {K : Type*} [Fintype K] (p : K → ℝ)
    (W : K → K → ℝ) : Prop :=
  (∀ k, 0 < p k) ∧ (∑ k, p k = 1) ∧
    (∀ i j, 0 ≤ W i j ∧ W i j ≤ 1) ∧ ∀ i j, W i j = W j i

/-- Prior weight of a labeling: each node draws its class independently. -/
noncomputable def sbmLabelWeight {V : Type*} [Fintype V]
    {K : Type*} [Fintype K] (p : K → ℝ) (z : V → K) : ℝ :=
  ∏ v, p (z v)

open Classical in
/-- Edge factor of a labeling: independent Bernoulli edges given classes. -/
noncomputable def sbmEdgeWeight {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] (W : K → K → ℝ) (z : V → K)
    (G : SimpleGraph V) : ℝ :=
  ∏ u, ∏ v, if u < v then
    (if G.Adj u v then W (z u) (z v) else 1 - W (z u) (z v)) else 1

/-- Block-model graph weight: sum over latent labelings.

This is an unnormalized weight for arbitrary `p` and `W`; under
`SBMAdmissible` it is a probability law (see `sbmGraphPMF`). -/
noncomputable def sbmGraphWeight {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] (p : K → ℝ) (W : K → K → ℝ)
    (G : SimpleGraph V) : ℝ :=
  ∑ z : V → K, sbmLabelWeight p z * sbmEdgeWeight W z G

/-- Relabeling the prior permutes the labeling. -/
theorem sbmLabelWeight_relabel {V : Type*} [Fintype V]
    {K : Type*} [Fintype K] {p : K → ℝ} {z : V → K}
    (σ : Equiv.Perm K) :
    sbmLabelWeight (p ∘ σ) z = sbmLabelWeight p (σ ∘ z) := by
  simp only [sbmLabelWeight, Function.comp_apply]

/-- Relabeling the affinities permutes the labeling. -/
theorem sbmEdgeWeight_relabel {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] {W : K → K → ℝ} {z : V → K}
    {G : SimpleGraph V} (σ : Equiv.Perm K) :
    sbmEdgeWeight (fun i j => W (σ i) (σ j)) z G
      = sbmEdgeWeight W (σ ∘ z) G := by
  simp only [sbmEdgeWeight, Function.comp_apply]

/-- Label swapping (Allman, Matias and Rhodes 2009, Section 2): relabeled parameters give the
same weight.

Parameters are identified at most modulo permutation of the classes: a
numerical clustering output is not statistical identification. Under
`SBMAdmissible` this is equality of laws (see `sbmGraphPMF_relabel`).
-/
theorem sbmGraphWeight_relabel {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] {p : K → ℝ} {W : K → K → ℝ}
    (σ : Equiv.Perm K) :
    sbmGraphWeight (V := V) (p ∘ σ) (fun i j => W (σ i) (σ j))
      = sbmGraphWeight p W := by
  funext G
  simp only [sbmGraphWeight, sbmLabelWeight_relabel σ,
    sbmEdgeWeight_relabel σ]
  have h : ∀ z : V → K,
      (σ ∘ z) = (Equiv.arrowCongr (Equiv.refl V) σ) z := by
    intro z
    funext v
    rfl
  simp only [h]
  exact Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl V) σ)
    (fun z => sbmLabelWeight p z * sbmEdgeWeight W z G)

/-- Admissibility is preserved under relabeling. -/
theorem SBMAdmissible_relabel {K : Type*} [Fintype K]
    {p : K → ℝ} {W : K → K → ℝ} (σ : Equiv.Perm K)
    (h : SBMAdmissible p W) :
    SBMAdmissible (p ∘ σ) (fun i j => W (σ i) (σ j)) := by
  obtain ⟨hpos, hsum, hmem, hsym⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact hpos (σ k)
  · have hcomp : ∑ k, p (σ k) = ∑ k, p k := Equiv.sum_comp σ p
    simpa [Function.comp_apply] using hcomp.trans hsum
  · intro i j
    exact hmem (σ i) (σ j)
  · intro i j
    exact hsym (σ i) (σ j)

/-- The admissible parameter space is nonempty (uniform mixing). -/
theorem SBMAdmissible_nonempty {K : Type*} [Fintype K] [Nonempty K] :
    ∃ p : K → ℝ, ∃ W : K → K → ℝ, SBMAdmissible p W := by
  have hcard : 0 < (Fintype.card K : ℝ) := by
    have hc : 0 < Fintype.card K := Fintype.card_pos
    exact Nat.cast_pos.mpr hc
  refine ⟨fun _ => 1 / Fintype.card K, fun _ _ => 1 / 2, ?_, ?_, ?_, ?_⟩
  · intro k
    change (0:ℝ) < 1 / (Fintype.card K : ℝ)
    exact div_pos zero_lt_one hcard
  · simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · intro i j
    norm_num
  · intro i j
    rfl

private theorem sbmLabelWeight_pos {V : Type*} [Fintype V]
    {K : Type*} [Fintype K] {p : K → ℝ} {z : V → K}
    (hpos : ∀ k, 0 < p k) : 0 < sbmLabelWeight p z := by
  unfold sbmLabelWeight
  apply Finset.prod_pos
  intro v _
  exact hpos (z v)

private theorem sbmEdgeWeight_nonneg_aux {V : Type*} [Fintype V]
    [LinearOrder V] {K : Type*} [Fintype K] {W : K → K → ℝ}
    {z : V → K} {G : SimpleGraph V}
    (hmem : ∀ i j, 0 ≤ W i j ∧ W i j ≤ 1) :
    0 ≤ sbmEdgeWeight W z G := by
  unfold sbmEdgeWeight
  apply Finset.prod_nonneg
  intro u _
  apply Finset.prod_nonneg
  intro v _
  by_cases huv : u < v
  · simp only [huv, ite_true]
    by_cases hadj : G.Adj u v
    · simp only [hadj, ite_true]
      exact (hmem (z u) (z v)).1
    · simp only [hadj, ite_false]
      exact sub_nonneg.mpr (hmem (z u) (z v)).2
  · simp [huv]

/-- The graph weight is nonnegative under admissibility. -/
theorem sbmGraphWeight_nonneg {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] {p : K → ℝ} {W : K → K → ℝ}
    (G : SimpleGraph V) (h : SBMAdmissible p W) :
    0 ≤ sbmGraphWeight p W G := by
  obtain ⟨hpos, _, hmem, _⟩ := h
  unfold sbmGraphWeight
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg
  · exact le_of_lt (sbmLabelWeight_pos hpos)
  · exact sbmEdgeWeight_nonneg_aux hmem

private theorem sum_sbmLabelWeight_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] {K : Type*} [Fintype K]
    {p : K → ℝ} (_hpos : ∀ k, 0 < p k) (hsum : ∑ k, p k = 1) :
    ∑ z : V → K, sbmLabelWeight p z = 1 := by
  have hprod : (∑ z : V → K, ∏ v, p (z v)) = ∏ _v : V, ∑ k, p k :=
    (Fintype.prod_sum (fun _ : V => fun k : K => p k)).symm
  unfold sbmLabelWeight
  rw [hprod, hsum]
  simp

/-- The unordered pairs of distinct vertices. -/
private noncomputable def sbmPairSet (V : Type*) [Fintype V] [LinearOrder V] :
    Finset (V × V) :=
  Finset.univ.filter (fun p : V × V => p.1 < p.2)

private theorem sbmPairSet_mem {V : Type*} [Fintype V] [LinearOrder V] (u v : V)
    (h : u ≠ v) : (min u v, max u v) ∈ sbmPairSet V := by
  unfold sbmPairSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact min_lt_max.mpr h

open Classical in
/-- Graphs correspond to boolean labelings of the unordered pairs. -/
private noncomputable def sbmGraphEquivBool (V : Type*) [Fintype V] [LinearOrder V]
    [DecidableEq V] : (↥(sbmPairSet V) → Bool) ≃ SimpleGraph V where
  toFun b :=
    { Adj := fun u v => if _h : u = v then False else
        b ⟨(min u v, max u v), sbmPairSet_mem u v _h⟩ = true
      symm := ⟨fun u v h => by
        by_cases heq : u = v
        · subst heq
          exact absurd h (by simp)
        · have heq' : ¬ v = u := fun hvu => heq hvu.symm
          simp only [dite_eq_right heq] at h
          simp only [dite_eq_right heq']
          have e : (min v u, max v u) = (min u v, max u v) := by
            rw [min_comm, max_comm]
          have hsub : (⟨(min v u, max v u), sbmPairSet_mem v u heq'⟩ :
            ↥(sbmPairSet V)) = ⟨(min u v, max u v), sbmPairSet_mem u v heq⟩ :=
            Subtype.ext e
          rw [hsub]
          exact h⟩
      loopless := ⟨fun u h => by simp at h⟩ }
  invFun G p := decide (G.Adj p.1.1 p.1.2)
  left_inv := by
    intro b
    funext p
    obtain ⟨⟨u, v⟩, hp⟩ := p
    have hp' : u < v := by
      have hmem := hp
      unfold sbmPairSet at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    have hne : ¬ u = v := ne_of_lt hp'
    have hsub : (⟨(min u v, max u v), sbmPairSet_mem u v hne⟩ :
      ↥(sbmPairSet V)) = ⟨(u, v), hp⟩ := by
      apply Subtype.ext
      simp [min_eq_left (le_of_lt hp'), max_eq_right (le_of_lt hp')]
    dsimp only
    simp only [dite_eq_right hne, hsub]
    simp
  right_inv := by
    intro G
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · intro h
      by_cases heq : u = v
      · subst heq
        exact absurd h (by simp)
      · simp only [dite_eq_right heq] at h
        by_cases huv : u < v
        · have e1 : min u v = u := min_eq_left (le_of_lt huv)
          have e2 : max u v = v := max_eq_right (le_of_lt huv)
          have hadj : G.Adj (min u v) (max u v) :=
            of_decide_eq_true h
          rw [e1, e2] at hadj
          exact hadj
        · by_cases hvu : v < u
          · have e1 : min u v = v := min_eq_right (le_of_lt hvu)
            have e2 : max u v = u := max_eq_left (le_of_lt hvu)
            have hadj : G.Adj (min u v) (max u v) :=
              of_decide_eq_true h
            rw [e1, e2] at hadj
            exact Std.Symm.symm (self := G.symm) _ _ hadj
          · have huv' : u = v := by
              rcases lt_trichotomy u v with h1 | h1 | h1
              · exact absurd h1 huv
              · exact h1
              · exact absurd h1 hvu
            exact absurd huv' heq
    · intro h
      by_cases heq : u = v
      · subst heq
        exact absurd h (Std.Irrefl.irrefl (self := G.loopless) u)
      · simp only [dite_eq_right heq]
        by_cases huv : u < v
        · have e1 : min u v = u := min_eq_left (le_of_lt huv)
          have e2 : max u v = v := max_eq_right (le_of_lt huv)
          have hadj : G.Adj (min u v) (max u v) := by
            rw [e1, e2]
            exact h
          exact decide_eq_true hadj
        · by_cases hvu : v < u
          · have e1 : min u v = v := min_eq_right (le_of_lt hvu)
            have e2 : max u v = u := max_eq_left (le_of_lt hvu)
            have hadj : G.Adj (min u v) (max u v) := by
              rw [e1, e2]
              exact Std.Symm.symm (self := G.symm) _ _ h
            exact decide_eq_true hadj
          · have huv' : u = v := by
              rcases lt_trichotomy u v with h1 | h1 | h1
              · exact absurd h1 huv
              · exact h1
              · exact absurd h1 hvu
            exact absurd huv' heq

open Classical in
private theorem sbmEdgeWeight_eq_prod {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] {W : K → K → ℝ} {z : V → K}
    {G : SimpleGraph V} :
    sbmEdgeWeight W z G =
      ∏ p ∈ sbmPairSet V,
        (if G.Adj p.1 p.2 then W (z p.1) (z p.2) else
          1 - W (z p.1) (z p.2)) := by
  unfold sbmEdgeWeight sbmPairSet
  have h1 : ∀ u : V, (∏ v, (if u < v then
      (if G.Adj u v then W (z u) (z v) else 1 - W (z u) (z v)) else 1)) =
      ∏ v ∈ Finset.univ.filter (fun v => u < v),
        (if G.Adj u v then W (z u) (z v) else 1 - W (z u) (z v)) := by
    intro u
    rw [← Finset.prod_filter]
  simp only [h1]
  exact (Finset.prod_finset_product
    (Finset.univ.filter (fun p : V × V => p.1 < p.2))
    (Finset.univ : Finset V)
    (fun u : V => Finset.univ.filter (fun v => u < v))
    (fun p => by simp)
    (f := fun p : V × V => if G.Adj p.1 p.2 then W (z p.1) (z p.2)
      else 1 - W (z p.1) (z p.2))).symm

open Classical in
private theorem sbmEdgeWeight_of_graphBool {V : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq V] {K : Type*} [Fintype K] {W : K → K → ℝ} {z : V → K}
    (b : ↥(sbmPairSet V) → Bool) :
    sbmEdgeWeight W z (sbmGraphEquivBool V b) =
      ∏ p : ↥(sbmPairSet V),
        (if b p then W (z p.1.1) (z p.1.2) else
          1 - W (z p.1.1) (z p.1.2)) := by
  classical
  rw [sbmEdgeWeight_eq_prod, ← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  have hP : p.1 ∈ Finset.univ.filter (fun q : V × V => q.1 < q.2) := p.2
  have hmem : p.1.1 < p.1.2 := (Finset.mem_filter.mp hP).2
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt hmem
  have e1 : min p.1.1 p.1.2 = p.1.1 := min_eq_left (le_of_lt hmem)
  have e2 : max p.1.1 p.1.2 = p.1.2 := max_eq_right (le_of_lt hmem)
  have hAdjEq : (sbmGraphEquivBool V b).Adj p.1.1 p.1.2 =
      (b ⟨(min p.1.1 p.1.2, max p.1.1 p.1.2),
        sbmPairSet_mem _ _ hne⟩ = true) := by
    change ((if _h : p.1.1 = p.1.2 then False else
      b ⟨(min p.1.1 p.1.2, max p.1.1 p.1.2),
        sbmPairSet_mem _ _ _h⟩ = true)) = _
    rw [dite_eq_right hne]
  have hX : (⟨(min p.1.1 p.1.2, max p.1.1 p.1.2), sbmPairSet_mem _ _ hne⟩ :
      ↥(sbmPairSet V)) = p :=
    Subtype.ext (by simp [e1, e2])
  have hcond : (sbmGraphEquivBool V b).Adj p.1.1 p.1.2 ↔ b p = true := by
    rw [hAdjEq, hX]
  rcases Bool.eq_false_or_eq_true (b p) with hb | hb
  · have hpc : (sbmGraphEquivBool V b).Adj p.1.1 p.1.2 := hcond.mpr hb
    rw [ite_eq_left hpc, hb]
    simp
  · have hnc : ¬ (sbmGraphEquivBool V b).Adj p.1.1 p.1.2 := by
      intro hc
      have hcon := hcond.mp hc
      rw [hb] at hcon
      exact Bool.false_ne_true hcon
    rw [ite_eq_right hnc, hb]
    simp

private theorem sum_sbmEdgeWeight_eq_one {V : Type*} [Fintype V]
    [LinearOrder V] [DecidableEq V] {K : Type*} [Fintype K]
    {W : K → K → ℝ} {z : V → K}
    (_hmem : ∀ i j, 0 ≤ W i j ∧ W i j ≤ 1)
    (_hsym : ∀ i j, W i j = W j i) :
    ∑ G : SimpleGraph V, sbmEdgeWeight W z G = 1 := by
  classical
  have hsum : (∑ G : SimpleGraph V, sbmEdgeWeight W z G) =
      ∑ b : (↥(sbmPairSet V) → Bool),
        sbmEdgeWeight W z (sbmGraphEquivBool V b) :=
    (Equiv.sum_comp (sbmGraphEquivBool V) _).symm
  rw [hsum]
  have hper : ∀ b : (↥(sbmPairSet V) → Bool),
      sbmEdgeWeight W z (sbmGraphEquivBool V b) =
        ∏ p : (↥(sbmPairSet V)),
          (if b p then W (z p.1.1) (z p.1.2) else
            1 - W (z p.1.1) (z p.1.2)) :=
    fun b => sbmEdgeWeight_of_graphBool b
  simp only [hper]
  have key : (∑ b : (↥(sbmPairSet V) → Bool), ∏ p : (↥(sbmPairSet V)),
      (if b p then W (z p.1.1) (z p.1.2) else 1 - W (z p.1.1) (z p.1.2))) =
      ∏ p : (↥(sbmPairSet V)), ∑ c : Bool,
      (if c then W (z p.1.1) (z p.1.2) else 1 - W (z p.1.1) (z p.1.2)) :=
    (Fintype.prod_sum (fun (p : ↥(sbmPairSet V)) (c : Bool) =>
      if c then W (z p.1.1) (z p.1.2) else 1 - W (z p.1.1) (z p.1.2))).symm
  rw [key]
  have hBool : ∀ (f : Bool → ℝ), ∑ b : Bool, f b = f false + f true := by
    intro f
    have h : ({false, true} : Finset Bool) = Finset.univ := by decide
    conv_lhs => rw [← h]
    simp
  have hW : ∀ p : (↥(sbmPairSet V)),
      (∑ c : Bool, (if c then W (z p.1.1) (z p.1.2) else
        1 - W (z p.1.1) (z p.1.2))) = 1 := by
    intro p
    rw [hBool]
    simp
  simp only [hW]
  simp

/-- The graph weights sum to one under admissibility. -/
theorem sum_sbmGraphWeight {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K]
    {p : K → ℝ} {W : K → K → ℝ} (h : SBMAdmissible p W) :
    ∑ G : SimpleGraph V, sbmGraphWeight p W G = 1 := by
  obtain ⟨hpos, hsum, hmem, hsym⟩ := h
  unfold sbmGraphWeight
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hE : ∀ z : V → K, ∑ G : SimpleGraph V,
    sbmEdgeWeight W z G = 1 :=
    fun z => sum_sbmEdgeWeight_eq_one hmem hsym
  simp only [hE, mul_one]
  exact sum_sbmLabelWeight_eq_one hpos hsum

/-- Block-model graph law as a `PMF` under admissibility. -/
noncomputable def sbmGraphPMF {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] [DecidableEq K]
    (p : K → ℝ) (W : K → K → ℝ) (h : SBMAdmissible p W) :
    PMF (SimpleGraph V) :=
  PMF.ofFintype (fun G => ENNReal.ofReal (sbmGraphWeight p W G)) (by
    have hnn : ∀ G ∈ (Finset.univ : Finset (SimpleGraph V)),
      0 ≤ sbmGraphWeight p W G :=
      fun G _ => sbmGraphWeight_nonneg G h
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    rw [sum_sbmGraphWeight h]
    exact ENNReal.ofReal_one)

/-- Evaluation of the block-model `PMF`. -/
theorem sbmGraphPMF_apply {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] [DecidableEq K]
    {p : K → ℝ} {W : K → K → ℝ} {h : SBMAdmissible p W}
    (G : SimpleGraph V) :
    sbmGraphPMF p W h G = ENNReal.ofReal (sbmGraphWeight p W G) := by
  rfl

/-- Real value of the block-model `PMF`. -/
theorem toReal_sbmGraphPMF_apply {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] [DecidableEq K]
    {p : K → ℝ} {W : K → K → ℝ} {h : SBMAdmissible p W}
    (G : SimpleGraph V) :
    (sbmGraphPMF p W h G).toReal = sbmGraphWeight p W G := by
  rw [sbmGraphPMF_apply]
  exact ENNReal.toReal_ofReal (sbmGraphWeight_nonneg G h)

/-- Label swapping for the block-model `PMF`: relabeled admissible
parameters give the same law. -/
theorem sbmGraphPMF_relabel {V : Type*} [Fintype V] [LinearOrder V]
    {K : Type*} [Fintype K] [DecidableEq K]
    {p : K → ℝ} {W : K → K → ℝ} (σ : Equiv.Perm K)
    (h : SBMAdmissible p W) :
    sbmGraphPMF (V := V) (p ∘ σ) (fun i j => W (σ i) (σ j))
      (SBMAdmissible_relabel σ h) = sbmGraphPMF (V := V) p W h := by
  apply PMF.ext
  intro G
  simp only [sbmGraphPMF_apply]
  rw [congrFun (sbmGraphWeight_relabel (V := V) σ) G]

/-- Label swapping makes the weight map non-injective. -/
theorem not_injective_sbmGraphWeight_of_relabel_ne {K : Type*}
    [Fintype K] {p : K → ℝ} {W : K → K → ℝ}
    (V : Type*) [Fintype V] [LinearOrder V] (σ : Equiv.Perm K)
    (h : (p ∘ σ, fun i j => W (σ i) (σ j)) ≠ (p, W)) :
    ¬ Function.Injective
      (fun θ : (K → ℝ) × (K → K → ℝ) =>
        sbmGraphWeight (V := V) θ.1 θ.2) := by
  intro hinj
  apply h
  refine hinj ?_
  exact sbmGraphWeight_relabel (V := V) (p := p) (W := W) σ

/-- Label swapping makes the admissible parameter-to-law map non-injective.

Identification holds at most modulo permutation of the latent classes.
-/
theorem not_injective_sbmGraphPMF_of_relabel_ne {K : Type*}
    [Fintype K] [DecidableEq K] {p : K → ℝ} {W : K → K → ℝ}
    (V : Type*) [Fintype V] [LinearOrder V]
    (σ : Equiv.Perm K) (h : SBMAdmissible p W)
    (hne : (p ∘ σ, fun i j => W (σ i) (σ j)) ≠ (p, W)) :
    ¬ Function.Injective
      (fun θ : {θ : (K → ℝ) × (K → K → ℝ) //
        SBMAdmissible θ.1 θ.2} =>
        sbmGraphPMF (V := V) θ.1.1 θ.1.2 θ.2) := by
  intro hinj
  apply hne
  have hpmf : sbmGraphPMF (V := V) (p ∘ σ) (fun i j => W (σ i) (σ j))
    (SBMAdmissible_relabel σ h) = sbmGraphPMF (V := V) p W h :=
    sbmGraphPMF_relabel (V := V) σ h
  have hsub : (⟨(p ∘ σ, fun i j => W (σ i) (σ j)),
    SBMAdmissible_relabel σ h⟩ :
    {θ : (K → ℝ) × (K → K → ℝ) // SBMAdmissible θ.1 θ.2}) =
    ⟨(p, W), h⟩ := hinj hpmf
  exact congrArg Subtype.val hsub

end

end MathlibExt.Probability.Networks
