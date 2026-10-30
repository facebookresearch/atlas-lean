/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# EM for Gaussian mixtures

The EM algorithm for a mixture of `K` isotropic Gaussians in `EuclideanSpace ℝ (Fin d)` (Bishop,
*Pattern Recognition and Machine Learning*, Section 9.2; Ng, *CS229 Lecture Notes*, "Mixtures of
Gaussians and the EM algorithm"), as an instance of the generic EM of
`LatentVariable/ExpectationMaximization.lean`. The component density is Mathlib's Gaussian: the
isotropic density `isoGaussPDF μ v` is the product of `ProbabilityTheory.gaussianPDFReal` over the
coordinates, with `log_isoGaussPDF` giving `-(d / 2) log (2 π v) - ‖x - μ‖² / (2 v)`.

Main results:

* `joint` (`π k N(x | μ k, σ k² I)`) on `ValidParams` (positive weights summing to one, positive
  variances); `resp`: **the E-step responsibilities are the posterior** `P(z = k | xₙ)`
  (`resp = posterior joint`, `resp_pos`, `sum_resp`).
* The M-step `mStep`: `π k' = N k / N` (`mass`), `μ k'` the responsibility-weighted mean
  (`newMean`), `σ k'² = S k / (d N k)` (`scatter`, `newVar`); it is valid on data that are not all
  equal (`NotAllEqual`, `mStep_valid`, `emStep`).
* `emQ_le_emStep`: **the M-step maximizes `Q(· | θ)`** over all valid parameters: `emQ_eq` splits
  `Q` into a weights term,
  maximized at `N k / N` by Gibbs' inequality (`sum_mass_mul_log_le`), and one term per component,
  maximized at the weighted mean (`sum_mul_norm_sub_sq`, the weighted form of
  `KMeans.sum_sq_eq`) and the variance update (`compTerm_le`).
* `logLik_le_emStep`: **each EM step does not decrease the log-likelihood**;
  `logLik_iterate_emStep_monotone`: the log-likelihood is monotone along the EM iterates.

Only the isotropic case (covariance `σ k² I`) is proved; full covariances are not treated.

## Relation to `FormalizedTextbooks`

`FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/Ch24.lean` has mixing
weights (`MixWeights`, the conditions of `Params.Valid` on `weight`) and assumes EM's monotonicity
(`EMMonotone`), proved here for Gaussian mixtures by `logLik_iterate_emStep_monotone`.
`FormalizedTextbooks/HighDimensionalProbability/Chapter04/Section07/GaussianMixtureModel.lean` gives
the law of the symmetric two-component mixture; no bridge is provided.

## Cost model

No running-time model: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.GaussianMixture

open Real NNReal ProbabilityTheory
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

variable {d K N : ℕ}

/-! ## The isotropic Gaussian density -/

/-- The isotropic Gaussian density `N(x | μ, v I)` on `EuclideanSpace ℝ (Fin d)`: the product of
Mathlib's one-dimensional densities `gaussianPDFReal` over the coordinates. -/
noncomputable def isoGaussPDF (μ : EuclideanSpace ℝ (Fin d)) (v : ℝ≥0)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, gaussianPDFReal (μ i) v (x i)

theorem isoGaussPDF_pos (μ : EuclideanSpace ℝ (Fin d)) {v : ℝ≥0} (hv : v ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : 0 < isoGaussPDF μ v x :=
  Finset.prod_pos fun _ _ => gaussianPDFReal_pos _ _ _ hv

/-- The log-density: `log N(x | μ, v I) = -(d / 2) log (2 π v) - ‖x - μ‖² / (2 v)`. -/
theorem log_isoGaussPDF (μ : EuclideanSpace ℝ (Fin d)) {v : ℝ≥0} (hv : v ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    log (isoGaussPDF μ v x) = -(d / 2) * log (2 * π * v) - ‖x - μ‖ ^ 2 / (2 * v) := by
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (by exact_mod_cast hv))
  have h2 : 0 < 2 * π * (v : ℝ) := by positivity
  rw [isoGaussPDF, log_prod (fun i _ => (gaussianPDFReal_pos _ _ _ hv).ne'),
    EuclideanSpace.real_norm_sq_eq]
  have hterm : ∀ i, log (gaussianPDFReal (μ i) v (x i)) =
      -(1 / 2) * log (2 * π * v) - (x i - μ i) ^ 2 / (2 * v) := by
    intro i
    rw [gaussianPDFReal, log_mul (inv_pos.2 (sqrt_pos.2 h2)).ne' (exp_pos _).ne', log_inv,
      log_exp, log_sqrt h2.le]
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, PiLp.sub_apply, Finset.sum_div]
  ring

/-! ## The mixture model -/

/-- Parameters of a `K`-component isotropic Gaussian mixture in `d` dimensions: mixing weights,
means and variances. -/
structure Params (d K : ℕ) where
  /-- The mixing weights `π k`. -/
  weight : Fin K → ℝ
  /-- The component means `μ k`. -/
  mean : Fin K → EuclideanSpace ℝ (Fin d)
  /-- The component variances `σ k²` (isotropic: covariance `σ k² I`). -/
  var : Fin K → ℝ≥0

/-- Valid parameters: positive weights summing to one, positive variances. -/
structure Params.Valid (θ : Params d K) : Prop where
  weight_pos : ∀ k, 0 < θ.weight k
  weight_sum : ∑ k, θ.weight k = 1
  var_ne_zero : ∀ k, θ.var k ≠ 0

/-- The valid parameters, the parameter space of EM. -/
abbrev ValidParams (d K : ℕ) := {θ : Params d K // θ.Valid}

/-- The joint density `p_θ(x, k) = π k N(x | μ k, σ k² I)`. -/
noncomputable def joint (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  θ.1.weight k * isoGaussPDF (θ.1.mean k) (θ.1.var k) x

theorem joint_pos (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    0 < joint θ x k :=
  mul_pos (θ.2.weight_pos k) (isoGaussPDF_pos _ (θ.2.var_ne_zero k) x)

/-- The mixture density `p_θ(x) = ∑ k, π k N(x | μ k, σ k² I)`. -/
theorem marginal_joint (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) :
    marginal joint θ x = ∑ k, θ.1.weight k * isoGaussPDF (θ.1.mean k) (θ.1.var k) x := rfl

/-- The responsibilities `r n k = P(z = k | xₙ)` (the E-step): the posterior of the mixture. -/
noncomputable def resp (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  posterior joint θ x k

theorem resp_pos (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    0 < resp θ x k :=
  div_pos (joint_pos θ x k) (Finset.sum_pos (fun k _ => joint_pos θ x k) ⟨k, Finset.mem_univ k⟩)

/-- Valid parameters have at least one component. -/
theorem nonempty_of_valid (θ : ValidParams d K) : Nonempty (Fin K) := by
  by_contra h
  have : IsEmpty (Fin K) := not_nonempty_iff.1 h
  have := θ.2.weight_sum
  simp at this

theorem sum_resp (θ : ValidParams d K) (x : EuclideanSpace ℝ (Fin d)) : ∑ k, resp θ x k = 1 := by
  have := nonempty_of_valid θ
  exact (isDist_posterior (fun θ x k => joint_pos θ x k) θ x).2

/-! ## The M-step -/

variable (xs : Fin N → EuclideanSpace ℝ (Fin d))

/-- The effective number of points of component `k`, `N k = ∑ n, r n k`. -/
noncomputable def mass (θ : ValidParams d K) (k : Fin K) : ℝ := ∑ n, resp θ (xs n) k

/-- The responsibility-weighted mean `μ k' = (∑ n, r n k xₙ) / N k`. -/
noncomputable def newMean (θ : ValidParams d K) (k : Fin K) : EuclideanSpace ℝ (Fin d) :=
  (mass xs θ k)⁻¹ • ∑ n, resp θ (xs n) k • xs n

/-- The responsibility-weighted scatter `S k = ∑ n, r n k ‖xₙ - μ k'‖²`. -/
noncomputable def scatter (θ : ValidParams d K) (k : Fin K) : ℝ :=
  ∑ n, resp θ (xs n) k * ‖xs n - newMean xs θ k‖ ^ 2

/-- The isotropic variance update `σ k'² = S k / (d N k)`. -/
noncomputable def newVar (θ : ValidParams d K) (k : Fin K) : ℝ := scatter xs θ k / (d * mass xs θ k)

/-- The M-step: `π k' = N k / N`, `μ k'` the weighted mean, `σ k'² = S k / (d N k)`. -/
noncomputable def mStep (θ : ValidParams d K) : Params d K where
  weight k := mass xs θ k / N
  mean := newMean xs θ
  var k := (newVar xs θ k).toNNReal

/-! ## Weighted means -/

/-- **The weighted centroid decomposition**: `∑ w ‖x - c‖² = ∑ w ‖x - m‖² + W ‖m - c‖²` for
`m = W⁻¹ ∑ w x`, `W = ∑ w ≠ 0` (the weighted version of `KMeans.sum_sq_eq`). When `W > 0` the
weighted mean is a minimizer (`sum_mul_norm_sub_sq_mean_le`). -/
theorem sum_mul_norm_sub_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (x : ι → F) (hW : ∑ i ∈ s, w i ≠ 0) (c : F) :
    ∑ i ∈ s, w i * ‖x i - c‖ ^ 2 =
      ∑ i ∈ s, w i * ‖x i - (∑ i ∈ s, w i)⁻¹ • ∑ i ∈ s, w i • x i‖ ^ 2 +
        (∑ i ∈ s, w i) * ‖(∑ i ∈ s, w i)⁻¹ • ∑ i ∈ s, w i • x i - c‖ ^ 2 := by
  set W := ∑ i ∈ s, w i with hWdef
  set m := W⁻¹ • ∑ i ∈ s, w i • x i with hm
  have hWm : W • m = ∑ i ∈ s, w i • x i := by rw [hm, smul_smul, mul_inv_cancel₀ hW, one_smul]
  have hcross : ∑ i ∈ s, w i * inner ℝ (x i - m) (m - c) = 0 := by
    have : ∑ i ∈ s, w i * inner ℝ (x i - m) (m - c) =
        inner ℝ (∑ i ∈ s, w i • x i - W • m) (m - c) := by
      rw [inner_sub_left, sum_inner, inner_smul_left, hWdef, conj_trivial, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [inner_sub_left, inner_smul_left, conj_trivial, mul_sub]
    rw [this, hWm, sub_self, inner_zero_left]
  have hexp : ∀ i, ‖x i - c‖ ^ 2 = ‖x i - m‖ ^ 2 + 2 * inner ℝ (x i - m) (m - c) + ‖m - c‖ ^ 2 :=
    fun i => by rw [← norm_add_sq_real, sub_add_sub_cancel]
  simp only [hexp, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [show ∑ i ∈ s, w i * (2 * inner ℝ (x i - m) (m - c)) =
      2 * ∑ i ∈ s, w i * inner ℝ (x i - m) (m - c) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hcross]
  ring

/-- **With positive total weight, the weighted mean minimizes the weighted sum of squared
distances.** -/
theorem sum_mul_norm_sub_sq_mean_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hW : 0 < ∑ i ∈ s, w i)
    (x : ι → F) (c : F) :
    ∑ i ∈ s, w i * ‖x i - (∑ i ∈ s, w i)⁻¹ • ∑ i ∈ s, w i • x i‖ ^ 2 ≤
      ∑ i ∈ s, w i * ‖x i - c‖ ^ 2 := by
  rw [sum_mul_norm_sub_sq s w x hW.ne' c]
  have : 0 ≤ (∑ i ∈ s, w i) * ‖(∑ i ∈ s, w i)⁻¹ • ∑ i ∈ s, w i • x i - c‖ ^ 2 := by positivity
  linarith

/-! ## The M-step is valid -/

variable {xs}

/-- Data that are not all equal. -/
def NotAllEqual (xs : Fin N → EuclideanSpace ℝ (Fin d)) : Prop := ∃ n n', xs n ≠ xs n'

theorem NotAllEqual.pos (hx : NotAllEqual xs) : 0 < N := by
  obtain ⟨n, -, -⟩ := hx
  exact Fin.pos n

theorem NotAllEqual.dim_pos (hx : NotAllEqual xs) : 0 < d := by
  obtain ⟨_, _, hne⟩ := hx
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exact absurd (by ext i; exact i.elim0) hne
  · exact h

theorem mass_pos (hN : 0 < N) (θ : ValidParams d K) (k : Fin K) : 0 < mass xs θ k :=
  Finset.sum_pos (fun _ _ => resp_pos θ _ k) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

theorem sum_mass (θ : ValidParams d K) : ∑ k, mass xs θ k = N := by
  simp only [mass]
  rw [Finset.sum_comm]
  simp [sum_resp]

theorem scatter_pos (hx : NotAllEqual xs) (θ : ValidParams d K) (k : Fin K) :
    0 < scatter xs θ k := by
  obtain ⟨n, n', hne⟩ := hx
  have : xs n ≠ newMean xs θ k ∨ xs n' ≠ newMean xs θ k := by
    by_contra h
    push Not at h
    exact hne (h.1.trans h.2.symm)
  have hterm : ∀ m, 0 ≤ resp θ (xs m) k * ‖xs m - newMean xs θ k‖ ^ 2 :=
    fun m => mul_nonneg (resp_pos θ _ k).le (sq_nonneg _)
  have hpos : ∀ m, xs m ≠ newMean xs θ k → 0 < resp θ (xs m) k * ‖xs m - newMean xs θ k‖ ^ 2 :=
    fun m hm => mul_pos (resp_pos θ _ k) (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hm)) 2)
  rcases this with h | h
  · exact lt_of_lt_of_le (hpos n h)
      (Finset.single_le_sum (fun m _ => hterm m) (Finset.mem_univ n))
  · exact lt_of_lt_of_le (hpos n' h)
      (Finset.single_le_sum (fun m _ => hterm m) (Finset.mem_univ n'))

theorem newVar_pos (hx : NotAllEqual xs) (θ : ValidParams d K) (k : Fin K) :
    0 < newVar xs θ k :=
  div_pos (scatter_pos hx θ k) (mul_pos (by exact_mod_cast hx.dim_pos) (mass_pos hx.pos θ k))

theorem mStep_valid (hx : NotAllEqual xs) (θ : ValidParams d K) : (mStep xs θ).Valid where
  weight_pos k := div_pos (mass_pos hx.pos θ k) (by exact_mod_cast hx.pos)
  weight_sum := by
    simp only [mStep]
    rw [← Finset.sum_div, sum_mass, div_self (by exact_mod_cast hx.pos.ne')]
  var_ne_zero k := by
    simp only [mStep, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact newVar_pos hx θ k

variable (xs) in
/-- One EM step for the Gaussian mixture (E-step then M-step), on data that are not all equal. -/
noncomputable def emStep (hx : NotAllEqual xs) (θ : ValidParams d K) : ValidParams d K :=
  ⟨mStep xs θ, mStep_valid hx θ⟩

/-! ## The M-step maximizes `Q` -/

variable (xs) in
/-- The component term of `Q`: `∑ n, r n k log N(xₙ | μ, v I)`, written out for `v > 0`. -/
noncomputable def compTerm (θ : ValidParams d K) (k : Fin K) (μ : EuclideanSpace ℝ (Fin d))
    (v : ℝ) : ℝ :=
  ∑ n, resp θ (xs n) k * (-(d / 2) * log (2 * π * v) - ‖xs n - μ‖ ^ 2 / (2 * v))

variable (xs) in
/-- `Q(θ' | θ)` splits into a weights term and one term per component. -/
theorem emQ_eq (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ = ∑ k, (mass xs θ k * log (θ'.1.weight k) +
      compTerm xs θ k (θ'.1.mean k) (θ'.1.var k)) := by
  have hlog : ∀ n k, log (joint θ' (xs n) k) = log (θ'.1.weight k) +
      (-(d / 2) * log (2 * π * (θ'.1.var k)) - ‖xs n - θ'.1.mean k‖ ^ 2 / (2 * (θ'.1.var k))) := by
    intro n k
    rw [joint, log_mul (θ'.2.weight_pos k).ne' (isoGaussPDF_pos _ (θ'.2.var_ne_zero k) _).ne',
      log_isoGaussPDF _ (θ'.2.var_ne_zero k)]
  simp only [emQ, hlog, mul_add, Finset.sum_add_distrib, mass, compTerm]
  rw [Finset.sum_comm (f := fun n k => posterior joint θ (xs n) k * log (θ'.1.weight k)),
    Finset.sum_comm (f := fun n k => posterior joint θ (xs n) k * (-(d / 2) *
      log (2 * π * (θ'.1.var k)) - ‖xs n - θ'.1.mean k‖ ^ 2 / (2 * (θ'.1.var k))))]
  simp only [Finset.sum_mul, resp]

/-- **The weight update maximizes the weights term**: over all mixing weights,
`∑ k, N k log π k` is largest at `π k = N k / N` (Gibbs' inequality). -/
theorem sum_mass_mul_log_le (hN0 : 0 < N) (θ : ValidParams d K) {w : Fin K → ℝ}
    (hw : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1) :
    ∑ k, mass xs θ k * log (w k) ≤ ∑ k, mass xs θ k * log (mass xs θ k / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq : IsDist fun k => mass xs θ k / N :=
    ⟨fun k => (div_pos (mass_pos hN0 θ k) hN).le, by
      rw [← Finset.sum_div, sum_mass, div_self hN.ne']⟩
  have h := sum_mul_log_sub_le hw hq
  rw [hsum, log_one] at h
  have heq : ∑ k, mass xs θ k * log (w k) - ∑ k, mass xs θ k * log (mass xs θ k / N) =
      N * ∑ k, mass xs θ k / N * (log (w k) - log (mass xs θ k / N)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have : N * ∑ k, mass xs θ k / N * (log (w k) - log (mass xs θ k / N)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hN.le h
  linarith

theorem compTerm_eq (θ : ValidParams d K) (k : Fin K) (μ : EuclideanSpace ℝ (Fin d)) (v : ℝ) :
    compTerm xs θ k μ v = -(d / 2) * log (2 * π * v) * mass xs θ k -
      (∑ n, resp θ (xs n) k * ‖xs n - μ‖ ^ 2) / (2 * v) := by
  simp only [compTerm, mass, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by ring
  · exact Finset.sum_congr rfl fun n _ => by ring

/-- **The mean and variance updates maximize each component term**: over all means `μ` and
variances `v > 0`, `∑ n, r n k log N(xₙ | μ, v I)` is largest at the weighted mean and
`v = S k / (d N k)`. -/
theorem compTerm_le (hx : NotAllEqual xs) (θ : ValidParams d K) (k : Fin K)
    (μ : EuclideanSpace ℝ (Fin d)) {v : ℝ} (hv : 0 < v) :
    compTerm xs θ k μ v ≤ compTerm xs θ k (newMean xs θ k) (newVar xs θ k) := by
  have hM : 0 < mass xs θ k := mass_pos hx.pos θ k
  have hS := scatter_pos hx θ k
  have hd : (0 : ℝ) < d := by exact_mod_cast hx.dim_pos
  have hv' := newVar_pos hx θ k
  set M := mass xs θ k with hMdef
  set S := scatter xs θ k with hSdef
  set v' := newVar xs θ k with hv'def
  -- the weighted decomposition
  have hdec := sum_mul_norm_sub_sq Finset.univ (fun n => resp θ (xs n) k) xs
    (hM.ne' : mass xs θ k ≠ 0) μ
  have hdec' : ∑ n, resp θ (xs n) k * ‖xs n - μ‖ ^ 2 = S + M * ‖newMean xs θ k - μ‖ ^ 2 := hdec
  have hS' : ∑ n, resp θ (xs n) k * ‖xs n - newMean xs θ k‖ ^ 2 = S := rfl
  rw [compTerm_eq, compTerm_eq, hdec', hS']
  -- `S = d M v'`
  have hSv : S = d * M * v' := by
    rw [hv'def, newVar, ← hSdef, ← hMdef]
    field_simp
  have hlog := log_le_sub_one_of_pos (div_pos hv' hv)
  rw [log_div hv'.ne' hv.ne'] at hlog
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [log_mul h2π.ne' hv.ne', log_mul h2π.ne' hv'.ne']
  have hmv : 0 ≤ M * ‖newMean xs θ k - μ‖ ^ 2 / (2 * v) := by positivity
  have key : d * M / 2 * (log v' - log v) ≤ d * M / 2 * (v' / v - 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have e1 : (S + M * ‖newMean xs θ k - μ‖ ^ 2) / (2 * v) =
      d * M / 2 * (v' / v) + M * ‖newMean xs θ k - μ‖ ^ 2 / (2 * v) := by
    rw [hSv]; field_simp
  have e2 : S / (2 * v') = d * M / 2 := by
    rw [hSv]; field_simp
  rw [e1, e2]
  nlinarith

variable (xs) in
/-- **The M-step maximizes `Q(· | θ)`**: no valid parameter `θ'` has a larger `Q(θ' | θ)` than the
EM update `emStep xs hx θ`. -/
theorem emQ_le_emStep (hx : NotAllEqual xs) (θ' θ : ValidParams d K) :
    emQ joint xs θ' θ ≤ emQ joint xs (emStep xs hx θ) θ := by
  rw [emQ_eq, emQ_eq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine add_le_add (sum_mass_mul_log_le hx.pos θ θ'.2.weight_pos θ'.2.weight_sum) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have hv : (0 : ℝ) < θ'.1.var k := lt_of_le_of_ne (θ'.1.var k).2
    (Ne.symm (by exact_mod_cast θ'.2.var_ne_zero k))
  have hvar : ((emStep xs hx θ).1.var k : ℝ) = newVar xs θ k :=
    Real.coe_toNNReal _ (newVar_pos hx θ k).le
  rw [hvar]
  exact compTerm_le hx θ k _ hv

variable (xs) in
/-- **Each EM step for the Gaussian mixture does not decrease the log-likelihood** (from the EM
theorem `logLik_le_of_emQ_le`). -/
theorem logLik_le_emStep (hx : NotAllEqual xs) (θ : ValidParams d K) :
    logLik joint xs θ ≤ logLik joint xs (emStep xs hx θ) := by
  have := nonempty_of_valid θ
  exact logLik_le_of_emQ_le (fun θ x k => joint_pos θ x k) xs (emQ_le_emStep xs hx θ θ)

variable (xs) in
/-- **The log-likelihood is monotone along the EM iterates** of the Gaussian mixture. -/
theorem logLik_iterate_emStep_monotone (hx : NotAllEqual xs) (θ₀ : ValidParams d K) :
    Monotone fun t => logLik joint xs ((emStep xs hx)^[t] θ₀) := by
  have := nonempty_of_valid θ₀
  exact logLik_iterate_monotone (fun θ x k => joint_pos θ x k) xs (fun θ => emQ_le_emStep xs hx θ θ)
    θ₀

end Cslib.MachineLearning.LatentVariable.GaussianMixture
