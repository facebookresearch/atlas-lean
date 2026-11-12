/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import MathlibExt.Probability.Statistics.LinearModel.Sampling

/-!
# Gauss–Markov: the BLUE covariance ordering in the classical linear model

Fixed-design linear model `y = X β + ε` with `X : Matrix m k ℝ` of full column rank
(`IsUnit (Xᵀ * X)`), errors `ε` that are square-integrable with
`cov[ε i, ε j] = if i = j then σ² else 0`, integrable with mean zero.

* The covariance of a general linear estimator `A *ᵥ y` is `σ² • (A * Aᵀ)`
  (`covariance_mulVec_apply`), generalizing the landed `covariance_olsEstimator`
  (the `A = olsMatrix X` case) to arbitrary `A`.
* Unbiasedness for every `β` forces `A * X = 1` (`unbiased_mul_eq_one`).
* Hence every linear unbiased estimator has covariance at least that of OLS in
  positive-semidefinite order (`blue_covariance_minimality`), by Aitken's
  theorem at `V = 1` (which specializes to Gauss–Markov) scaled by `σ² ≥ 0`.

## Main results

* `covariance_mulVec_apply`, `unbiased_mul_eq_one`, `blue_covariance_minimality`.

Provenance: the proof bodies were drafted by Muse Code from pinned statements
and were independently checked with Codex before integration. The lane
repaired one corrupted identifier (a hallucinated token) in the test section's
`unfold` line, deleted an unused private `olsMatrix_eq` helper that
shadowed the landed `Sampling.olsMatrix_eq`, and changed one `simp` to
`simp only` (same lemma list) in `h_covB`, because the landed `@[simp]`
`olsMatrix_eq` otherwise rewrites `olsMatrix X` before
`covariance_mulVec_apply` can match.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix

/-- `MemLp` of a coordinate of `A *ᵥ ε`, from `MemLp` of each error coordinate. -/
private theorem memLp_mulVec_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {ε : Ω → m → ℝ} (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (A : Matrix k m ℝ) (a : k) :
    MemLp (fun ω => (A *ᵥ ε ω) a) 2 μ := by
  have h_each : ∀ i : m, MemLp (fun ω => A a i * ε ω i) 2 μ := by
    intro i
    have h := (hL2 i).const_mul (A a i)
    simpa [smul_eq_mul] using h
  have h_sum : MemLp (fun ω => ∑ i, A a i * ε ω i) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => h_each i)
  have h_eq : (fun ω => (A *ᵥ ε ω) a) = (fun ω => ∑ i, A a i * ε ω i) := by
    ext ω
    simp [Matrix.mulVec, dotProduct]
  rw [h_eq]
  exact h_sum

/-- Integrability of a coordinate of `A *ᵥ (c + ε)`, from integrability of each
error coordinate. The constant vector `c` is typically `X *ᵥ β`. -/
private theorem integrable_mulVec_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {ε : Ω → m → ℝ} (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (A : Matrix k m ℝ) (a : k) (c : m → ℝ) :
    Integrable (fun ω => (A *ᵥ (c + ε ω)) a) μ := by
  have h_each : ∀ i : m, Integrable (fun ω => A a i * (c i + ε ω i)) μ := by
    intro i
    have h_const : Integrable (fun _ : Ω => A a i * c i) μ := integrable_const _
    have h_var : Integrable (fun ω => A a i * ε ω i) μ := by
      have h := (hint i).const_mul (A a i)
      simpa [smul_eq_mul] using h
    have h_eq : (fun ω => A a i * (c i + ε ω i))
        = (fun _ : Ω => A a i * c i) + (fun ω => A a i * ε ω i) := by
      ext ω
      simp [mul_add, Pi.add_apply]
    rw [h_eq]
    exact h_const.add h_var
  have h_sum : Integrable (fun ω => ∑ i, A a i * (c i + ε ω i)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => h_each i)
  have h_eq : (fun ω => (A *ᵥ (c + ε ω)) a)
      = (fun ω => ∑ i, A a i * (c i + ε ω i)) := by
    ext ω
    simp [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [h_eq]
  exact h_sum

/-- **Covariance of a general linear estimator**: if the errors are square-integrable
with `cov[ε i, ε j] = if i = j then σ² else 0`, then for any matrix `A` the covariance
of `A *ᵥ (X *ᵥ β + ε)` is `σ² • (A * Aᵀ)`, entrywise. This generalizes the landed
`covariance_olsEstimator` (the `A = olsMatrix X` case) to arbitrary `A`. No mean-zero
hypothesis is needed: covariance is translation-invariant. -/
theorem covariance_mulVec_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (β : k → ℝ) {ε : Ω → m → ℝ} (σ : ℝ)
    (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = if i = j then σ ^ 2 else 0)
    (A : Matrix k m ℝ) (a b : k) :
    cov[fun ω => (A *ᵥ (X *ᵥ β + ε ω)) a, fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b; μ]
      = σ ^ 2 * (A * Aᵀ) a b := by
  have hL2A_a : MemLp (fun ω => (A *ᵥ ε ω) a) 2 μ := memLp_mulVec_apply hL2 A a
  have hL2A_b : MemLp (fun ω => (A *ᵥ ε ω) b) 2 μ := memLp_mulVec_apply hL2 A b
  have hL2a : ∀ i : m, MemLp (fun ω => A a i * ε ω i) 2 μ := by
    intro i
    have h := (hL2 i).const_mul (A a i)
    simpa [smul_eq_mul] using h
  have hL2b : ∀ j : m, MemLp (fun ω => A b j * ε ω j) 2 μ := by
    intro j
    have h := (hL2 j).const_mul (A b j)
    simpa [smul_eq_mul] using h
  have hL2_full_b : MemLp (fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b) 2 μ := by
    have h_const : MemLp (fun _ : Ω => (A *ᵥ (X *ᵥ β)) b) 2 μ := memLp_const _
    have h_eq : (fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b)
        = (fun _ : Ω => (A *ᵥ (X *ᵥ β)) b) + (fun ω => (A *ᵥ ε ω) b) := by
      ext ω
      have h_add : A *ᵥ (X *ᵥ β + ε ω) = A *ᵥ (X *ᵥ β) + A *ᵥ ε ω :=
        Matrix.mulVec_add _ _ _
      rw [h_add]
      rfl
    rw [h_eq]
    exact h_const.add hL2A_b
  have h_coord_a : (fun ω => (A *ᵥ (X *ᵥ β + ε ω)) a)
      = (fun ω => (A *ᵥ (X *ᵥ β)) a + (A *ᵥ ε ω) a) := by
    ext ω
    have h_add : A *ᵥ (X *ᵥ β + ε ω) = A *ᵥ (X *ᵥ β) + A *ᵥ ε ω :=
      Matrix.mulVec_add _ _ _
    rw [h_add]
    rfl
  have h_coord_b : (fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b)
      = (fun ω => (A *ᵥ (X *ᵥ β)) b + (A *ᵥ ε ω) b) := by
    ext ω
    have h_add : A *ᵥ (X *ᵥ β + ε ω) = A *ᵥ (X *ᵥ β) + A *ᵥ ε ω :=
      Matrix.mulVec_add _ _ _
    rw [h_add]
    rfl
  have h_sum_a : (fun ω => (A *ᵥ ε ω) a) = (fun ω => ∑ i, A a i * ε ω i) := by
    ext ω
    simp [Matrix.mulVec, dotProduct]
  have h_sum_b : (fun ω => (A *ᵥ ε ω) b) = (fun ω => ∑ j, A b j * ε ω j) := by
    ext ω
    simp [Matrix.mulVec, dotProduct]
  have hq : (1 : ENNReal) ≤ 2 := by norm_num
  have h_intA_a : Integrable (fun ω => (A *ᵥ ε ω) a) μ := MemLp.integrable hq hL2A_a
  have h_intA_b : Integrable (fun ω => (A *ᵥ ε ω) b) μ := MemLp.integrable hq hL2A_b
  have h_strip : cov[fun ω => (A *ᵥ (X *ᵥ β + ε ω)) a,
        fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b; μ]
      = cov[fun ω => (A *ᵥ ε ω) a, fun ω => (A *ᵥ ε ω) b; μ] := by
    rw [h_coord_a, h_coord_b,
      covariance_const_add_left h_intA_a _,
      covariance_const_add_right h_intA_b _]
  have h_bilin : cov[fun ω => (A *ᵥ ε ω) a, fun ω => (A *ᵥ ε ω) b; μ]
      = ∑ i, ∑ j, cov[fun ω => A a i * ε ω i, fun ω => A b j * ε ω j; μ] := by
    rw [h_sum_a, h_sum_b, covariance_fun_sum_fun_sum hL2a hL2b]
  have h_scale : ∀ i j : m, cov[fun ω => A a i * ε ω i, fun ω => A b j * ε ω j; μ]
      = A a i * A b j * cov[fun ω => ε ω i, fun ω => ε ω j; μ] := by
    intro i j
    rw [covariance_const_mul_left _, covariance_const_mul_right _]
    ring
  have h_inner : ∀ i : m, (∑ j, A a i * A b j * (if i = j then σ ^ 2 else 0))
      = A a i * A b i * σ ^ 2 := by
    intro i
    simp [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
  have h_mat : (A * Aᵀ) a b = ∑ i, A a i * A b i := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [h_strip, h_bilin]
  simp_rw [h_scale, hcov, h_inner]
  rw [h_mat, ← Finset.sum_mul, mul_comm]

/-- **Unbiasedness for every `β` forces `A * X = 1`**: if `A *ᵥ (X *ᵥ β + ε)` has
expectation `β` for every `β` and the errors are integrable with mean zero, then
`A * X = 1`. Take `β = Pi.single j 1` and read off column `j`. -/
theorem unbiased_mul_eq_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} {ε : Ω → m → ℝ}
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (A : Matrix k m ℝ)
    (hunb : ∀ β : k → ℝ, ∫ ω, A *ᵥ (X *ᵥ β + ε ω) ∂μ = β) :
    A * X = 1 := by
  have h_int_each : ∀ (i : k) (l : m) (β : k → ℝ),
      Integrable (fun ω => A i l * ((X *ᵥ β) l + ε ω l)) μ := by
    intro i l β
    have h_const : Integrable (fun _ : Ω => A i l * (X *ᵥ β) l) μ := integrable_const _
    have h_var : Integrable (fun ω => A i l * ε ω l) μ := by
      have h := (hint l).const_mul (A i l)
      simpa [smul_eq_mul] using h
    have h_eq : (fun ω => A i l * ((X *ᵥ β) l + ε ω l))
        = (fun _ : Ω => A i l * (X *ᵥ β) l) + (fun ω => A i l * ε ω l) := by
      ext ω
      simp [mul_add, Pi.add_apply]
    rw [h_eq]
    exact h_const.add h_var
  have h_int_full : ∀ (i : k) (β : k → ℝ),
      Integrable (fun ω => (A *ᵥ (X *ᵥ β + ε ω)) i) μ := by
    intro i β
    exact integrable_mulVec_apply hint A i (X *ᵥ β)
  ext i j
  set β : k → ℝ := Pi.single j 1 with hβ
  have h_unb := hunb β
  have h_coord : (∫ ω, A *ᵥ (X *ᵥ β + ε ω) ∂μ) i = β i := by rw [h_unb]
  have h_eval : (∫ ω, A *ᵥ (X *ᵥ β + ε ω) ∂μ) i
      = ∫ ω, (A *ᵥ (X *ᵥ β + ε ω)) i ∂μ :=
    eval_integral (fun i => h_int_full i β) i
  rw [h_eval] at h_coord
  have h_expand : (fun ω => (A *ᵥ (X *ᵥ β + ε ω)) i)
      = (fun ω => ∑ l, A i l * ((X *ᵥ β) l + ε ω l)) := by
    ext ω
    simp [Matrix.mulVec, dotProduct, Pi.add_apply]
  have h_forall : ∀ l ∈ (Finset.univ : Finset m),
      Integrable (fun ω => A i l * ((X *ᵥ β) l + ε ω l)) μ := by
    intro l _
    exact h_int_each i l β
  rw [h_expand, integral_finsetSum _ h_forall] at h_coord
  have h_each_int : ∀ l : m, (∫ ω, A i l * ((X *ᵥ β) l + ε ω l) ∂μ)
      = A i l * (X *ᵥ β) l := by
    intro l
    have hf : Integrable (fun _ : Ω => A i l * (X *ᵥ β) l) μ := integrable_const _
    have hg : Integrable (fun ω => A i l * ε ω l) μ := by
      have h := (hint l).const_mul (A i l)
      simpa [smul_eq_mul] using h
    have h1 : (fun ω => A i l * ((X *ᵥ β) l + ε ω l))
        = (fun ω => A i l * (X *ᵥ β) l + A i l * ε ω l) := by
      ext ω
      simp [mul_add]
    have h_var_eq : (∫ ω, A i l * ε ω l ∂μ) = A i l * (∫ ω, ε ω l ∂μ) :=
      integral_const_mul (A i l) (fun ω => ε ω l)
    have h_const_eq : (∫ _ : Ω, A i l * (X *ᵥ β) l ∂μ) = A i l * (X *ᵥ β) l := by
      simp [integral_const]
    rw [h1, integral_add hf hg, h_const_eq, h_var_eq, hmean l, mul_zero, add_zero]
  simp_rw [h_each_int] at h_coord
  have h_Xβ : ∀ l : m, (X *ᵥ β) l = X l j := by
    intro l
    have h_eq : (X *ᵥ β) l = ∑ j', X l j' * β j' := by
      simp [Matrix.mulVec, dotProduct]
    rw [h_eq, hβ]
    simp [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      eq_comm]
  simp_rw [h_Xβ] at h_coord
  have h_AX : (A * X) i j = ∑ l, A i l * X l j := by
    simp [Matrix.mul_apply]
  have h_one : (1 : Matrix k k ℝ) i j = β i := by
    simp [hβ, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [h_AX, h_one]
  exact h_coord

/-- **Gauss–Markov (BLUE)**: every estimator linear in the observations and unbiased
for every coefficient vector `β` has covariance at least that of OLS in
positive-semidefinite order. The two matrices are the entrywise covariance matrices
of `A *ᵥ y` and of `olsMatrix X *ᵥ y`; by `covariance_mulVec_apply` they equal
`σ² • (A * Aᵀ)` and `σ² • (B * Bᵀ)` with `B = olsMatrix X`. -/
theorem blue_covariance_minimality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X))
    (β : k → ℝ) {ε : Ω → m → ℝ} (σ : ℝ)
    (hL2 : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = if i = j then σ ^ 2 else 0)
    (hint : ∀ i, Integrable (fun ω => ε ω i) μ)
    (hmean : ∀ i, ∫ ω, ε ω i ∂μ = 0) (A : Matrix k m ℝ)
    (hunb : ∀ β' : k → ℝ, ∫ ω, A *ᵥ (X *ᵥ β' + ε ω) ∂μ = β') :
    ((Matrix.of fun a b => cov[fun ω => (A *ᵥ (X *ᵥ β + ε ω)) a,
        fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b; μ])
      - (Matrix.of fun a b => cov[fun ω => (olsMatrix X *ᵥ (X *ᵥ β + ε ω)) a,
        fun ω => (olsMatrix X *ᵥ (X *ᵥ β + ε ω)) b; μ])).PosSemidef := by
  have hAX : A * X = 1 := unbiased_mul_eq_one hint hmean A hunb
  have hV : (1 : Matrix m m ℝ).PosDef := Matrix.PosDef.one
  have hX1 : IsUnit (Xᵀ * (1 : Matrix m m ℝ)⁻¹ * X) := by
    simpa [inv_one, mul_one] using hX
  have hB : MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix X 1
      = olsMatrix X := rfl
  have h_aitken := MathlibExt.Probability.Statistics.GeneralizedLeastSquares.aitken
    hV hX1 A hAX
  have h_base : (A * Aᵀ - olsMatrix X * (olsMatrix X)ᵀ).PosSemidef := by
    simpa [mul_one, hB] using h_aitken
  have h_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
  have h_scaled := h_base.smul h_nonneg
  have h_covA : (Matrix.of fun a b => cov[fun ω => (A *ᵥ (X *ᵥ β + ε ω)) a,
        fun ω => (A *ᵥ (X *ᵥ β + ε ω)) b; μ]) = σ ^ 2 • (A * Aᵀ) := by
    ext a b
    simp [covariance_mulVec_apply β σ hL2 hcov A a b, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply]
  have h_covB : (Matrix.of fun a b => cov[fun ω => (olsMatrix X *ᵥ (X *ᵥ β + ε ω)) a,
        fun ω => (olsMatrix X *ᵥ (X *ᵥ β + ε ω)) b; μ])
      = σ ^ 2 • (olsMatrix X * (olsMatrix X)ᵀ) := by
    ext a b
    -- `simp only`: the landed `@[simp] olsMatrix_eq` would rewrite `olsMatrix X`
    -- before `covariance_mulVec_apply` can match, so the ambient simp set is off.
    simp only [covariance_mulVec_apply β σ hL2 hcov (olsMatrix X) a b, Matrix.smul_apply,
      smul_eq_mul, Matrix.of_apply]
  rw [h_covA, h_covB, ← smul_sub]
  exact h_scaled

end MathlibExt.Probability.Statistics.LinearModel
