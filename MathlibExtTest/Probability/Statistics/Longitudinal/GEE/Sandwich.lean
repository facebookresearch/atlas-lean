/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.Sandwich
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for GEE asymptotics and the sandwich covariance

* Smoke test: `sandwichCovariance 1 1 = 1`.
* Scalar sandwich: `sandwichCovariance (c • 1) (d • 1) = (d / c²) • 1` for `c ≠ 0`.
* A concrete independent-cluster model, the Gaussian random-intercept model
  `Y i j = β₀ + b i + e i j`, `j = 1, 2`, with `b i, e i 1, e i 2` independent standard normals,
  fitted by GEE with identity link and working independence (`D i = (1, 1)ᵀ`, `V i = I`). The
  estimator is the grand mean, the bread is `A = -2`, the meat is `B = Var(U i β₀) = 6`, and the
  sandwich is `3 / 2 = Var((Y i 1 + Y i 2) / 2)`, whereas the working-independence model-based
  variance would be `Var(Y i j) / 2 = 1`. Every hypothesis of
  `tendstoInDistribution_sqrt_smul_sub_sandwich` is verified, including the cluster Lindeberg
  condition (via `lindebergConditionTriangular_inner_of_identDistrib`), and the model is realized
  on an infinite product space.
* Boundary: a singular bread. With `A = 0`, deterministic bread estimators `Ahat n → 0` and meat
  `1` give sandwiches `(n + 1)² • 1` that do not converge to `sandwichCovariance 0 1 = 0`: the
  invertibility hypothesis of `tendstoInMeasure_sandwichCovariance` cannot be dropped.
* Boundary: Lindeberg failure. Exploding cluster scores `U k = 2 ^ k` violate the cluster
  Lindeberg condition, so the hypothesis is not vacuous.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ProbabilityTheory.GEE Filter Finset RealInnerProductSpace
open scoped Real Topology

namespace GEESandwichTest

/-! ### Smoke test -/

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    sandwichCovariance (1 : E →L[ℝ] E) 1 = 1 := by
  rw [sandwichCovariance, Ring.inverse_one, mul_one, one_mul, ContinuousLinearMap.one_def,
    ContinuousLinearMap.adjoint_id]

/-! ### Scalar sandwich -/

/-- In one dimension the sandwich of `c • 1` and `d • 1` is `d / c²`. -/
theorem sandwichCovariance_smul_one (c d : ℝ) (hc : c ≠ 0) :
    sandwichCovariance (c • (1 : ℝ →L[ℝ] ℝ)) (d • 1) = (d / c ^ 2) • 1 := by
  have hinv : Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ)) = c⁻¹ • 1 := by
    have hu : IsUnit (c • (1 : ℝ →L[ℝ] ℝ)) :=
      ⟨⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc, one_smul],
        by rw [smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hc, one_smul]⟩, rfl⟩
    have h1 : Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ)) * (c • 1) = 1 := Ring.inverse_mul_cancel _ hu
    calc Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ))
        = Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ)) * ((c • 1) * (c⁻¹ • 1)) := by
          rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc, one_smul, mul_one]
      _ = c⁻¹ • 1 := by rw [← mul_assoc, h1, one_mul]
  have hadj : ContinuousLinearMap.adjoint (c⁻¹ • (1 : ℝ →L[ℝ] ℝ)) = c⁻¹ • 1 := by
    rw [map_smulₛₗ, ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
    simp
  rw [sandwichCovariance, hinv, hadj]
  ext
  simp
  field_simp

/-! ### The Gaussian random-intercept model under working independence -/

/-- The latent standard Gaussian vector of a cluster: `(b, e 1, e 2)`. -/
abbrev F := EuclideanSpace ℝ (Fin 3)

/-- The loading vector of the cluster score: `U i β₀ = 2 b + e 1 + e 2 = ⟪ξ, s⟫`. -/
noncomputable def s : F := !₂[2, 1, 1]

theorem inner_s (x : F) : ⟪x, s⟫ = 2 * x 0 + x 1 + x 2 := by
  simp [s, PiLp.inner_apply, Fin.sum_univ_three]

theorem norm_s_sq : ‖s‖ ^ 2 = 6 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [s, Fin.sum_univ_three]
  norm_num

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Response `j ∈ {1, 2}` of cluster `i`: `Y i j = β₀ + b i + e i j`, with
`(b i, e i 1, e i 2) = ξ i`. -/
noncomputable def Y (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (j : Fin 3) (ω : Ω) : ℝ :=
  β₀ + ξ i ω 0 + ξ i ω j

/-- The GEE score of cluster `i` for the identity link under working independence:
`D iᵀ V i⁻¹ (Y i - μ i β) = (Y i 1 - β) + (Y i 2 - β)`. -/
noncomputable def U (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (β : ℝ) (ω : Ω) : ℝ :=
  (Y β₀ ξ i 1 ω - β) + (Y β₀ ξ i 2 ω - β)

/-- The GEE estimator: the grand mean `∑_{i<n} (Y i 1 + Y i 2) / (2 n)`. -/
noncomputable def βhat (β₀ : ℝ) (ξ : ℕ → Ω → F) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ range n, (Y β₀ ξ i 1 ω + Y β₀ ξ i 2 ω)) / (2 * n)

theorem U_eq (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (β : ℝ) (ω : Ω) :
    U β₀ ξ i β ω = ⟪ξ i ω, s⟫ + 2 * (β₀ - β) := by
  rw [inner_s, U, Y, Y]
  ring

theorem U_self (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) :
    U β₀ ξ i β₀ = fun ω ↦ ⟪ξ i ω, s⟫ := by
  ext ω
  rw [U_eq, sub_self, mul_zero, add_zero]

theorem sum_U (β₀ : ℝ) (ξ : ℕ → Ω → F) (n : ℕ) (β : ℝ) (ω : Ω) :
    ∑ i ∈ range n, U β₀ ξ i β ω =
      ∑ i ∈ range n, (Y β₀ ξ i 1 ω + Y β₀ ξ i 2 ω) - 2 * n * β := by
  simp only [U]
  rw [show 2 * (n : ℝ) * β = ∑ _i ∈ range n, 2 * β by simp; ring, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The grand mean solves the GEE estimating equation exactly, for every `n`. -/
theorem sum_U_βhat (β₀ : ℝ) (ξ : ℕ → Ω → F) (n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, U β₀ ξ i (βhat β₀ ξ n ω) ω = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sum_U, βhat]
  field_simp
  ring

/-- The bread of the model: `A = E[∂U/∂β] = -2`. -/
noncomputable def A : ℝ →L[ℝ] ℝ := (-2 : ℝ) • 1

/-- The meat of the model: `B = E[U²] = Var(2 b + e 1 + e 2) = 6`. -/
noncomputable def B : ℝ →L[ℝ] ℝ := (6 : ℝ) • 1

theorem isUnit_A : IsUnit A :=
  ⟨⟨(-2 : ℝ) • 1, (-2 : ℝ)⁻¹ • 1, by rw [smul_mul_smul_comm, mul_one]; norm_num,
    by rw [smul_mul_smul_comm, mul_one]; norm_num⟩, rfl⟩

/-- **The sandwich of the random-intercept model is `3 / 2`**, the variance of a cluster mean
`(Y i 1 + Y i 2) / 2 = β₀ + b i + (e i 1 + e i 2) / 2`; the working-independence model-based
variance `Var(Y i j) / 2 = 1` understates it. -/
theorem sandwichCovariance_A_B : sandwichCovariance A B = (3 / 2 : ℝ) • 1 := by
  rw [A, B, sandwichCovariance_smul_one _ _ (by norm_num)]
  norm_num

variable {ξ : ℕ → Ω → F}

omit [IsProbabilityMeasure P] in
theorem integral_inner_s (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (k : ℕ) :
    ∫ ω, ⟪ξ k ω, s⟫ ∂P = 0 := by
  have h := (hlaw k).integral_comp (f := fun x : F ↦ ⟪x, s⟫)
    (continuous_id.inner continuous_const).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, ← integral_strongDual_stdGaussian (E := F) (innerSL ℝ s)]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [real_inner_comm])

omit [IsProbabilityMeasure P] in
theorem integral_inner_s_sq (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (k : ℕ) :
    ∫ ω, ⟪ξ k ω, s⟫ ^ 2 ∂P = 6 := by
  have h := (hlaw k).integral_comp (f := fun x : F ↦ ⟪x, s⟫ ^ 2)
    ((continuous_id.inner continuous_const).pow 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  have hvar := variance_dual_stdGaussian (E := F) (innerSL ℝ s)
  rw [innerSL_apply_norm, norm_s_sq,
    variance_of_integral_eq_zero (innerSL ℝ s).continuous.aemeasurable
      (integral_strongDual_stdGaussian _)] at hvar
  rw [← hvar]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [real_inner_comm])

theorem inner_real (x t : ℝ) : ⟪x, t⟫ = x * t := by simp [mul_comm]

omit [IsProbabilityMeasure P] in
theorem measurable_βhat (hξ : ∀ i, Measurable (ξ i)) (β₀ : ℝ) (n : ℕ) :
    Measurable (βhat β₀ ξ n) := by
  have hc : ∀ j : Fin 3, Measurable fun x : F ↦ x j := fun j ↦
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable
  unfold βhat Y
  exact (Finset.measurable_sum _ fun i _ ↦
    ((measurable_const.add ((hc 0).comp (hξ i))).add ((hc 1).comp (hξ i))).add
      ((measurable_const.add ((hc 0).comp (hξ i))).add ((hc 2).comp (hξ i)))).div_const _

/-- **Asymptotic normality of the GEE estimator in the random-intercept model, with the sandwich
variance `3 / 2`.** Every hypothesis of `tendstoInDistribution_sqrt_smul_sub_sandwich` is
discharged: independence and laws of the clusters, unbiasedness, second moments, the meat
`B = 6`, the cluster Lindeberg condition, the exact root, and the exact linearization with bread
`A = -2`. -/
theorem tendstoInDistribution_randomIntercept (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) (β₀ : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat β₀ ξ n ω - β₀)) atTop id
      (fun _ ↦ P) (gaussianReal 0 (3 / 2)) := by
  have hinner : Measurable fun x : F ↦ ⟪x, s⟫ := (continuous_id.inner continuous_const).measurable
  have hL2 : ∀ k, MemLp (U β₀ ξ k β₀) 2 P := fun k ↦ by
    rw [U_self]
    exact (hlaw k).memLp_comp (MemLp.inner_const IsGaussian.memLp_two_id s)
  have hident : ∀ k, IdentDistrib (U β₀ ξ k β₀) (U β₀ ξ 0 β₀) P P := fun k ↦ by
    rw [U_self, U_self]
    exact (IdentDistrib.mk (hlaw k).aemeasurable (hlaw 0).aemeasurable
      ((hlaw k).map_eq.trans (hlaw 0).map_eq.symm)).comp hinner
  have hrem : ∀ n : ℕ, 1 ≤ n → ∀ ω, (n : ℝ)⁻¹ • (∑ i ∈ range n, U β₀ ξ i (βhat β₀ ξ n ω) ω -
      ∑ i ∈ range n, U β₀ ξ i β₀ ω) - A (βhat β₀ ξ n ω - β₀) = 0 := by
    intro n hn ω
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    rw [sum_U, sum_U]
    simp only [A, smul_apply, one_apply_eq_self,
      smul_eq_mul]
    field_simp
    ring
  refine tendstoInDistribution_sqrt_smul_sub_sandwich (A := A) (B := B) isUnit_A
    (fun k ↦ by rw [U_self]; exact hinner.comp (hξ k))
    (by simp_rw [U_self]; exact hind.comp (fun _ x ↦ ⟪x, s⟫) fun _ ↦ hinner)
    (fun k ↦ by rw [U_self]; exact integral_inner_s hlaw k) hL2 (fun t ↦ ?_) (fun t ht ↦ ?_)
    (fun t ↦ lindebergConditionTriangular_inner_of_identDistrib hident (hL2 0) t)
    (fun n ↦ (measurable_βhat hξ β₀ n).aemeasurable) ?_ (fun ε hε ↦ ?_) aemeasurable_id
    (fun t ↦ ?_)
  · -- the meat: `n⁻¹ ∑_{k<n} E[(U k β₀ t)²] = 6 t²` for `n ≥ 1`
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    simp only [U_self, inner_real, mul_pow, integral_mul_const, integral_inner_s_sq hlaw,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, B, smul_apply,
      one_apply_eq_self, smul_eq_mul]
    field_simp
  · simp only [inner_real, B, smul_apply,
      one_apply_eq_self, smul_eq_mul]
    have := mul_self_pos.2 ht
    nlinarith
  · simp [sum_U_βhat]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).symm
    simp only [Set.mem_ofPred_eq] at hω
    rw [hrem n hn ω, norm_zero] at hω
    exact absurd hω (not_lt.2 (by positivity))
  · rw [sandwichCovariance_A_B]
    refine ⟨(continuous_id.inner continuous_const).aemeasurable, ?_⟩
    simp only [id, inner_real, smul_apply,
      one_apply_eq_self, smul_eq_mul]
    rw [gaussianReal_map_mul_const, mul_zero]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    rw [Real.coe_toNNReal _ (by nlinarith [mul_self_nonneg t])]
    norm_num
    ring

/-- The random-intercept model is realized by i.i.d. standard Gaussian vectors on the infinite
product space `ℕ → F`. -/
example (β₀ : ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → F) ↦ √n • (βhat β₀ (fun i ω ↦ ω i) n ω - β₀)) atTop id
      (fun _ ↦ Measure.infinitePi fun _ ↦ stdGaussian F) (gaussianReal 0 (3 / 2)) :=
  tendstoInDistribution_randomIntercept (fun i ↦ measurable_pi_apply i)
    (fun i ↦ (measurePreserving_eval_infinitePi (fun _ ↦ stdGaussian F) i).hasLaw)
    (iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id) β₀

/-! ### Boundary: a singular bread breaks sandwich consistency -/

/-- With the singular bread `A = 0`, the deterministic bread estimators `(n + 1)⁻¹ • 1` converge
to `A` and the meat is the constant `1`, yet the sandwiches `(n + 1)² • 1` do not converge to
`sandwichCovariance 0 1 = 0`: `tendstoInMeasure_sandwichCovariance` needs `IsUnit A`. -/
theorem singular_bread_sandwich :
    TendstoInMeasure (Measure.dirac ())
        (fun (n : ℕ) (_ : Unit) ↦ (1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) atTop (fun _ ↦ 0) ∧
      ¬ TendstoInMeasure (Measure.dirac ())
        (fun (n : ℕ) (_ : Unit) ↦
          sandwichCovariance ((1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) ((1 : ℝ) • 1))
        atTop (fun _ ↦ sandwichCovariance 0 ((1 : ℝ) • 1)) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · refine tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ ?_)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (1 : ℝ →L[ℝ] ℝ)
  have hzero : sandwichCovariance (0 : ℝ →L[ℝ] ℝ) ((1 : ℝ) • 1) = 0 := by
    simp [sandwichCovariance]
  have hn : ∀ n : ℕ, sandwichCovariance ((1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) ((1 : ℝ) • 1) =
      ((n : ℝ) + 1) ^ 2 • 1 := fun n ↦ by
    rw [sandwichCovariance_smul_one _ _ (by positivity)]
    congr 1
    field_simp
  rw [tendstoInMeasure_iff_dist] at h
  have h1 := h 1 one_pos
  simp only [hzero, hn, dist_zero_right, norm_smul, norm_one, mul_one, Real.norm_eq_abs] at h1
  have huniv : ∀ n : ℕ, {_x : Unit | (1 : ℝ) ≤ |((n : ℝ) + 1) ^ 2|} = Set.univ := fun n ↦ by
    ext
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  simp only [huniv, measure_univ] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-! ### Boundary: Lindeberg failure -/

/-- Exploding cluster scores `U k = 2 ^ k` violate the cluster Lindeberg condition in direction
`1`: the last cluster alone contributes `4 ^ (n - 1) / n > 1` to the Lindeberg sum. -/
theorem not_lindeberg_exploding :
    ¬ LindebergConditionTriangular
      (fun n k (_ : Unit) ↦ (√n)⁻¹ * ⟪(2 : ℝ) ^ k, (1 : ℝ)⟫) (Measure.dirac ()) := by
  intro h
  have hge : ∀ n : ℕ, 2 ≤ n → 1 ≤ ∑ k ∈ range n, ∫ ω, ((√n)⁻¹ * ⟪(2 : ℝ) ^ k, (1 : ℝ)⟫) ^ 2 *
      Set.indicator {ω' : Unit | 1 < |(√n)⁻¹ * ⟪(2 : ℝ) ^ k, (1 : ℝ)⟫|} 1 ω
        ∂(Measure.dirac ()) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    simp only [integral_dirac, inner_real, mul_one]
    set x : ℝ := (√((m + 1 : ℕ) : ℝ))⁻¹ * 2 ^ m with hx_def
    have hpow : (m : ℝ) + 1 < 4 ^ m := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 3 by norm_num) m
      norm_num at this
      linarith
    have hx2 : 1 < x ^ 2 := by
      rw [hx_def, mul_pow, inv_pow, Real.sq_sqrt (by positivity), ← pow_mul, pow_mul',
        show (2 : ℝ) ^ 2 = 4 by norm_num, inv_mul_eq_div, one_lt_div (by positivity)]
      push_cast
      exact hpow
    have hx : 1 < |x| := by
      rw [← sq_lt_sq₀ zero_le_one (abs_nonneg x), sq_abs, one_pow]
      exact hx2
    calc (1 : ℝ) ≤ x ^ 2 * Set.indicator {_ω' : Unit | 1 < |x|} 1 () := by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte, Pi.one_apply,
            mul_one]
          exact hx2.le
      _ ≤ _ := Finset.single_le_sum (f := fun k ↦ ((√((m + 1 : ℕ) : ℝ))⁻¹ * (2 : ℝ) ^ k) ^ 2 *
            Set.indicator {_ω' : Unit | 1 < |(√((m + 1 : ℕ) : ℝ))⁻¹ * (2 : ℝ) ^ k|} 1 ())
          (fun k _ ↦ mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _))
          (Finset.mem_range.2 (Nat.lt_succ_self m))
  obtain ⟨n, hn⟩ := (((h 1 one_pos).eventually (gt_mem_nhds one_pos)).and
    (eventually_ge_atTop 2)).exists
  exact absurd (hge n hn.2) (not_le.2 hn.1)

end GEESandwichTest
