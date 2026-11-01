/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranTheorem
public import MathlibExt.Probability.Statistics.MetaAnalysis

/-!
# Cochran's heterogeneity statistic `Q`

For `k` independent estimates `X₁, …, X_k` of a common parameter `θ` with known variances
`v₁, …, v_k > 0`, Cochran's `Q` statistic is

`Q = ∑ᵢ vᵢ⁻¹ (Xᵢ - X̄)²`, with `X̄ = ∑ⱼ wⱼ Xⱼ` the inverse-variance-weighted mean
(`wⱼ = vⱼ⁻¹ / ∑ₗ vₗ⁻¹`, `inverseVarianceWeights`).

Under homogeneity (`Xᵢ ~ N(θ, vᵢ)` independent) and `k ≥ 2`, `Q` is chi-square with `k - 1`
degrees of freedom. The proof standardizes `Zᵢ = (Xᵢ - θ) / √vᵢ`, writes
`Q = ‖Z - P_a Z‖²` for the orthogonal projection `P_a` onto the line spanned by
`a = (v₁^{-1/2}, …, v_k^{-1/2})`, and applies Cochran's theorem
(`stdGaussian_map_norm_sq_starProjection`) to the hyperplane `a^⊥` of dimension `k - 1`.

## Main results

* `cochranQ_eq_norm_sq`: the algebraic identity `Q = ‖Z - P_a Z‖²`.
* `hasLaw_cochranQ`: `Q ~ χ²_{k-1}` (Cochran 1954).

## References

* W. G. Cochran, *The combination of estimates from different experiments*, Biometrics 10
  (1954), 101–129.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MetaAnalysis

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace

open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- Cochran's heterogeneity statistic `Q = ∑ᵢ vᵢ⁻¹ (Xᵢ - ∑ⱼ wⱼ Xⱼ)²` of the estimates `X` with
variances `v`, where `w = inverseVarianceWeights v`. -/
noncomputable def cochranQ (v X : Fin k → ℝ) : ℝ :=
  ∑ i, (v i)⁻¹ * (X i - ∑ j, inverseVarianceWeights v j * X j) ^ 2

/-- Algebraic core of Cochran's theorem for `Q`: if `Xᵢ = θ + √vᵢ zᵢ` with `vᵢ > 0`, then `Q` is
the squared distance from `z` to the line spanned by `a = (vᵢ^{-1/2})ᵢ`, i.e. the squared norm
of the projection of `z` onto the orthogonal complement of that line. -/
theorem cochranQ_eq_norm_sq {v : Fin k → ℝ} (hv : ∀ i, 0 < v i) (θ : ℝ)
    (z : EuclideanSpace ℝ (Fin k)) :
    cochranQ v (fun i => θ + √(v i) * z i) =
      ‖(Submodule.span ℝ {WithLp.toLp 2 fun i => (√(v i))⁻¹})ᗮ.starProjection z‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Subsingleton.elim z 0]
    simp [cochranQ]
  set S := ∑ j, (v j)⁻¹ with hSdef
  have hS : 0 < S := Finset.sum_pos (fun i _ => inv_pos.2 (hv i)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsq : ∀ i, √(v i) ^ 2 = v i := fun i => Real.sq_sqrt (hv i).le
  have hspos : ∀ i, 0 < √(v i) := fun i => Real.sqrt_pos.2 (hv i)
  have ha2 : ‖(WithLp.toLp 2 fun i => (√(v i))⁻¹ : EuclideanSpace ℝ (Fin k))‖ ^ 2 = S := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [inv_pow, hsq]
  have hinner : ⟪(WithLp.toLp 2 fun i => (√(v i))⁻¹ : EuclideanSpace ℝ (Fin k)), z⟫ =
      ∑ j, (√(v j))⁻¹ * z j := by
    simp [PiLp.inner_apply, mul_comm]
  have hw : ∀ j, inverseVarianceWeights v j * √(v j) = (√(v j))⁻¹ / S := by
    intro j
    have := (hspos j).ne'
    simp only [inverseVarianceWeights, ← hSdef]
    rw [show (v j)⁻¹ = (√(v j) ^ 2)⁻¹ by rw [hsq]]
    field_simp
  have hmean : ∑ j, inverseVarianceWeights v j * (θ + √(v j) * z j) =
      θ + (∑ j, (√(v j))⁻¹ * z j) / S := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_inverseVarianceWeights hv hk,
      one_mul, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hw j]
    ring
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, ha2, hinner,
    EuclideanSpace.norm_sq_eq, cochranQ, hmean]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hspos i).ne'
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs,
    RCLike.ofReal_real_eq_id, id_eq]
  rw [show (v i)⁻¹ = (√(v i) ^ 2)⁻¹ by rw [hsq]]
  field_simp
  ring

/-- **Cochran (1954).** For `k ≥ 2` independent Gaussian estimates `Xᵢ ~ N(θ, vᵢ)` with
positive known variances, Cochran's `Q` has the chi-square law with `k - 1` degrees of
freedom. -/
theorem hasLaw_cochranQ (hk : 2 ≤ k) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : ℝ} {v : Fin k → ℝ≥0} (hv : ∀ i, v i ≠ 0) {X : Fin k → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal θ (v i)) μ) (hind : iIndepFun X μ) :
    HasLaw (fun ω => cochranQ (fun i => (v i : ℝ)) fun i => X i ω)
      (chiSquareMeasure (k - 1)) μ := by
  have hvpos : ∀ i, 0 < (v i : ℝ) := fun i => NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv i))
  set g : Fin k → ℝ → ℝ := fun i x => (x - θ) / √(v i : ℝ) with hgdef
  have hg : ∀ i, Measurable (g i) := fun i => (measurable_id.sub_const _).div_const _
  have hgauss : ∀ i, (gaussianReal θ (v i)).map (g i) = gaussianReal 0 1 := by
    intro i
    have : g i = (· / √(v i : ℝ)) ∘ (· - θ) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_div_const, sub_self, zero_div]
    congr 1
    ext
    simp [Real.sq_sqrt (hvpos i).le, (hvpos i).ne']
  set Z : Fin k → Ω → ℝ := fun i => g i ∘ X i with hZdef
  have hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) μ :=
    fun i => HasLaw.comp ⟨(hg i).aemeasurable, hgauss i⟩ (hlaw i)
  have hindZ : iIndepFun Z μ := hind.comp g hg
  have hZm : ∀ i, AEMeasurable (Z i) μ := fun i => (hZlaw i).aemeasurable
  have hjoint : μ.map (fun ω i => Z i ω) = Measure.pi fun _ => gaussianReal 0 1 := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hZm).1 hindZ]
    congr 1
    funext i
    exact (hZlaw i).map_eq
  set W : Ω → EuclideanSpace ℝ (Fin k) := fun ω => WithLp.toLp 2 (fun i => Z i ω) with hWdef
  have hWm : AEMeasurable (fun ω i => Z i ω) μ := AEMeasurable.of_eval hZm
  have hW : HasLaw W (stdGaussian (EuclideanSpace ℝ (Fin k))) μ := by
    have h1 : HasLaw (fun ω i => Z i ω) (Measure.pi fun _ => gaussianReal 0 1) μ := ⟨hWm, hjoint⟩
    have h2 : HasLaw (WithLp.toLp 2) (stdGaussian (EuclideanSpace ℝ (Fin k)))
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) :=
      ⟨by fun_prop, map_pi_eq_stdGaussian⟩
    exact h2.comp h1
  set a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i => (√(v i : ℝ))⁻¹ with hadef
  set K := (Submodule.span ℝ {a})ᗮ with hKdef
  have ha : a ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin k) => x ⟨0, by omega⟩) h
    simp only [hadef, PiLp.zero_apply] at h0
    exact (inv_pos.2 (Real.sqrt_pos.2 (hvpos _))).ne' h0
  have hfr : finrank ℝ K = k - 1 := by
    have := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {a})
    rw [finrank_span_singleton ha, finrank_euclideanSpace_fin] at this
    change finrank ℝ (Submodule.span ℝ {a})ᗮ = k - 1
    omega
  have hQ : (fun ω => cochranQ (fun i => (v i : ℝ)) fun i => X i ω) =
      (fun x => ‖K.starProjection x‖ ^ 2) ∘ W := by
    funext ω
    have hX : (fun i => X i ω) = fun i => θ + √(v i : ℝ) * W ω i := by
      funext i
      have := (Real.sqrt_pos.2 (hvpos i)).ne'
      simp only [hWdef, hZdef, hgdef, Function.comp_apply]
      field_simp
      ring
    rw [Function.comp_apply, hX, cochranQ_eq_norm_sq (fun i => hvpos i)]
  rw [hQ, ← hfr]
  exact HasLaw.comp ⟨by fun_prop, stdGaussian_map_norm_sq_starProjection K (by omega)⟩ hW

end MathlibExt.Probability.Statistics.MetaAnalysis
