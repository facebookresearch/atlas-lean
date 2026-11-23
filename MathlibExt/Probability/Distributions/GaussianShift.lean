/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianCdf
public import MathlibExt.Probability.Distributions.GaussianDensity
public import MathlibExt.Probability.Statistics.NeymanPearson

/-!
# Translates and affine images of the standard Gaussian

For `Z ~ stdGaussian (EuclideanSpace ℝ ι)` (the standard Gaussian `N(0, I)` on `ℝⁿ`), with
`Φ = cdf (gaussianReal 0 1)` and its generalized inverse `Φ⁻¹ = cdfQuantile (gaussianReal 0 1)`:

* `stdGaussian_map_const_add_smul`: `x + σ Z` has law `multivariateGaussian x (σ² • 1)`.
* `stdGaussian_real_inner_le`: for `v ≠ 0`, `P(⟪Z, v⟫ ≤ s) = Φ(s / ‖v‖)`.
* `stdGaussian_shift_lower` (**Gaussian Neyman–Pearson shift bound**): if `p ≤ P(Z ∈ A)` with
  `p ∈ (0, 1)`, then `Φ(Φ⁻¹ p - ‖v‖) ≤ P(Z + v ∈ A)`; `stdGaussian_shift_upper` is the
  complementary bound `P(Z + v ∈ B) ≤ Φ(Φ⁻¹ p + ‖v‖)` when `P(Z ∈ B) ≤ p`. Both apply
  `neyman_pearson_dominated_two_simple` to the Lebesgue densities of `N(0, I)` and `N(v, I)`,
  whose likelihood ratio `exp(⟪z, v⟫ - ‖v‖² / 2)` is increasing in `⟪z, v⟫`, so the optimal tests
  are half-spaces; half-spaces `{⟪z, v⟫ ≤ s}` attain equality.

The shift bound is Lemma 4 of Cohen, Rosenfeld and Kolter, *Certified adversarial robustness via
randomized smoothing*, ICML 2019 (arXiv:1902.02918), where it gives the certified radius of
randomized smoothing (`CSLibExt.MachineLearning.Robustness.RandomizedSmoothing`).

## References

* J. Neyman and E. S. Pearson, *On the problem of the most efficient tests of statistical
  hypotheses*, Phil. Trans. R. Soc. Lond. A 231 (1933), 289–337.
* J. Cohen, E. Rosenfeld and J. Z. Kolter, *Certified adversarial robustness via randomized
  smoothing*, ICML 2019, Lemma 4.
-/

@[expose] public section

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory Set
open MetaMathlibExt (stdGaussianPDFReal)
open scoped RealInnerProductSpace

variable {ι : Type*} [Fintype ι]

/-! ### Affine images -/

/-- `x + σ Z ~ N(x, σ² I)`: the affine image of the standard Gaussian is
`multivariateGaussian x (σ² • 1)`. -/
theorem stdGaussian_map_const_add_smul [DecidableEq ι] (x : EuclideanSpace ℝ ι) (σ : ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => x + σ • z) =
      multivariateGaussian x (σ ^ 2 • (1 : Matrix ι ι ℝ)) := by
  have hS : (σ ^ 2 • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.PosSemidef.one.smul (sq_nonneg σ)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [show (fun z : EuclideanSpace ℝ ι => x + σ • z) = (x + ·) ∘ (σ • ·) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_const_add, charFun_map_smul,
    charFun_stdGaussian, charFun_multivariateGaussian hS, ← Complex.exp_add]
  congr 1
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, real_inner_comm]
  have h1 : t.ofLp ⬝ᵥ t.ofLp = ‖t‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  rw [h1, ← Complex.ofReal_pow, mul_pow, sq_abs]
  push_cast
  ring


/-! ### Half-spaces under the standard Gaussian -/

/-- `⟪Z, v⟫ ~ N(0, ‖v‖²)` for `Z ~ stdGaussian`, so for `v ≠ 0` the half-space
`{z | ⟪z, v⟫ ≤ s}` has probability `Φ(s / ‖v‖)`. -/
theorem stdGaussian_real_inner_le {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) (s : ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).real {z | ⟪z, v⟫ ≤ s} =
      cdf (gaussianReal 0 1) (s / ‖v‖) := by
  set L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ v
  have hv2 : (‖v‖ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 hv) 2
  have hmap : (stdGaussian (EuclideanSpace ℝ ι)).map L = gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm]
  have hset : {z : EuclideanSpace ℝ ι | ⟪z, v⟫ ≤ s} = L ⁻¹' Iic s := by
    ext z
    simp [L, real_inner_comm]
  rw [hset, ← map_measureReal_apply L.continuous.measurable measurableSet_Iic, hmap,
    ← cdf_eq_real, cdf_gaussianReal_eq_std 0 s hv2, sub_zero,
    Real.coe_toNNReal _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### Densities of the standard Gaussian and its translates -/

private theorem stdGaussianPDFReal_pos (z : EuclideanSpace ℝ ι) : 0 < stdGaussianPDFReal z := by
  unfold stdGaussianPDFReal
  positivity

/-- The likelihood ratio of `N(v, I)` to `N(0, I)` at `z` is `exp(⟪z, v⟫ - ‖v‖² / 2)`. -/
private theorem stdGaussianPDFReal_sub (z v : EuclideanSpace ℝ ι) :
    stdGaussianPDFReal (z - v) = stdGaussianPDFReal z * Real.exp (⟪z, v⟫ - ‖v‖ ^ 2 / 2) := by
  simp only [stdGaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add, norm_sub_sq_real]
  congr 2
  ring

/-- `Z + v ~ N(v, I)` has density `z ↦ φ(z - v)` with respect to Lebesgue measure. -/
private theorem stdGaussian_map_add (v : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (· + v) =
      volume.withDensity fun z => ENNReal.ofReal (stdGaussianPDFReal (z - v)) := by
  rw [MetaMathlibExt.stdGaussian_eq_withDensity, ← MeasurableEquiv.coe_addRight,
    MetaMathlibExt.map_withDensity_measurableEquiv, MeasurableEquiv.coe_addRight,
    map_add_right_eq_self]
  rfl

private theorem measurableSet_add_mem {G : Type*} [MeasurableSpace G] [Add G] [MeasurableAdd G]
    {S : Set G} (hS : MeasurableSet S) (v : G) : MeasurableSet {z | z + v ∈ S} :=
  (measurable_add_const v) hS

/-- `P(Z + v ∈ S) = ∫ 1_S(z) φ(z - v) dz`. -/
private theorem stdGaussian_real_add_mem {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S)
    (v : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + v ∈ S} =
      ∫ z, S.indicator (fun z => stdGaussianPDFReal (z - v)) z := by
  have hint : Integrable (fun z => stdGaussianPDFReal (z - v)) :=
    MetaMathlibExt.integrable_stdGaussianPDFReal.comp_sub_right v
  change _ = ∫ z, S.indicator (fun z => stdGaussianPDFReal (z - v)) z ∂volume
  rw [show {z | z + v ∈ S} = (· + v) ⁻¹' S from rfl,
    ← map_measureReal_apply (measurable_add_const v) hS, stdGaussian_map_add, measureReal_def,
    withDensity_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_of_all _ fun z => MetaMathlibExt.stdGaussianPDFReal_nonneg _),
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun z _ =>
      MetaMathlibExt.stdGaussianPDFReal_nonneg _), integral_indicator hS]

/-! ### The Gaussian Neyman–Pearson shift bound -/

/-- The `{0, 1}`-valued test of a set. -/
private noncomputable def setTest {Ω : Type*} (S : Set Ω) (z : Ω) : Icc (0 : ℝ) 1 :=
  ⟨S.indicator 1 z, by by_cases h : z ∈ S <;> simp [h]⟩

private theorem measurable_setTest {Ω : Type*} [MeasurableSpace Ω] {S : Set Ω}
    (hS : MeasurableSet S) : Measurable (setTest S) :=
  (measurable_one.indicator hS).subtype_mk

private theorem setTest_mul {Ω : Type*} (S : Set Ω) (g : Ω → ℝ) :
    (fun z => (setTest S z).val * g z) = S.indicator g := by
  funext z
  by_cases h : z ∈ S <;> simp [setTest, h]

/-- **Gaussian Neyman–Pearson shift bound** (Cohen, Rosenfeld and Kolter, Lemma 4). If a
measurable set `A` has standard Gaussian probability at least `p ∈ (0, 1)`, then its translate by
`-v` has probability at least `Φ(Φ⁻¹ p - ‖v‖)`: `Φ(Φ⁻¹ p - ‖v‖) ≤ P(Z + v ∈ A)`. The half-spaces
`{z | ⟪z, v⟫ ≤ s}` attain equality. -/
theorem stdGaussian_shift_lower {A : Set (EuclideanSpace ℝ ι)} (hA : MeasurableSet A)
    (v : EuclideanSpace ℝ ι) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpA : p ≤ (stdGaussian (EuclideanSpace ℝ ι)).real A) :
    cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) p - ‖v‖) ≤
      (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + v ∈ A} := by
  set γ := stdGaussian (EuclideanSpace ℝ ι)
  set t := cdfQuantile (gaussianReal 0 1) p
  have hΦt : cdf (gaussianReal 0 1) t = p :=
    cdf_cdfQuantile_eq_of_continuous _ (continuous_cdf_gaussianReal 0 one_ne_zero) hp
  rcases eq_or_ne v 0 with rfl | hv
  · simpa [hΦt] using hpA
  set r := ‖v‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 hv
  -- The Neyman–Pearson rejection region: the half-space `{⟪z, v⟫ > t ‖v‖}`.
  set H : Set (EuclideanSpace ℝ ι) := {z | t * r < ⟪z, v⟫} with hH_def
  have hH : MeasurableSet H := measurableSet_lt measurable_const (by fun_prop)
  have hHc : Hᶜ = {z | ⟪z, v⟫ ≤ t * r} := by
    ext z
    simp [hH_def]
  have hγ0 : ∀ {S : Set (EuclideanSpace ℝ ι)}, MeasurableSet S →
      γ.real S = ∫ z, S.indicator stdGaussianPDFReal z := fun hS => by
    simpa using stdGaussian_real_add_mem hS 0
  have hγH : γ.real H = 1 - p := by
    rw [← compl_compl H, measureReal_compl hH.compl, probReal_univ, hHc,
      stdGaussian_real_inner_le hv, mul_div_cancel_right₀ _ hr.ne', hΦt]
  have hγAc : γ.real Aᶜ ≤ 1 - p := by
    rw [measureReal_compl hA, probReal_univ]
    linarith
  have hk : 0 ≤ Real.exp (t * r - r ^ 2 / 2) := (Real.exp_pos _).le
  have hNP := MathlibExt.Probability.Statistics.NeymanPearson.neyman_pearson_dominated_two_simple
    (μ := volume) (p := stdGaussianPDFReal) (q := fun z => stdGaussianPDFReal (z - v))
    MetaMathlibExt.measurable_stdGaussianPDFReal
    (MetaMathlibExt.measurable_stdGaussianPDFReal.comp (measurable_sub_const v))
    MetaMathlibExt.stdGaussianPDFReal_nonneg (fun z => MetaMathlibExt.stdGaussianPDFReal_nonneg _)
    MetaMathlibExt.integrable_stdGaussianPDFReal
    (MetaMathlibExt.integrable_stdGaussianPDFReal.comp_sub_right v)
    _ hk (setTest H) (measurable_setTest hH) ?_ ?_ (setTest Aᶜ) (measurable_setTest hA.compl) ?_
  · -- Power comparison: `P(Z + v ∉ A) ≤ P(Z + v ∈ H)`.
    simp only [setTest_mul] at hNP
    rw [← stdGaussian_real_add_mem hA.compl, ← stdGaussian_real_add_mem hH] at hNP
    have hcompl : ∀ {S : Set (EuclideanSpace ℝ ι)}, MeasurableSet S →
        γ.real {z | z + v ∈ Sᶜ} = 1 - γ.real {z | z + v ∈ S} := by
      intro S hS
      rw [show {z | z + v ∈ Sᶜ} = {z | z + v ∈ S}ᶜ from rfl,
        measureReal_compl (measurableSet_add_mem hS v), probReal_univ]
    have hshift : {z | z + v ∈ Hᶜ} = {z | ⟪z, v⟫ ≤ t * r - r ^ 2} := by
      ext z
      simp only [hHc, mem_ofPred_eq, inner_add_left, real_inner_self_eq_norm_sq, ← hr_def]
      constructor <;> intro h <;> linarith
    have hlow : γ.real {z | z + v ∈ Hᶜ} = cdf (gaussianReal 0 1) (t - r) := by
      rw [hshift, stdGaussian_real_inner_le hv, ← hr_def]
      congr 1
      rw [div_eq_iff hr.ne']
      ring
    rw [hcompl hA] at hNP
    rw [hcompl hH] at hlow
    linarith
  · intro z hz
    have hzH : z ∈ H := by
      rw [stdGaussianPDFReal_sub, mul_comm (Real.exp _)] at hz
      have := lt_of_mul_lt_mul_left hz (stdGaussianPDFReal_pos z).le
      rw [Real.exp_lt_exp] at this
      simp only [hH_def, mem_ofPred_eq]
      linarith
    simp [setTest, hzH]
  · intro z hz
    have hzH : z ∉ H := by
      rw [stdGaussianPDFReal_sub, mul_comm (Real.exp (t * r - r ^ 2 / 2))] at hz
      have := lt_of_mul_lt_mul_left hz (stdGaussianPDFReal_pos z).le
      rw [Real.exp_lt_exp] at this
      simp only [hH_def, mem_ofPred_eq, not_lt]
      linarith
    simp [setTest, hzH]
  · -- Size comparison: `P(Z ∉ A) ≤ 1 - p = P(Z ∈ H)`.
    simp only [setTest_mul]
    rw [← hγ0 hA.compl, ← hγ0 hH, hγH]
    exact hγAc

/-- The complementary shift bound: if `P(Z ∈ B) ≤ p` with `p ∈ (0, 1)`, then
`P(Z + v ∈ B) ≤ Φ(Φ⁻¹ p + ‖v‖)`. -/
theorem stdGaussian_shift_upper {B : Set (EuclideanSpace ℝ ι)} (hB : MeasurableSet B)
    (v : EuclideanSpace ℝ ι) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpB : (stdGaussian (EuclideanSpace ℝ ι)).real B ≤ p) :
    (stdGaussian (EuclideanSpace ℝ ι)).real {z | z + v ∈ B} ≤
      cdf (gaussianReal 0 1) (cdfQuantile (gaussianReal 0 1) p + ‖v‖) := by
  have hp' : 1 - p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hBc : 1 - p ≤ (stdGaussian (EuclideanSpace ℝ ι)).real Bᶜ := by
    rw [measureReal_compl hB, probReal_univ]
    linarith
  have h := stdGaussian_shift_lower hB.compl v hp' hBc
  rw [cdfQuantile_gaussianReal_one_sub, show -cdfQuantile (gaussianReal 0 1) p - ‖v‖ =
      -(cdfQuantile (gaussianReal 0 1) p + ‖v‖) by ring, cdf_gaussianReal_neg,
    show {z | z + v ∈ Bᶜ} = {z | z + v ∈ B}ᶜ from rfl,
    measureReal_compl (measurableSet_add_mem hB v), probReal_univ] at h
  linarith

end ProbabilityTheory
