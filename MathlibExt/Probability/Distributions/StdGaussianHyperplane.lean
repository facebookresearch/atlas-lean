/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Signs of a standard Gaussian vector against two directions

For a standard Gaussian vector `r` in a finite-dimensional real inner product space:

* `map_inner_stdGaussian` and `map_inner_pair_stdGaussian`: `⟪u, r⟫` is standard normal for a
  unit vector `u`, and `(⟪e₁, r⟫, ⟪e₂, r⟫)` is a pair of independent standard normals for
  orthonormal `e₁`, `e₂` (proved with characteristic functions);
* `gaussianReal_prod_wedge`: in the plane, two lines through the origin at angle `2a` separate a
  standard Gaussian point with probability `2a / π` (proved in polar coordinates);
* `stdGaussian_sign_ne`: hence `P[sgn⟪u, r⟫ ≠ sgn⟪v, r⟫] = arccos⟪u, v⟫ / π` for unit vectors `u`,
  `v`, the separation lemma of M. X. Goemans and D. P. Williamson, "Improved approximation
  algorithms for maximum cut and satisfiability problems using semidefinite programming",
  *J. ACM* 42(6) (1995), 1115–1145, Lemma 3.2, in the Gaussian form of their remark on p. 1121.
  Equivalently, for a standard bivariate normal pair with correlation `ρ`, the probability of
  different signs is `arccos ρ / π`, Sheppard's formula in another guise.
-/

@[expose] public section

namespace MathlibExt.Probability.Distributions.StdGaussianHyperplane

open Real MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem cos_nonneg_iff_mem {x : ℝ} (h1 : -(π + π / 2) < x) (h2 : x < π + π / 2) :
    0 ≤ cos x ↔ x ∈ Icc (-(π / 2)) (π / 2) := by
  constructor
  · intro h
    by_contra hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have := cos_neg_of_pi_div_two_lt_of_lt (x := -x) (by linarith) (by linarith)
      rw [cos_neg] at this
      linarith
    · have := cos_neg_of_pi_div_two_lt_of_lt hx h2
      linarith
  · intro h
    exact cos_nonneg_of_mem_Icc h

private theorem wedge_iff {a φ : ℝ} (ha0 : 0 < a) (ha : a < π / 2) (hφ : φ ∈ Ioo (-π) π) :
    ((0 ≤ cos (φ + a)) ≠ (0 ≤ cos (φ - a))) ↔
      φ ∈ Ico (-(π / 2) - a) (-(π / 2) + a) ∪ Ioc (π / 2 - a) (π / 2 + a) := by
  obtain ⟨h1, h2⟩ := hφ
  have hpi := pi_pos
  rw [cos_nonneg_iff_mem (by linarith) (by linarith),
    cos_nonneg_iff_mem (by linarith) (by linarith)]
  have key : ∀ P Q : Prop, (P ≠ Q) ↔ ((P ∧ ¬Q) ∨ (Q ∧ ¬P)) := by
    intro P Q; rw [ne_eq, eq_iff_iff]; tauto
  rw [key]
  simp only [mem_Icc, mem_union, mem_Ico, mem_Ioc]
  constructor
  · rintro (⟨⟨hA1, hA2⟩, hB⟩ | ⟨⟨hB1, hB2⟩, hA⟩)
    · left
      refine ⟨by linarith, ?_⟩
      by_contra h
      push Not at h
      exact hB ⟨by linarith, by linarith⟩
    · right
      refine ⟨?_, by linarith⟩
      by_contra h
      push Not at h
      exact hA ⟨by linarith, by linarith⟩
  · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
    · left
      exact ⟨⟨by linarith, by linarith⟩, fun ⟨hb, _⟩ => by linarith⟩
    · right
      exact ⟨⟨by linarith, by linarith⟩, fun ⟨_, hb⟩ => by linarith⟩

/-- **Sign-disagreement sets are measurable.** For continuous real functions `f`, `g`, the set of
points where `0 ≤ f` and `0 ≤ g` disagree is measurable. -/
theorem measurableSet_sign_ne {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {f g : α → ℝ} (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {p | (0 ≤ f p) ≠ (0 ≤ g p)} := by
  have : {p | (0 ≤ f p) ≠ (0 ≤ g p)} =
      ({p | 0 ≤ f p} \ {p | 0 ≤ g p}) ∪ ({p | 0 ≤ g p} \ {p | 0 ≤ f p}) := by
    ext p
    simp only [mem_ofPred_eq, mem_union, mem_sdiff, ne_eq, eq_iff_iff]
    tauto
  rw [this]
  have hF : MeasurableSet {p | 0 ≤ f p} := measurableSet_le measurable_const hf.measurable
  have hG : MeasurableSet {p | 0 ≤ g p} := measurableSet_le measurable_const hg.measurable
  exact (hF.diff hG).union (hG.diff hF)

private theorem lintegral_radial :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * rexp (-r ^ 2 / 2)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  have h' : ∫ x in Ioi (0 : ℝ), x * rexp (-x ^ 2 / 2) = 1 := by
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal, h', ENNReal.ofReal_one]
  · exact Integrable.of_integral_ne_zero (by rw [h']; norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (le_of_lt hx) (exp_pos _).le


private theorem gaussianReal_prod_eq_withDensity :
    (gaussianReal 0 1).prod (gaussianReal 0 1) =
      volume.withDensity fun p : ℝ × ℝ =>
        ENNReal.ofReal (gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    ← Measure.volume_eq_prod]
  congr 1
  funext p
  rw [gaussianPDF, gaussianPDF, ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 _)]

private theorem gaussianPDFReal_polar (r φ : ℝ) :
    gaussianPDFReal 0 1 (r * cos φ) * gaussianPDFReal 0 1 (r * sin φ) =
      rexp (-r ^ 2 / 2) / (2 * π) := by
  have hpi := pi_pos
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [show (√(2 * π))⁻¹ * rexp (-(r * cos φ) ^ 2 / 2) * ((√(2 * π))⁻¹ * rexp (-(r * sin φ) ^ 2 / 2))
      = ((√(2 * π)) ^ 2)⁻¹ * (rexp (-(r * cos φ) ^ 2 / 2) * rexp (-(r * sin φ) ^ 2 / 2)) by ring,
    ← exp_add, Real.sq_sqrt (by positivity)]
  have : -(r * cos φ) ^ 2 / 2 + -(r * sin φ) ^ 2 / 2 = -r ^ 2 / 2 := by
    have := sin_sq_add_cos_sq φ
    linear_combination (-(r ^ 2) / 2) * this
  rw [this]
  field_simp

/-- **The planar wedge probability.** For a standard Gaussian vector `p` in the plane and
`0 < a < π / 2`, the probability that the lines with normals `(cos a, -sin a)` and
`(cos a, sin a)` put `p` on different sides is `2a / π`. -/
theorem gaussianReal_prod_wedge {a : ℝ} (ha0 : 0 < a) (ha : a < π / 2) :
    (gaussianReal 0 1).prod (gaussianReal 0 1)
        {p : ℝ × ℝ | (0 ≤ cos a * p.1 - sin a * p.2) ≠ (0 ≤ cos a * p.1 + sin a * p.2)} =
      ENNReal.ofReal (2 * a / π) := by
  have hpi := pi_pos
  set S := {p : ℝ × ℝ | (0 ≤ cos a * p.1 - sin a * p.2) ≠ (0 ≤ cos a * p.1 + sin a * p.2)}
    with hSdef
  have hS : MeasurableSet S := measurableSet_sign_ne (by fun_prop) (by fun_prop)
  set W := Ico (-(π / 2) - a) (-(π / 2) + a) ∪ Ioc (π / 2 - a) (π / 2 + a) with hWdef
  have hW : MeasurableSet W := measurableSet_Ico.union measurableSet_Ioc
  rw [gaussianReal_prod_eq_withDensity, withDensity_apply _ hS, ← lintegral_indicator hS,
    ← lintegral_comp_polarCoord_symm, polarCoord_target]
  have hcongr : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • S.indicator (fun p : ℝ × ℝ =>
        ENNReal.ofReal (gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2)) (polarCoord.symm p) =
      ENNReal.ofReal (p.1 * rexp (-p.1 ^ 2 / 2) / (2 * π)) * W.indicator 1 p.2 := by
    rintro ⟨r, φ⟩ ⟨hr, hφ⟩
    simp only [mem_Ioi] at hr
    simp only [polarCoord_symm_apply]
    have hmem : (r * cos φ, r * sin φ) ∈ S ↔ φ ∈ W := by
      rw [hSdef, mem_ofPred_eq, ← wedge_iff ha0 ha hφ]
      have e1 : cos a * (r * cos φ) - sin a * (r * sin φ) = r * cos (φ + a) := by
        rw [cos_add]; ring
      have e2 : cos a * (r * cos φ) + sin a * (r * sin φ) = r * cos (φ - a) := by
        rw [cos_sub]; ring
      rw [e1, e2, mul_nonneg_iff_of_pos_left hr, mul_nonneg_iff_of_pos_left hr]
    by_cases h : φ ∈ W
    · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h, gaussianPDFReal_polar, smul_eq_mul,
        Pi.one_apply, mul_one, ← ENNReal.ofReal_mul hr.le]
      congr 1
      ring
    · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), indicator_of_notMem h, smul_zero,
        mul_zero]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcongr,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r => ENNReal.ofReal (r * rexp (-r ^ 2 / 2) / (2 * π)))
      (g := fun φ => W.indicator 1 φ) (by fun_prop) ((measurable_one.indicator hW).aemeasurable)]
  have hrad : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * rexp (-r ^ 2 / 2) / (2 * π)) =
      ENNReal.ofReal (1 / (2 * π)) := by
    have : ∀ r : ℝ, ENNReal.ofReal (r * rexp (-r ^ 2 / 2) / (2 * π)) =
        ENNReal.ofReal (r * rexp (-r ^ 2 / 2)) * ENNReal.ofReal (1 / (2 * π)) := by
      intro r
      rw [← ENNReal.ofReal_mul' (by positivity)]
      congr 1
      ring
    simp_rw [this]
    rw [lintegral_mul_const _ (by fun_prop), lintegral_radial, one_mul]
  have hang : ∫⁻ φ in Ioo (-π) π, W.indicator 1 φ = ENNReal.ofReal (4 * a) := by
    rw [lintegral_indicator_one hW, Measure.restrict_apply hW]
    have hsub : W ∩ Ioo (-π) π = W := by
      apply inter_eq_left.2
      rintro φ (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    rw [hsub, hWdef, measure_union _ measurableSet_Ioc, Real.volume_Ico, Real.volume_Ioc,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    · congr 1; ring
    · rw [Set.disjoint_left]
      rintro φ ⟨_, h2⟩ ⟨h3, _⟩
      linarith
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **One-dimensional marginal of the standard Gaussian.** For a unit vector `u`, the law of
`⟪u, r⟫` under the standard Gaussian measure is the standard normal law. -/
theorem map_inner_stdGaussian {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun r => inner ℝ u r) = gaussianReal 0 1 := by
  have hmeas : Measurable fun r : E => inner ℝ u r :=
    (continuous_const.inner continuous_id).measurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop), charFun_gaussianReal]
  have h := charFun_stdGaussian (E := E) (t • u)
  rw [charFun_apply] at h
  have hint : ∀ x : E, Complex.exp (↑t * ↑(inner ℝ u x) * Complex.I) =
      Complex.exp (↑(inner ℝ x (t • u)) * Complex.I) := by
    intro x
    rw [real_inner_smul_right, real_inner_comm]
    push_cast
    ring_nf
  simp_rw [hint, h, norm_smul, hu, Real.norm_eq_abs]
  congr 1
  rw [mul_one, ← Complex.ofReal_pow, sq_abs]
  push_cast
  ring

/-- **Characteristic function of a pair of inner products.** For vectors `u`, `v` and a standard
Gaussian vector `r`, the characteristic function of `(⟪u, r⟫, ⟪v, r⟫) ∈ ℝ²` at `t` is
`exp(-‖t₀ u + t₁ v‖² / 2)`. -/
theorem charFun_map_inner_pair (u v : E) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun ((stdGaussian E).map fun r => WithLp.toLp 2 ![inner ℝ u r, inner ℝ v r]) t =
      Complex.exp (-(‖t 0 • u + t 1 • v‖ : ℂ) ^ 2 / 2) := by
  have hPc : Continuous fun r : E => WithLp.toLp 2 ![inner ℝ u r, inner ℝ v r] :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by fin_cases i <;> fun_prop)
  rw [charFun_apply, integral_map hPc.measurable.aemeasurable (by fun_prop)]
  have h := charFun_stdGaussian (E := E) (t 0 • u + t 1 • v)
  rw [charFun_apply] at h
  have hint : ∀ x : E, inner ℝ (WithLp.toLp 2 ![inner ℝ u x, inner ℝ v x] :
      EuclideanSpace ℝ (Fin 2)) t = inner ℝ x (t 0 • u + t 1 • v) := by
    intro x
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      inner_add_right, real_inner_smul_right, RCLike.inner_apply, conj_trivial,
      real_inner_comm x]
  simp_rw [hint, h]

/-- **Two-dimensional marginal of the standard Gaussian.** For orthonormal `e₁`, `e₂`, the law of
`(⟪e₁, r⟫, ⟪e₂, r⟫)` under the standard Gaussian measure is the product of two standard normal
laws. -/
theorem map_inner_pair_stdGaussian {e₁ e₂ : E} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = 0) :
    (stdGaussian E).map (fun r => (inner ℝ e₁ r, inner ℝ e₂ r)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  -- first into `EuclideanSpace ℝ (Fin 2)`
  let P : E → EuclideanSpace ℝ (Fin 2) := fun r => WithLp.toLp 2 ![inner ℝ e₁ r, inner ℝ e₂ r]
  have hPc : Continuous P :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by fin_cases i <;> fun_prop)
  have hP : Measurable P := hPc.measurable
  have hmapP : (stdGaussian E).map P = stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_apply, integral_map hP.aemeasurable (by fun_prop), charFun_stdGaussian]
    have h := charFun_stdGaussian (E := E) (t 0 • e₁ + t 1 • e₂)
    rw [charFun_apply] at h
    have hint : ∀ x : E, inner ℝ (P x) t = inner ℝ x (t 0 • e₁ + t 1 • e₂) := by
      intro x
      simp only [P, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        inner_add_right, real_inner_smul_right, RCLike.inner_apply, conj_trivial,
        real_inner_comm x]
    simp_rw [hint, h]
    congr 3
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, norm_add_sq_real, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_right, h₁₂, h₁, h₂, Real.norm_eq_abs,
      Real.norm_eq_abs]
    ring_nf
    rw [sq_abs, sq_abs]
  have hpi : (stdGaussian (EuclideanSpace ℝ (Fin 2))).map (fun x => (x 0, x 1)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((fun x : EuclideanSpace ℝ (Fin 2) => (x 0, x 1)) ∘ WithLp.toLp 2) =
        (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) := by
      funext x; rfl
    rw [this]
    exact (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [← hpi, ← hmapP, Measure.map_map (by fun_prop) hP]
  rfl

/-- **A random hyperplane separates two unit vectors with probability angle over π.** For unit
vectors `u`, `v` of a finite-dimensional real inner product space and a standard Gaussian vector
`r`, the probability that `⟪u, r⟫` and `⟪v, r⟫` have different signs (`sgn x = 1` for `x ≥ 0`)
is `arccos ⟪u, v⟫ / π` (Goemans and Williamson, *J. ACM* 42(6) (1995), Lemma 3.2 with the
Gaussian remark on p. 1121). -/
theorem stdGaussian_sign_ne {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    stdGaussian E {r | (0 ≤ inner ℝ u r) ≠ (0 ≤ inner ℝ v r)} =
      ENNReal.ofReal (arccos (inner ℝ u v) / π) := by
  have hpi := pi_pos
  have hρle : |inner ℝ u v| ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rwa [hu, hv, one_mul] at this
  have hsum : ‖u + v‖ ^ 2 = 2 + 2 * inner ℝ u v := by
    rw [norm_add_sq_real, hu, hv]; ring
  have hdiff : ‖v - u‖ ^ 2 = 2 - 2 * inner ℝ u v := by
    rw [norm_sub_sq_real, hu, hv, real_inner_comm]; ring
  rcases eq_or_lt_of_le (abs_le.1 hρle).2 with h1 | h1
  · -- `⟪u, v⟫ = 1`: the vectors coincide
    have hvu : v = u := by
      have h0 : ‖v - u‖ ^ 2 = 0 := by rw [hdiff, h1]; ring
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    subst hvu
    have : {r : E | (0 ≤ inner ℝ v r) ≠ (0 ≤ inner ℝ v r)} = ∅ := by
      ext r; simp
    rw [this, measure_empty, h1, arccos_one, zero_div, ENNReal.ofReal_zero]
  rcases eq_or_lt_of_le (abs_le.1 hρle).1 with h2 | h2
  · -- `⟪u, v⟫ = -1`: the vectors are opposite
    have hvu : v = -u := by
      have h0 : ‖u + v‖ ^ 2 = 0 := by rw [hsum, ← h2]; ring
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
      exact eq_neg_of_add_eq_zero_right (norm_eq_zero.1 this)
    have hset : {r : E | (0 ≤ inner ℝ u r) ≠ (0 ≤ inner ℝ v r)} =
        (fun r => inner ℝ u r) ⁻¹' {0}ᶜ := by
      ext r
      simp only [hvu, inner_neg_left, mem_ofPred_eq, mem_preimage, mem_compl_iff,
        mem_singleton_iff, ne_eq, eq_iff_iff]
      constructor
      · intro h h0; rw [h0, neg_zero] at h; exact h (Iff.rfl)
      · intro h0 h
        rcases lt_or_gt_of_ne h0 with hl | hl
        · exact absurd (h.2 (by linarith)) (by linarith)
        · exact absurd (h.1 hl.le) (by linarith)
    have hmeas : Measurable fun r : E => inner ℝ u r :=
      (continuous_const.inner continuous_id).measurable
    rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton 0).compl,
      map_inner_stdGaussian hu, prob_compl_eq_one_sub (measurableSet_singleton 0)]
    have hzero : gaussianReal 0 1 {0} = 0 := by
      rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
      exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
    rw [hzero, tsub_zero, ← h2, arccos_neg_one, div_self hpi.ne', ENNReal.ofReal_one]
  -- the main case `-1 < ⟪u, v⟫ < 1`
  set ρ := inner ℝ u v with hρ
  have hp : 0 < ‖u + v‖ := by
    have : 0 < ‖u + v‖ ^ 2 := by rw [hsum]; linarith
    nlinarith [norm_nonneg (u + v)]
  have hq : 0 < ‖v - u‖ := by
    have : 0 < ‖v - u‖ ^ 2 := by rw [hdiff]; linarith
    nlinarith [norm_nonneg (v - u)]
  set e₁ : E := ‖u + v‖⁻¹ • (u + v) with he₁
  set e₂ : E := ‖v - u‖⁻¹ • (v - u) with he₂
  have hn₁ : ‖e₁‖ = 1 := by rw [he₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp.ne']
  have hn₂ : ‖e₂‖ = 1 := by rw [he₂, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hq.ne']
  have h₁₂ : inner ℝ e₁ e₂ = 0 := by
    rw [he₁, he₂, real_inner_smul_left, real_inner_smul_right]
    have : inner ℝ (u + v) (v - u) = (0 : ℝ) := by
      rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, hu, hv, real_inner_comm u v]
      ring
    rw [this, mul_zero, mul_zero]
  set c := ‖u + v‖ / 2 with hc
  set s := ‖v - u‖ / 2 with hs
  have hinner : ∀ r : E, inner ℝ u r = c * inner ℝ e₁ r - s * inner ℝ e₂ r ∧
      inner ℝ v r = c * inner ℝ e₁ r + s * inner ℝ e₂ r := by
    intro r
    rw [he₁, he₂, real_inner_smul_left, real_inner_smul_left, inner_add_left, inner_sub_left]
    have hp' : c * ‖u + v‖⁻¹ = 1 / 2 := by rw [hc]; field_simp
    have hq' : s * ‖v - u‖⁻¹ = 1 / 2 := by rw [hs]; field_simp
    constructor
    · rw [← mul_assoc, ← mul_assoc, hp', hq']; ring
    · rw [← mul_assoc, ← mul_assoc, hp', hq']; ring
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, div_pow, div_pow, hsum, hdiff]; ring
  have hc0 : 0 < c := by rw [hc]; positivity
  have hs0 : 0 < s := by rw [hs]; positivity
  have hc1 : c < 1 := by nlinarith
  set a := arccos c with ha
  have ha0 : 0 < a := arccos_pos.2 hc1
  have ha1 : a < π / 2 := arccos_lt_pi_div_two.2 hc0
  have hcos : cos a = c := cos_arccos (by linarith) hc1.le
  have hsin : sin a = s := by
    rw [ha, sin_arccos, show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq hs0.le]
  have hset : {r : E | (0 ≤ inner ℝ u r) ≠ (0 ≤ inner ℝ v r)} =
      (fun r => (inner ℝ e₁ r, inner ℝ e₂ r)) ⁻¹'
        {p : ℝ × ℝ | (0 ≤ cos a * p.1 - sin a * p.2) ≠ (0 ≤ cos a * p.1 + sin a * p.2)} := by
    ext r
    simp only [mem_ofPred_eq, mem_preimage, hcos, hsin, (hinner r).1, (hinner r).2]
  have hT : Measurable fun r : E => (inner ℝ e₁ r, inner ℝ e₂ r) :=
    ((continuous_const.inner continuous_id).prodMk
      (continuous_const.inner continuous_id)).measurable
  rw [hset, ← Measure.map_apply hT (measurableSet_sign_ne (by fun_prop) (by fun_prop)),
    map_inner_pair_stdGaussian hn₁ hn₂ h₁₂, gaussianReal_prod_wedge ha0 ha1]
  congr 1
  have h2a : arccos ρ = 2 * a := by
    have : ρ = cos (2 * a) := by
      rw [cos_two_mul, hcos]
      have : c ^ 2 = (2 + 2 * ρ) / 4 := by rw [hc, div_pow, hsum]; ring
      rw [this]; ring
    rw [this, arccos_cos (by linarith) (by linarith)]
  rw [h2a]

/-- **Hyperplanes through the origin are null for the standard Gaussian.** For a unit vector `u`,
the set `{r : ⟪u, r⟫ = 0}` has standard Gaussian measure `0`. -/
theorem stdGaussian_inner_eq_zero {u : E} (hu : ‖u‖ = 1) :
    stdGaussian E {r | inner ℝ u r = 0} = 0 := by
  have hmeas : Measurable fun r : E => inner ℝ u r :=
    (continuous_const.inner continuous_id).measurable
  have : {r : E | inner ℝ u r = 0} = (fun r => inner ℝ u r) ⁻¹' {0} := rfl
  rw [this, ← Measure.map_apply hmeas (measurableSet_singleton 0), map_inner_stdGaussian hu,
    gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact withDensity_absolutelyContinuous _ _ Real.volume_singleton

/-- **Quadrant probability for two directions.** For unit vectors `u`, `v` of a
finite-dimensional real inner product space and a standard Gaussian vector `r`,
`P[⟪u, r⟫ > 0, ⟪v, r⟫ > 0] = 1/4 + arcsin ⟪u, v⟫ / (2π)`. The proof combines
`stdGaussian_sign_ne` with the symmetry `r ↦ -r` and the nullity of hyperplanes. -/
theorem stdGaussian_pos_pos {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).real {r | 0 < inner ℝ u r ∧ 0 < inner ℝ v r} =
      1 / 4 + arcsin (inner ℝ u v) / (2 * π) := by
  have hpi := pi_pos
  set μ := stdGaussian E
  have hcu : Continuous fun r : E => inner ℝ u r := continuous_const.inner continuous_id
  have hcv : Continuous fun r : E => inner ℝ v r := continuous_const.inner continuous_id
  set P := {r : E | 0 < inner ℝ u r ∧ 0 < inner ℝ v r} with hP
  set TT := {r : E | 0 ≤ inner ℝ u r ∧ 0 ≤ inner ℝ v r} with hTT
  set FF := {r : E | inner ℝ u r < 0 ∧ inner ℝ v r < 0} with hFF
  set D := {r : E | (0 ≤ inner ℝ u r) ≠ (0 ≤ inner ℝ v r)} with hD
  have hPm : MeasurableSet P :=
    (measurableSet_lt measurable_const hcu.measurable).inter
      (measurableSet_lt measurable_const hcv.measurable)
  have hTTm : MeasurableSet TT :=
    (measurableSet_le measurable_const hcu.measurable).inter
      (measurableSet_le measurable_const hcv.measurable)
  have hFFm : MeasurableSet FF :=
    (measurableSet_lt hcu.measurable measurable_const).inter
      (measurableSet_lt hcv.measurable measurable_const)
  have hDm : MeasurableSet D := measurableSet_sign_ne hcu hcv
  -- `FF` is the reflection of `P`
  have hFF_eq : μ.real FF = μ.real P := by
    have hneg : μ.map (LinearIsometryEquiv.neg ℝ (E := E)) = μ := stdGaussian_map _
    have hpre : (LinearIsometryEquiv.neg ℝ (E := E)) ⁻¹' P = FF := by
      ext r
      simp [hP, hFF, inner_neg_right]
    rw [← hpre, ← map_measureReal_apply
      (LinearIsometryEquiv.neg ℝ (E := E)).continuous.measurable hPm, hneg]
  -- `TT` and `P` differ by a null set
  have hTT_eq : μ.real TT = μ.real P := by
    have hsub : P ⊆ TT := fun r hr => ⟨hr.1.le, hr.2.le⟩
    have hnull : μ (TT \ P) = 0 := by
      refine measure_mono_null (t := {r | inner ℝ u r = 0} ∪ {r | inner ℝ v r = 0}) ?_
        (measure_union_null (stdGaussian_inner_eq_zero hu) (stdGaussian_inner_eq_zero hv))
      rintro r ⟨⟨h1, h2⟩, h3⟩
      by_contra hc
      simp only [mem_union, mem_ofPred_eq, not_or] at hc
      exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 (Ne.symm hc.2)⟩
    rw [← measureReal_sdiff_add_inter hPm, inter_eq_right.2 hsub, measureReal_def,
      hnull, ENNReal.toReal_zero, zero_add]
  -- the complement of `D` is `TT ∪ FF`
  have hDc : Dᶜ = TT ∪ FF := by
    ext r
    simp only [hD, hTT, hFF, mem_compl_iff, mem_ofPred_eq, mem_union, ne_eq, eq_iff_iff,
      not_not]
    constructor
    · intro h
      by_cases h1 : 0 ≤ inner ℝ u r
      · exact Or.inl ⟨h1, h.1 h1⟩
      · right
        refine ⟨lt_of_not_ge h1, lt_of_not_ge fun h2 => h1 (h.2 h2)⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · exact ⟨fun h => absurd h (not_le.2 h1), fun h => absurd h (not_le.2 h2)⟩
  have hdisj : Disjoint TT FF := by
    rw [Set.disjoint_left]
    rintro r ⟨h1, _⟩ ⟨h3, _⟩
    linarith
  have htot : μ.real D + μ.real Dᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hDm, probReal_univ]
  rw [hDc, measureReal_union hdisj hFFm, hTT_eq, hFF_eq] at htot
  have hDval : μ.real D = arccos (inner ℝ u v) / π := by
    rw [measureReal_def, stdGaussian_sign_ne hu hv,
      ENNReal.toReal_ofReal (div_nonneg (arccos_nonneg _) hpi.le)]
  rw [hDval, arccos_eq_pi_div_two_sub_arcsin] at htot
  field_simp at htot ⊢
  linarith

end MathlibExt.Probability.Distributions.StdGaussianHyperplane
