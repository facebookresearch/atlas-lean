/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerUpperBound
public import MathlibExt.Probability.LegendreTransform
public import MathlibExt.Probability.LargeDeviationPrinciple
public import Mathlib.Analysis.Convex.Integral

/-!
# Extended log moments and the Cramér conjugate

The exponential moment is a nonnegative lintegral, and its logarithm is
`EReal`-valued. Infinite moments have log `⊤`. At integrable directions on a
probability space, this equals the embedding of the canonical real expression
`CramerUpperBound.logMGFVec`; that real expression is not used outside its
finite domain to define the primary rate.

The primary rate converts the existing extended-real
`LegendreTransform.legendreTransform` to `ℝ≥0∞`, preserving `⊤`. Under
probability, the zero direction makes the conjugate nonnegative, so this
conversion preserves its full extended value. The existing LDP rate-function
interface supplies the regularity conclusion. No large-deviation bound is
claimed here.

Source: the Lecture 13 Cramér target and
`v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean`. Its totalized real
logarithm and real conditional supremum are corrected separately. The
fixed-direction real log moment, canonical conjugate and LDP structures are
already present on the base and are reused. Global exponential integrability
appears only on particular finite-agreement and mean corollaries, and is not
an assumption of the definitions or general rate-function results.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MathlibExt.Probability.CramerRateFunction

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Extended log moment: nonintegrable measurable exponential moments give `⊤`. -/
noncomputable def extendedLogMGFVec {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (t : EuclideanSpace ℝ (Fin d)) : EReal :=
  ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp ⟪t, X ω⟫_ℝ) ∂μ)

/-- The canonical extended conjugate, converted with top preserved. -/
noncomputable def cramerRateFunction {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  (MathlibExt.Probability.LegendreTransform.legendreTransform (extendedLogMGFVec X μ) x).toENNReal

/-- The canonical real log moment is zero at the zero direction. -/
theorem logMGFVec_zero {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] :
    MathlibExt.Probability.CramerUpperBound.logMGFVec X μ 0 = 0 := by
  simp [MathlibExt.Probability.CramerUpperBound.logMGFVec]

/-- The canonical real log moment of a constant vector. -/
theorem logMGFVec_const {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] (t : EuclideanSpace ℝ (Fin d)) :
    MathlibExt.Probability.CramerUpperBound.logMGFVec (fun _ => c) μ t = ⟪t, c⟫_ℝ := by
  simp [MathlibExt.Probability.CramerUpperBound.logMGFVec, integral_const, Measure.real]

/-- Finite directions compose with the existing fixed-direction Chernoff API. -/
theorem extendedLogMGFVec_eq_coe_logMGFVec {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    {t : EuclideanSpace ℝ (Fin d)}
    (hInt : Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ) :
    extendedLogMGFVec X μ t =
      ((MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t : ℝ) : EReal) := by
  have hpos : 0 < ∫ ω, Real.exp ⟪t, X ω⟫_ℝ ∂μ := by
    have h := ProbabilityTheory.mgf_pos (μ := μ) (X := fun ω => ⟪t, X ω⟫_ℝ)
      (t := 1) (by simpa using hInt)
    simpa [ProbabilityTheory.mgf] using h
  unfold extendedLogMGFVec MathlibExt.Probability.CramerUpperBound.logMGFVec
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun ω => Real.exp_nonneg _)]
  exact ENNReal.log_ofReal_of_pos hpos

/-- Measurability separates infinite moments from nonmeasurable totalized integrals. -/
theorem extendedLogMGFVec_eq_top_of_not_integrable {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω)
    {t : EuclideanSpace ℝ (Fin d)}
    (hmeas : AEStronglyMeasurable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ)
    (hInt : ¬ Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ) :
    extendedLogMGFVec X μ t = ⊤ := by
  have htop : (∫⁻ ω, ENNReal.ofReal (Real.exp ⟪t, X ω⟫_ℝ) ∂μ) = ⊤ := by
    by_contra h
    apply hInt
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => Real.exp_nonneg _)]
    exact lt_top_iff_ne_top.mpr h
  simp [extendedLogMGFVec, htop]

/-- The zero direction has extended log moment zero under probability. -/
theorem extendedLogMGFVec_zero {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] : extendedLogMGFVec X μ 0 = 0 := by
  simp [extendedLogMGFVec]

/-- Extended log moments of constant vectors retain the exact inner product. -/
theorem extendedLogMGFVec_const {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] (t : EuclideanSpace ℝ (Fin d)) :
    extendedLogMGFVec (fun _ => c) μ t = ((⟪t, c⟫_ℝ : ℝ) : EReal) := by
  rw [extendedLogMGFVec_eq_coe_logMGFVec _ (integrable_const _), logMGFVec_const]

/-- The nonnegative conversion commutes with extended suprema. -/
private theorem toENNReal_iSup {ι : Sort*} (f : ι → EReal) :
    (⨆ i, f i).toENNReal = ⨆ i, (f i).toENNReal := by
  apply le_antisymm
  · have h : (⨆ i, f i) ≤ ((⨆ i, (f i).toENNReal : ℝ≥0∞) : EReal) := by
      apply iSup_le
      intro i
      have hi : f i ≤ ((f i).toENNReal : EReal) := by
        rw [EReal.coe_toENNReal_eq_max]
        exact le_max_right _ _
      exact hi.trans (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        (le_iSup (fun j => (f j).toENNReal) i))
    simpa using EReal.toENNReal_le_toENNReal h
  · exact iSup_le fun i => EReal.toENNReal_le_toENNReal (le_iSup f i)

/-- Supporting terms are obtained from the canonical conjugate, not a second transform. -/
theorem cramerRateFunction_eq_iSup {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x : EuclideanSpace ℝ (Fin d)) :
    cramerRateFunction X μ x =
      ⨆ t, (((⟪t, x⟫_ℝ : ℝ) : EReal) - extendedLogMGFVec X μ t).toENNReal := by
  unfold cramerRateFunction
  rw [MathlibExt.Probability.LegendreTransform.legendreTransform_eq_iSup, toENNReal_iSup]

/-- Extended Fenchel–Young, valid for every measure and every direction. -/
theorem le_cramerRateFunction {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x t : EuclideanSpace ℝ (Fin d)) :
    (((⟪t, x⟫_ℝ : ℝ) : EReal) - extendedLogMGFVec X μ t).toENNReal ≤
      cramerRateFunction X μ x :=
  EReal.toENNReal_le_toENNReal MathlibExt.Probability.LegendreTransform.le_legendreTransform

/-- The original real supporting term remains valid at integrable directions. -/
theorem le_cramerRateFunction_of_integrable {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    (x t : EuclideanSpace ℝ (Fin d))
    (hInt : Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ) :
    ENNReal.ofReal (⟪t, x⟫_ℝ - MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t) ≤
      cramerRateFunction X μ x := by
  have h := le_cramerRateFunction X μ x t
  rw [extendedLogMGFVec_eq_coe_logMGFVec X hInt, ← EReal.coe_sub,
    EReal.real_coe_toENNReal] at h
  exact h

/-- Probability makes the canonical conjugate nonnegative via the zero direction. -/
theorem legendreTransform_extendedLogMGFVec_nonneg {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ MathlibExt.Probability.LegendreTransform.legendreTransform (extendedLogMGFVec X μ) x := by
  have h := MathlibExt.Probability.LegendreTransform.le_legendreTransform
    (Λ := extendedLogMGFVec X μ) (x := x) (l := 0)
  simpa [extendedLogMGFVec_zero] using h

/-- Under probability the conversion preserves the entire nonnegative conjugate. -/
theorem coe_cramerRateFunction {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ (Fin d)) :
    ((cramerRateFunction X μ x : ℝ≥0∞) : EReal) =
      MathlibExt.Probability.LegendreTransform.legendreTransform (extendedLogMGFVec X μ) x :=
  EReal.coe_toENNReal (legendreTransform_extendedLogMGFVec_nonneg X x)

/-- Nonnegative conversion retains lower semicontinuity of a canonical conjugate. -/
private theorem lowerSemicontinuous_conjugate_toENNReal {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → EReal) :
    LowerSemicontinuous (fun x =>
      (MathlibExt.Probability.LegendreTransform.legendreTransform Λ x).toENNReal) := by
  have heq : (fun x =>
      (MathlibExt.Probability.LegendreTransform.legendreTransform Λ x).toENNReal) =
      fun x => ⨆ t, (((⟪t, x⟫_ℝ : ℝ) : EReal) - Λ t).toENNReal := by
    funext x
    rw [MathlibExt.Probability.LegendreTransform.legendreTransform_eq_iSup, toENNReal_iSup]
  rw [heq]
  apply lowerSemicontinuous_iSup
  intro t
  by_cases htop : Λ t = ⊤
  · simpa only [htop, EReal.sub_top, EReal.toENNReal_bot] using
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ≥0∞))).lowerSemicontinuous
  by_cases hbot : Λ t = ⊥
  · simpa only [hbot, EReal.sub_bot (EReal.coe_ne_bot _), EReal.toENNReal_top] using
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ (Fin d) => (⊤ : ℝ≥0∞))).lowerSemicontinuous
  lift Λ t to ℝ using ⟨htop, hbot⟩ with r hr
  simp only [← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (⟪t, x⟫_ℝ - r)) := by
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  exact hc.lowerSemicontinuous

/-- Converted canonical conjugates are lower semicontinuous for arbitrary input data. -/
theorem lowerSemicontinuous_cramerRateFunction {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) :
    LowerSemicontinuous (cramerRateFunction X μ) :=
  lowerSemicontinuous_conjugate_toENNReal (extendedLogMGFVec X μ)

/-- A finite converted value is a real upper level for the original extended value. -/
private theorem le_real_level {z : EReal} (hz : z.toENNReal ≠ ⊤) :
    z ≤ ((z.toENNReal.toReal : ℝ) : EReal) := by
  have hle : z ≤ ((z.toENNReal : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_toENNReal_eq_max]
    exact le_max_right _ _
  have hcoe : ((z.toENNReal : ℝ≥0∞) : EReal) = ((z.toENNReal.toReal : ℝ) : EReal) := by
    calc ((z.toENNReal : ℝ≥0∞) : EReal)
        = ((ENNReal.ofReal z.toENNReal.toReal : ℝ≥0∞) : EReal) :=
          congrArg (fun a : ℝ≥0∞ => (a : EReal)) (ENNReal.ofReal_toReal hz).symm
      _ = max ((z.toENNReal.toReal : ℝ) : EReal) 0 := EReal.coe_ennreal_ofReal
      _ = ((z.toENNReal.toReal : ℝ) : EReal) :=
        max_eq_left (by exact_mod_cast ENNReal.toReal_nonneg (a := z.toENNReal))
  exact hcoe ▸ hle

/-- Nonnegative conversion transports a canonical real-threshold convex epigraph. -/
private theorem convex_toENNReal_of_epigraph {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EReal)
    (hf : Convex ℝ {p : EuclideanSpace ℝ (Fin d) × ℝ | f p.1 ≤ (p.2 : EReal)})
    {x y : EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (f (a • x + b • y)).toENNReal ≤
      ENNReal.ofReal a * (f x).toENNReal + ENNReal.ofReal b * (f y).toENNReal := by
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    subst b
    simp only [zero_smul, one_smul, zero_add, ENNReal.ofReal_zero,
      ENNReal.ofReal_one, zero_mul, one_mul, le_refl]
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by linarith
    subst a
    simp only [zero_smul, one_smul, add_zero, ENNReal.ofReal_zero,
      ENNReal.ofReal_one, zero_mul, one_mul, le_refl]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases hx : (f x).toENNReal = ⊤
  · have ha' : ENNReal.ofReal a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hap)
    rw [hx, ENNReal.mul_top ha', top_add]
    exact le_top
  by_cases hy : (f y).toENNReal = ⊤
  · have hb' : ENNReal.ofReal b ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hbp)
    rw [hy, ENNReal.mul_top hb', add_top]
    exact le_top
  have hxl := le_real_level (z := f x) hx
  have hyl := le_real_level (z := f y) hy
  have hpx : (x, (f x).toENNReal.toReal) ∈
      {p : EuclideanSpace ℝ (Fin d) × ℝ | f p.1 ≤ (p.2 : EReal)} := hxl
  have hpy : (y, (f y).toENNReal.toReal) ∈
      {p : EuclideanSpace ℝ (Fin d) × ℝ | f p.1 ≤ (p.2 : EReal)} := hyl
  have hc := hf hpx hpy ha hb hab
  change f (a • x + b • y) ≤
    ((a * (f x).toENNReal.toReal + b * (f y).toENNReal.toReal : ℝ) : EReal) at hc
  have hn := EReal.toENNReal_le_toENNReal hc
  change (f (a • x + b • y)).toENNReal ≤ _ at hn
  rw [EReal.real_coe_toENNReal] at hn
  calc (f (a • x + b • y)).toENNReal
      ≤ ENNReal.ofReal (a * ((f x).toENNReal).toReal +
          b * ((f y).toENNReal).toReal) := hn
    _ = ENNReal.ofReal a * (f x).toENNReal +
        ENNReal.ofReal b * (f y).toENNReal := by
      rw [ENNReal.ofReal_add (mul_nonneg ha ENNReal.toReal_nonneg)
        (mul_nonneg hb ENNReal.toReal_nonneg), ENNReal.ofReal_mul ha,
        ENNReal.ofReal_mul hb, ENNReal.ofReal_toReal hx, ENNReal.ofReal_toReal hy]

/-- Convexity is transported from the actual canonical conjugate epigraph. -/
theorem cramerRateFunction_convex {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) {x y : EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cramerRateFunction X μ (a • x + b • y) ≤
      ENNReal.ofReal a * cramerRateFunction X μ x +
        ENNReal.ofReal b * cramerRateFunction X μ y :=
  convex_toENNReal_of_epigraph _
    (MathlibExt.Probability.LegendreTransform.convex_epi_legendreTransform
      (extendedLogMGFVec X μ)) ha hb hab

/-- The existing LDP convex-rate structure is available without global MGF finiteness. -/
theorem isConvexRateFunction_cramerRateFunction {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) :
    MathlibExt.Probability.LargeDeviationPrinciple.IsConvexRateFunction
      (cramerRateFunction X μ) :=
  ⟨⟨lowerSemicontinuous_cramerRateFunction X μ⟩,
    fun _ _ _ _ ha hb hab => cramerRateFunction_convex X μ ha hb hab⟩

/-- With all moments integrable, the canonical real expression represents every direction. -/
theorem cramerRateFunction_eq_iSup_of_integrable {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ)
    (x : EuclideanSpace ℝ (Fin d)) :
    cramerRateFunction X μ x =
      ⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t) := by
  rw [cramerRateFunction_eq_iSup]
  congr 1
  funext t
  rw [extendedLogMGFVec_eq_coe_logMGFVec X (hInt t), ← EReal.coe_sub,
    EReal.real_coe_toENNReal]

/-- Bounded real values commute with the nonnegative supremum. -/
private theorem iSup_ofReal_eq_ofReal_iSup {ι : Type*} [Nonempty ι]
    (f : ι → ℝ) (hbdd : BddAbove (Set.range f)) :
    (⨆ i, ENNReal.ofReal (f i)) = ENNReal.ofReal (⨆ i, f i) := by
  obtain ⟨B, hB⟩ := hbdd
  have hle : ∀ i, f i ≤ B := fun i => hB (Set.mem_range_self i)
  have hS : (⨆ i, ENNReal.ofReal (f i)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun i => ENNReal.ofReal_le_ofReal (hle i))
  have hmax : BddAbove (Set.range fun i => max (f i) 0) :=
    ⟨max B 0, fun _ ⟨i, hi⟩ => by rw [← hi]; exact max_le_max (hle i) le_rfl⟩
  have hreal : (⨆ i, f i) ≤ ⨆ i, max (f i) 0 := by
    apply ciSup_le
    intro i
    exact (le_max_left _ _).trans (le_ciSup hmax i)
  apply le_antisymm
  · exact iSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup ⟨B, hB⟩ i)
  · rw [ENNReal.ofReal_le_iff_le_toReal hS,
      ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal']
    exact hreal

/-- Physical finite-domain agreement: bounded real supporting values and integrable moments.
The finiteness premise belongs to this corollary, not the corrected definitions. -/
theorem cramerRateFunction_eq_ofReal_iSup {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hbdd : BddAbove (Set.range fun t =>
      ⟪t, x⟫_ℝ - MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t)) :
    cramerRateFunction X μ x =
      ENNReal.ofReal (⨆ t, ⟪t, x⟫_ℝ - MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t) := by
  rw [cramerRateFunction_eq_iSup_of_integrable X hInt x]
  exact iSup_ofReal_eq_ofReal_iSup _ hbdd

/-- The original integrable-vector and moment premises imply zero rate at the mean. -/
theorem cramerRateFunction_eq_zero_at_mean {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    (hX : Integrable X μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ) :
    cramerRateFunction X μ (∫ ω, X ω ∂μ) = 0 := by
  have hterm : ∀ t : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (⟪t, ∫ ω, X ω ∂μ⟫_ℝ -
        MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t) = 0 := by
    intro t
    rw [ENNReal.ofReal_eq_zero]
    have hinner : ⟪t, ∫ ω, X ω ∂μ⟫_ℝ = ∫ ω, ⟪t, X ω⟫_ℝ ∂μ := by
      have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ t) hX
      simp only [innerSL_apply_apply] at h
      exact h.symm
    have hfi : Integrable (fun ω => ⟪t, X ω⟫_ℝ) μ :=
      (innerSL ℝ t).integrable_comp hX
    have hj : Real.exp (∫ ω, ⟪t, X ω⟫_ℝ ∂μ) ≤ ∫ ω, Real.exp ⟪t, X ω⟫_ℝ ∂μ :=
      ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn
        isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi (hInt t)
    have hlog : ⟪t, ∫ ω, X ω ∂μ⟫_ℝ ≤
        MathlibExt.Probability.CramerUpperBound.logMGFVec X μ t := by
      unfold MathlibExt.Probability.CramerUpperBound.logMGFVec
      rw [← Real.log_exp (⟪t, ∫ ω, X ω ∂μ⟫_ℝ)]
      exact Real.log_le_log (Real.exp_pos _) (by rw [hinner]; exact hj)
    exact sub_nonpos.mpr hlog
  rw [cramerRateFunction_eq_iSup_of_integrable X hInt]
  simp_rw [hterm]
  simp

/-- Constant laws retain zero at their center and top elsewhere,
including dimension zero. -/
theorem cramerRateFunction_const {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] :
    cramerRateFunction (fun _ => c) μ c = 0 ∧
    ∀ x : EuclideanSpace ℝ (Fin d),
      x ≠ c → cramerRateFunction (fun _ => c) μ x = ⊤ := by
  have hconj : ∀ x : EuclideanSpace ℝ (Fin d),
      MathlibExt.Probability.LegendreTransform.legendreTransform
        (extendedLogMGFVec (fun _ : Ω => c) μ) x =
      MathlibExt.Probability.LegendreTransform.legendreTransform (fun _ => (0 : EReal)) (x - c) := by
    intro x
    rw [MathlibExt.Probability.LegendreTransform.legendreTransform_eq_iSup,
      MathlibExt.Probability.LegendreTransform.legendreTransform_eq_iSup]
    congr 1
    funext t
    rw [extendedLogMGFVec_const, sub_zero, ← EReal.coe_sub, inner_sub_right]
  refine ⟨?_, fun x hx => ?_⟩
  · unfold cramerRateFunction
    rw [hconj, sub_self, MathlibExt.Probability.LegendreTransform.legendreTransform_zero,
      EReal.toENNReal_zero]
  · unfold cramerRateFunction
    rw [hconj, MathlibExt.Probability.LegendreTransform.legendreTransform_zero_of_ne
      (sub_ne_zero.mpr hx), EReal.toENNReal_top]

end MathlibExt.Probability.CramerRateFunction
