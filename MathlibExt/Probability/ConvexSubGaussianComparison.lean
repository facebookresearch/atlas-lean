/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

/-!
# One-dimensional convex comparison under a sub-Gaussian tail bound

The comparator parameter is the variance factor `C`, so the standard Gaussian is scaled
by `sqrt C`. The Davis–Power equation data and the sharp comparison requests live in the
`WantedExt` module `ConvexSubGaussianComparisonWanted`.
-/

universe u

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace MathlibExt.Probability.ConvexSubGaussianComparison

/-- A measurable, integrable, centered random variable with the strict two-sided tail bound. -/
structure IsOneSubGaussianTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) : Prop where
  measurable : Measurable X
  integrable : Integrable X μ
  mean_zero : ∫ ω, X ω ∂μ = 0
  tail_le : ∀ t : ℝ, 0 ≤ t →
    μ {ω | |X ω| > t} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))

/-- Convex order between real random variables, for convex tests with both expectations finite. -/
def ConvexDominated {ΩX ΩY : Type*}
    [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (μX : Measure ΩX) (X : ΩX → ℝ) (μY : Measure ΩY) (Y : ΩY → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ConvexOn ℝ univ f →
    Integrable (fun ω => f (X ω)) μX →
    Integrable (fun ω => f (Y ω)) μY →
    (∫ ω, f (X ω) ∂μX) ≤ ∫ ω, f (Y ω) ∂μY

theorem ConvexDominated.refl {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ConvexDominated μ X μ X := by
  intro f _ _ _
  exact le_rfl

/-- A positive finite variance factor comparing every admissible law to `sqrt C * G`. -/
def IsAdmissibleConstant (C : ENNReal) : Prop :=
  C ≠ ⊤ ∧ 0 < C ∧
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ),
      IsOneSubGaussianTail μ X →
        ConvexDominated μ X (gaussianReal 0 1) (fun g : ℝ => Real.sqrt C.toReal * g)

/-- The infimum of positive finite comparator variance factors; an empty family gives `top`. -/
noncomputable def comparisonConstant : ENNReal :=
  sInf {C : ENNReal | IsAdmissibleConstant C}

theorem comparisonConstant_le_of_isAdmissibleConstant {C : ENNReal}
    (hC : IsAdmissibleConstant C) : comparisonConstant ≤ C :=
  sInf_le hC

theorem le_comparisonConstant_iff (C : ENNReal) :
    C ≤ comparisonConstant ↔ ∀ D : ENNReal, IsAdmissibleConstant D → C ≤ D :=
  le_sInf_iff

theorem comparisonConstant_eq_top_iff :
    comparisonConstant = ⊤ ↔ ∀ C : ENNReal, ¬IsAdmissibleConstant C := by
  constructor
  · intro h C hC
    have htop : ⊤ ≤ C := h ▸ comparisonConstant_le_of_isAdmissibleConstant hC
    exact hC.1 (top_le_iff.mp htop)
  · intro h
    apply top_le_iff.mp
    exact (le_comparisonConstant_iff ⊤).2 (fun C hC => (h C hC).elim)

@[simp] theorem not_isAdmissibleConstant_zero : ¬IsAdmissibleConstant 0 := by
  simp [IsAdmissibleConstant]

@[simp] theorem not_isAdmissibleConstant_top : ¬IsAdmissibleConstant ⊤ := by
  simp [IsAdmissibleConstant]

/-- The capped tail envelope from the probability tail constraint. -/
noncomputable def gaussianTailEnvelope (t : ℝ) : ℝ :=
  min 1 (2 * Real.exp (-t ^ 2 / 2))

theorem IsOneSubGaussianTail.tail_le_envelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : IsOneSubGaussianTail μ X) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | |X ω| > t} ≤ ENNReal.ofReal (gaussianTailEnvelope t) := by
  by_cases h : 1 ≤ 2 * Real.exp (-t ^ 2 / 2)
  · rw [gaussianTailEnvelope, min_eq_left h, ENNReal.ofReal_one]
    calc μ {ω | |X ω| > t} ≤ μ univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  · rw [gaussianTailEnvelope, min_eq_right (le_of_not_ge h)]
    exact hX.tail_le t ht

theorem IsOneSubGaussianTail.zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsOneSubGaussianTail μ (fun _ : Ω => 0) := by
  refine ⟨measurable_const, integrable_const 0, by simp, ?_⟩
  intro t ht
  have h : ({_ω : Ω | |(0 : ℝ)| > t} : Set Ω) = ∅ := by
    ext ω
    simp [not_lt.mpr ht]
  rw [h]
  simp

theorem IsOneSubGaussianTail.of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hmgf : HasSubgaussianMGF X 1 μ)
    (hmean : ∫ ω, X ω ∂μ = 0) : IsOneSubGaussianTail μ X := by
  refine ⟨hX, hmgf.integrable, hmean, ?_⟩
  intro t ht
  have hright : μ {ω | t ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
    rw [← ofReal_measureReal (μ := μ) (s := {ω | t ≤ X ω})]
    exact ENNReal.ofReal_le_ofReal (by simpa using hmgf.measure_ge_le ht)
  have hleft : μ {ω | t ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
    rw [← ofReal_measureReal (μ := μ) (s := {ω | t ≤ -X ω})]
    exact ENNReal.ofReal_le_ofReal (by simpa using hmgf.neg.measure_ge_le ht)
  have hsubset : {ω | |X ω| > t} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    by_cases hsign : 0 ≤ X ω
    · exact Or.inl (le_of_lt (by simpa [abs_of_nonneg hsign] using hω))
    · exact Or.inr (le_of_lt (by simpa [abs_of_neg (lt_of_not_ge hsign)] using hω))
  calc μ {ω | |X ω| > t} ≤ μ ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measure_mono hsubset
    _ ≤ μ {ω | t ≤ X ω} + μ {ω | t ≤ -X ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := add_le_add hright hleft
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

/-- The standard Gaussian's quadratic test forces every comparator to be at least one. -/
theorem one_le_of_isAdmissibleConstant {C : ENNReal} (hC : IsAdmissibleConstant C) :
    1 ≤ C := by
  have hmgf : HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) := by
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, ?_⟩
    intro t
    simp [mgf_fun_id_gaussianReal]
  have hX : IsOneSubGaussianTail (gaussianReal 0 1) (fun x : ℝ => x) :=
    IsOneSubGaussianTail.of_hasSubgaussianMGF measurable_id hmgf (by simp)
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).1 (hmgf.memLp 2)
  have hvariance : Var[fun x : ℝ => x; gaussianReal 0 1] = 1 := by simp
  have hquadratic : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    rw [variance_eq_integral (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) measurable_id.aemeasurable] at hvariance
    simpa using hvariance
  have hscaled : Integrable (fun x : ℝ => (Real.sqrt C.toReal * x) ^ 2)
      (gaussianReal 0 1) := by
    simpa only [mul_pow] using hint.const_mul (Real.sqrt C.toReal ^ 2)
  have hscaled_integral :
      (∫ x : ℝ, (Real.sqrt C.toReal * x) ^ 2 ∂gaussianReal 0 1) = C.toReal := by
    simp only [mul_pow, integral_const_mul, hquadratic, mul_one,
      Real.sq_sqrt ENNReal.toReal_nonneg]
  have hconvex : ConvexOn ℝ univ (fun x : ℝ => x ^ 2) :=
    (show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow
  have hcomparison := hC.2.2 ℝ (gaussianReal 0 1) (fun x : ℝ => x) hX
    (fun x : ℝ => x ^ 2) hconvex hint hscaled
  rw [hquadratic, hscaled_integral] at hcomparison
  calc
    (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    _ ≤ ENNReal.ofReal C.toReal := ENNReal.ofReal_le_ofReal hcomparison
    _ = C := ENNReal.ofReal_toReal hC.1

/-- The Gaussian lower bound also holds if the comparator family is empty. -/
theorem one_le_comparisonConstant : (1 : ENNReal) ≤ comparisonConstant :=
  (le_comparisonConstant_iff 1).2 (fun _ hC => one_le_of_isAdmissibleConstant hC)

/-- Universe-polymorphic form of admissibility: an admissible constant also compares
admissible variables on sample spaces in any universe, by pushing the law of the
variable forward to a probability measure on `ℝ`. -/
theorem IsAdmissibleConstant.elim {C : ENNReal} (hC : IsAdmissibleConstant C)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : IsOneSubGaussianTail μ X) :
    ConvexDominated μ X (gaussianReal 0 1) (fun g : ℝ => Real.sqrt C.toReal * g) := by
  haveI : IsProbabilityMeasure (μ.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.measurable.aemeasurable).mpr inferInstance
  have hlaw : IsOneSubGaussianTail (μ.map X) (id : ℝ → ℝ) := by
    refine ⟨measurable_id, ?_, ?_, ?_⟩
    · exact (integrable_map_measure measurable_id.aestronglyMeasurable
        hX.measurable.aemeasurable).mpr hX.integrable
    · rw [integral_map hX.measurable.aemeasurable measurable_id.aestronglyMeasurable]
      exact hX.mean_zero
    · intro t ht
      rw [Measure.map_apply hX.measurable
        (measurableSet_lt measurable_const (by fun_prop))]
      exact hX.tail_le t ht
  intro f hf hIntX hIntY
  have hfcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hIntLaw : Integrable f (μ.map X) :=
    (integrable_map_measure hfcont.aestronglyMeasurable
      hX.measurable.aemeasurable).mpr hIntX
  have hdom := hC.2.2 ℝ (μ.map X) (id : ℝ → ℝ) hlaw f hf hIntLaw hIntY
  have hmap : (∫ ω, f (X ω) ∂μ) = ∫ y, f y ∂(μ.map X) :=
    (integral_map hX.measurable.aemeasurable hfcont.aestronglyMeasurable).symm
  rw [hmap]
  exact hdom

/-- Saturation of the actual strict-tail event at every nonnegative threshold. -/
def SaturatesGaussianTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    μ {ω | |X ω| > t} = ENNReal.ofReal (gaussianTailEnvelope t)

end MathlibExt.Probability.ConvexSubGaussianComparison
