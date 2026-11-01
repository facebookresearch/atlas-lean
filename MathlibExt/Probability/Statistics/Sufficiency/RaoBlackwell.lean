/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# The Rao–Blackwell theorem

Conditioning an estimator on a sufficient statistic never increases its risk under a loss that
is convex in the estimate, and keeps its mean.

For one probability measure `μ` and a sub-σ-algebra `m`, conditional Jensen gives
`∫ L(μ[W | m]) ≤ ∫ L(W)` for convex `L` (`integral_comp_condExp_le`), and under squared error
the risk splits exactly (`integral_sq_sub_eq_add`):

`E (W - c)² = E (μ[W | m] - c)² + E (W - μ[W | m])²`,

so the improvement is strict unless `W = μ[W | m]` almost everywhere
(`integral_sq_sub_condExp_eq_iff`).

The statistical content needs sufficiency. Conditioning on an arbitrary `m` gives a function
that depends on the unknown parameter through `P θ`. When `m` is sufficient for the family
(`IsSufficient`), one parameter-free `m`-measurable function `η` is a version of every
`P_θ[W | m]` (`IsSufficient.exists_common_condExp`), so `η` is itself an estimator; it has the
same mean as `W` and no larger risk under every parameter (`IsSufficient.raoBlackwell`). For a
sufficient statistic `T`, the improved estimator is a measurable function of `T`
(`raoBlackwell_comap`).

## Main results

* `integrable_comp_condExp`, `integral_comp_condExp_le`: one-measure convex-loss form.
* `integral_sq_sub_eq_add`, `integral_sq_sub_condExp_eq_iff`: squared-error decomposition and
  its equality case.
* `IsSufficient.raoBlackwell`, `raoBlackwell_comap`: the Rao–Blackwell theorem.

## References

* C. R. Rao, *Information and the accuracy attainable in the estimation of statistical
  parameters*, Bull. Calcutta Math. Soc. 37 (1945), 81–91.
* D. Blackwell, *Conditional expectation and unbiased sequential estimation*, Ann. Math.
  Statist. 18 (1947), 105–110.
* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Section 7.3.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory

variable {Ω Θ : Type*}

/-- A convex function on `ℝ` is continuous. -/
private theorem continuous_of_convexOn_univ {L : ℝ → ℝ} (hL : ConvexOn ℝ Set.univ L) :
    Continuous L := by
  have h := hL.continuousOn_interior
  rw [interior_univ] at h
  exact continuousOn_univ.mp h

/-- A convex function on `ℝ` is bounded below by `L 0 - K |x|` for some `K`. -/
private theorem exists_sub_mul_abs_le_of_convexOn_univ {L : ℝ → ℝ}
    (hL : ConvexOn ℝ Set.univ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, L 0 - K * |x| ≤ L x := by
  set d₁ := L 0 - L (-1)
  set d₂ := L 1 - L 0
  refine ⟨|d₁| + |d₂|, by positivity, fun x => ?_⟩
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := hL.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ 1) hx one_pos
    simp only [zero_sub, sub_zero, div_one] at h
    rw [div_le_iff₀ (by linarith)] at h
    have h2 : d₂ * -x ≤ |d₂| * |x| := by
      rw [abs_of_neg hx]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    nlinarith [abs_nonneg d₁, abs_nonneg x]
  · simp
  · have h := hL.slope_mono_adjacent (Set.mem_univ (-1)) (Set.mem_univ x) (by norm_num) hx
    simp only [sub_neg_eq_add, zero_add, sub_zero, div_one] at h
    rw [le_div_iff₀ hx] at h
    have h2 : -(|d₁| * |x|) ≤ d₁ * x := by
      rw [abs_of_pos hx]
      nlinarith [neg_abs_le d₁]
    nlinarith [abs_nonneg d₂, abs_nonneg x]

/-- For a convex loss `L`, `L ∘ μ[W | m]` is integrable whenever `W` and `L ∘ W` are. -/
theorem integrable_comp_condExp {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    (μ : Measure[m₀] Ω) [IsProbabilityMeasure μ] {L : ℝ → ℝ} (hL : ConvexOn ℝ Set.univ L)
    {W : Ω → ℝ} (hW : Integrable W μ) (hLW : Integrable (fun ω => L (W ω)) μ) :
    Integrable (fun ω => L (μ[W | m] ω)) μ := by
  have hLc := continuous_of_convexOn_univ hL
  obtain ⟨K, hK0, hK⟩ := exists_sub_mul_abs_le_of_convexOn_univ hL
  have hJ : (fun ω => L (μ[W | m] ω)) ≤ᵐ[μ] μ[fun ω => L (W ω) | m] :=
    hL.map_condExp_le_univ hm hLc.lowerSemicontinuous hW hLW
  have hY : Integrable (μ[W | m]) μ := integrable_condExp
  have hU : Integrable (μ[fun ω => L (W ω) | m]) μ := integrable_condExp
  refine Integrable.mono' ((hU.abs.add (integrable_const |L 0|)).add (hY.abs.const_mul K))
    (hLc.comp_aestronglyMeasurable hY.aestronglyMeasurable) ?_
  filter_upwards [hJ] with ω hω
  have hlow := hK (μ[W | m] ω)
  have h1 := le_abs_self (μ[fun ω => L (W ω) | m] ω)
  have h2 := abs_nonneg (μ[fun ω => L (W ω) | m] ω)
  have h3 := neg_abs_le (L 0)
  have h4 := abs_nonneg (L 0)
  have h5 : 0 ≤ K * |μ[W | m] ω| := mul_nonneg hK0 (abs_nonneg _)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]
  constructor <;> linarith

/-- **Rao–Blackwell inequality for one law.** For a convex loss `L` and an integrable `W` with
integrable loss, `∫ L(μ[W | m]) dμ ≤ ∫ L(W) dμ`. -/
theorem integral_comp_condExp_le {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    (μ : Measure[m₀] Ω) [IsProbabilityMeasure μ] {L : ℝ → ℝ} (hL : ConvexOn ℝ Set.univ L)
    {W : Ω → ℝ} (hW : Integrable W μ) (hLW : Integrable (fun ω => L (W ω)) μ) :
    ∫ ω, L (μ[W | m] ω) ∂μ ≤ ∫ ω, L (W ω) ∂μ := by
  have hJ : (fun ω => L (μ[W | m] ω)) ≤ᵐ[μ] μ[fun ω => L (W ω) | m] :=
    hL.map_condExp_le_univ hm (continuous_of_convexOn_univ hL).lowerSemicontinuous hW hLW
  calc ∫ ω, L (μ[W | m] ω) ∂μ ≤ ∫ ω, (μ[fun ω => L (W ω) | m]) ω ∂μ :=
        integral_mono_ae (integrable_comp_condExp hm μ hL hW hLW) integrable_condExp hJ
    _ = ∫ ω, L (W ω) ∂μ := integral_condExp hm

/-- **Squared-error decomposition.** For `W` with a finite second moment and any target `c`,
`E (W - c)² = E (μ[W | m] - c)² + E (W - μ[W | m])²`. -/
theorem integral_sq_sub_eq_add {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    (μ : Measure[m₀] Ω) [IsProbabilityMeasure μ] {W : Ω → ℝ} (hW : MemLp W 2 μ) (c : ℝ) :
    ∫ ω, (W ω - c) ^ 2 ∂μ =
      ∫ ω, (μ[W | m] ω - c) ^ 2 ∂μ + ∫ ω, (W ω - μ[W | m] ω) ^ 2 ∂μ := by
  set Y := μ[W | m] with hY
  have hW1 : Integrable W μ := hW.integrable one_le_two
  have hY2 : MemLp Y 2 μ := hW.condExp (by norm_num)
  have hYc : MemLp (fun ω => Y ω - c) 2 μ := hY2.sub (memLp_const c)
  have hWY : MemLp (fun ω => W ω - Y ω) 2 μ := hW.sub hY2
  have hint1 : Integrable (fun ω => (Y ω - c) * W ω) μ := hYc.integrable_mul hW
  have hint2 : Integrable (fun ω => (Y ω - c) * Y ω) μ := hYc.integrable_mul hY2
  have hcross : ∫ ω, (Y ω - c) * (W ω - Y ω) ∂μ = 0 := by
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := m) (μ := μ)
      (f := fun ω => Y ω - c) (g := W)
      (stronglyMeasurable_condExp.sub stronglyMeasurable_const) hint1 hW1
    have h1 : ∫ ω, (Y ω - c) * W ω ∂μ = ∫ ω, (Y ω - c) * Y ω ∂μ := by
      rw [← integral_condExp hm (f := fun ω => (Y ω - c) * W ω)]
      exact integral_congr_ae hpull
    calc ∫ ω, (Y ω - c) * (W ω - Y ω) ∂μ
        = ∫ ω, ((Y ω - c) * W ω - (Y ω - c) * Y ω) ∂μ := by congr 1; ext ω; ring
      _ = 0 := by rw [integral_sub hint1 hint2, h1, sub_self]
  have hexp : (fun ω => (W ω - c) ^ 2) = fun ω =>
      ((Y ω - c) ^ 2 + (W ω - Y ω) ^ 2) + 2 * ((Y ω - c) * (W ω - Y ω)) := by
    ext ω; ring
  have hA : Integrable (fun ω => (Y ω - c) ^ 2) μ := hYc.integrable_sq
  have hB : Integrable (fun ω => (W ω - Y ω) ^ 2) μ := hWY.integrable_sq
  have hC : Integrable (fun ω => 2 * ((Y ω - c) * (W ω - Y ω))) μ :=
    (hYc.integrable_mul hWY).const_mul 2
  rw [hexp, integral_add (f := fun ω => (Y ω - c) ^ 2 + (W ω - Y ω) ^ 2) (hA.add hB) hC,
    integral_add hA hB, integral_const_mul, hcross,
    mul_zero, add_zero]

/-- **Equality case under squared error.** Conditioning leaves the squared-error risk at `c`
unchanged if and only if `W` already equals `μ[W | m]` almost everywhere. -/
theorem integral_sq_sub_condExp_eq_iff {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    (μ : Measure[m₀] Ω) [IsProbabilityMeasure μ] {W : Ω → ℝ} (hW : MemLp W 2 μ) (c : ℝ) :
    ∫ ω, (μ[W | m] ω - c) ^ 2 ∂μ = ∫ ω, (W ω - c) ^ 2 ∂μ ↔ W =ᵐ[μ] μ[W | m] := by
  have hWY : MemLp (fun ω => W ω - μ[W | m] ω) 2 μ := hW.sub (hW.condExp (by norm_num))
  rw [integral_sq_sub_eq_add hm μ hW c, left_eq_add,
    integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hWY.integrable_sq]
  constructor
  · intro h
    filter_upwards [h] with ω hω
    simpa [sub_eq_zero] using hω
  · intro h
    filter_upwards [h] with ω hω
    simp [hω]

/-- **The Rao–Blackwell theorem.** Let `m` be sufficient for the family of probability measures
`P`, and let `W` be a measurable estimator that is integrable under every `P θ`. There is one
parameter-free `m`-measurable estimator `η`, a version of `P_θ[W | m]` for every `θ`, with
the same mean as `W` under every `θ` and no larger risk under every loss `ℓ θ` that is convex
in the estimate (for which `ℓ θ ∘ W` is integrable).

Source: Rao (1945); Blackwell (1947); Casella–Berger, Section 7.3. -/
theorem IsSufficient.raoBlackwell {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)] (hP : IsSufficient m P)
    {W : Ω → ℝ} (hWm : Measurable[m₀] W) (hW : ∀ θ, Integrable W (P θ)) :
    ∃ η : Ω → ℝ, StronglyMeasurable[m] η ∧ (∀ θ, η =ᵐ[P θ] (P θ)[W | m]) ∧
      (∀ θ, ∫ ω, η ω ∂P θ = ∫ ω, W ω ∂P θ) ∧
      ∀ ℓ : Θ → ℝ → ℝ, ∀ θ, ConvexOn ℝ Set.univ (ℓ θ) →
        Integrable (fun ω => ℓ θ (W ω)) (P θ) →
        ∫ ω, ℓ θ (η ω) ∂P θ ≤ ∫ ω, ℓ θ (W ω) ∂P θ := by
  obtain ⟨η, hηm, hη⟩ := hP.exists_common_condExp hm hWm hW
  refine ⟨η, hηm, hη, fun θ => ?_, fun ℓ θ hℓ hℓW => ?_⟩
  · rw [integral_congr_ae (hη θ), integral_condExp hm]
  · calc ∫ ω, ℓ θ (η ω) ∂P θ = ∫ ω, ℓ θ ((P θ)[W | m] ω) ∂P θ :=
          integral_congr_ae ((hη θ).fun_comp (ℓ θ))
      _ ≤ ∫ ω, ℓ θ (W ω) ∂P θ := integral_comp_condExp_le hm (P θ) hℓ (hW θ) hℓW

/-- **The Rao–Blackwell theorem for a sufficient statistic.** If the statistic `T` is
sufficient for `P` and `W` is a measurable estimator with finite second moment under every
`P θ`, there is a measurable `φ` such that `φ ∘ T` is a version of every `E_θ[W | T]`, has the
same mean as `W`, and for every target `τ θ` satisfies
`E_θ (W - τ θ)² = E_θ (φ(T) - τ θ)² + E_θ (W - φ(T))²`. -/
theorem raoBlackwell_comap {τ : Type*} [MeasurableSpace τ] {m₀ : MeasurableSpace Ω}
    {T : Ω → τ} (hT : Measurable T) {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hP : IsSufficient (MeasurableSpace.comap T ‹MeasurableSpace τ›) P) {W : Ω → ℝ}
    (hWm : Measurable[m₀] W) (hW : ∀ θ, MemLp W 2 (P θ)) (tgt : Θ → ℝ) :
    ∃ φ : τ → ℝ, Measurable φ ∧
      (∀ θ, (fun ω => φ (T ω)) =ᵐ[P θ] (P θ)[W | MeasurableSpace.comap T ‹_›]) ∧
      (∀ θ, ∫ ω, φ (T ω) ∂P θ = ∫ ω, W ω ∂P θ) ∧
      ∀ θ, ∫ ω, (W ω - tgt θ) ^ 2 ∂P θ =
        ∫ ω, (φ (T ω) - tgt θ) ^ 2 ∂P θ + ∫ ω, (W ω - φ (T ω)) ^ 2 ∂P θ := by
  have hm := hT.comap_le
  obtain ⟨η, hηm, hη⟩ :=
    hP.exists_common_condExp hm hWm fun θ => (hW θ).integrable one_le_two
  obtain ⟨φ, hφ, rfl⟩ := hηm.exists_eq_measurable_comp
  refine ⟨φ, hφ.measurable, hη, fun θ => ?_, fun θ => ?_⟩
  · change ∫ ω, (φ ∘ T) ω ∂P θ = _
    rw [integral_congr_ae (hη θ), integral_condExp hm]
  · have h1 : (fun ω => (φ (T ω) - tgt θ) ^ 2) =ᵐ[P θ]
        fun ω => ((P θ)[W | MeasurableSpace.comap T ‹_›] ω - tgt θ) ^ 2 := by
      filter_upwards [hη θ] with ω hω
      simp only [Function.comp_apply] at hω
      rw [hω]
    have h2 : (fun ω => (W ω - φ (T ω)) ^ 2) =ᵐ[P θ]
        fun ω => (W ω - (P θ)[W | MeasurableSpace.comap T ‹_›] ω) ^ 2 := by
      filter_upwards [hη θ] with ω hω
      simp only [Function.comp_apply] at hω
      rw [hω]
    rw [integral_congr_ae h1, integral_congr_ae h2]
    exact integral_sq_sub_eq_add hm (P θ) (hW θ) (tgt θ)

end MathlibExt.Probability.Statistics.Sufficiency
