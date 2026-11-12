/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import MathlibExt.Probability.Statistics.EstimationRisk

/-!
# Complete statistics and Lehmann–Scheffé uniqueness

`IsCompleteStatistic P S`, for a family `P` of probability measures: the statistic `S` is
measurable, and every measurable `a` with `a ∘ S` integrable and of zero mean under every law
`P θ` vanishes `P θ`-almost everywhere for every `θ`. Two integrable functions of a complete
statistic with equal means under every law agree almost everywhere under every law; in
particular two unbiased estimators (`EstimationRisk.IsUnbiased`) of the same parameter function
that are functions of `S` agree almost everywhere under every law.

The minimum-variance (UMVU) conclusion and Basu's theorem are not part of this file.

Sources: E. L. Lehmann and H. Scheffé, Sankhyā 10 (1950), 305–340; Casella–Berger,
*Statistical Inference*, 2nd ed., Definition 6.2.21 and Theorem 7.3.23.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory

/-- A statistic `S : Ω → τ` is *complete* for the family of probability laws `P` if `S` is
measurable and every measurable `a : τ → ℝ` such that `a ∘ S` is integrable under every `P θ`
and has zero mean under every `P θ` vanishes `P θ`-almost everywhere (as a function of `ω`,
through `S`) for every `θ`. Completeness is not identifiability: the hypothesis and the
conclusion both range over all parameters.

Source: E. L. Lehmann and H. Scheffé, *Completeness, similar regions, and unbiased
estimation. Part I*, Sankhyā 10 (1950), 305–340; Casella–Berger, *Statistical Inference*,
2nd ed., Definition 6.2.21. -/
def IsCompleteStatistic {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    (P : Θ → ProbabilityMeasure Ω) (S : Ω → τ) : Prop :=
  Measurable S ∧
    ∀ a : τ → ℝ, Measurable a →
      (∀ θ, Integrable (fun ω => a (S ω)) ((P θ) : Measure Ω)) →
      (∀ θ, ∫ ω, a (S ω) ∂((P θ) : Measure Ω) = 0) →
      ∀ θ, (fun ω => a (S ω)) =ᵐ[((P θ) : Measure Ω)] 0

/-- **Lehmann–Scheffé uniqueness.** If `S` is complete for `P`, two measurable functions of
`S` that are integrable and have the same mean under every `P θ` agree `P θ`-almost
everywhere for every `θ`.

Source: Lehmann–Scheffé (1950); Casella–Berger, 2nd ed., proof of Theorem 7.3.23. -/
theorem IsCompleteStatistic.ae_eq_of_integral_eq {Ω Θ τ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace τ] {P : Θ → ProbabilityMeasure Ω} {S : Ω → τ}
    (hS : IsCompleteStatistic P S) {g h : τ → ℝ} (hg : Measurable g) (hh : Measurable h)
    (hgi : ∀ θ, Integrable (fun ω => g (S ω)) ((P θ) : Measure Ω))
    (hhi : ∀ θ, Integrable (fun ω => h (S ω)) ((P θ) : Measure Ω))
    (hgh : ∀ θ, ∫ ω, g (S ω) ∂((P θ) : Measure Ω) = ∫ ω, h (S ω) ∂((P θ) : Measure Ω)) :
    ∀ θ, (fun ω => g (S ω)) =ᵐ[((P θ) : Measure Ω)] fun ω => h (S ω) := by
  intro θ
  have hzero := hS.2 (fun t => g t - h t) (hg.sub hh) (fun θ => (hgi θ).sub (hhi θ))
    (fun θ => by rw [integral_sub (hgi θ) (hhi θ), hgh θ, sub_self]) θ
  filter_upwards [hzero] with ω hω
  simpa [sub_eq_zero] using hω

/-- **Unbiased functions of a complete statistic are unique.** If `S` is complete for `P` and
`g ∘ S`, `h ∘ S` are both unbiased estimators (`EstimationRisk.IsUnbiased`) of the same
`tgt : Θ → ℝ`, they agree `P θ`-almost everywhere for every `θ`. -/
theorem IsCompleteStatistic.ae_eq_of_unbiased {Ω Θ τ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace τ] {P : Θ → ProbabilityMeasure Ω} {S : Ω → τ}
    (hS : IsCompleteStatistic P S) (tgt : Θ → ℝ) {g h : τ → ℝ} (hg : Measurable g)
    (hh : Measurable h)
    (hg_unbiased : EstimationRisk.IsUnbiased (fun ω => g (S ω)) P tgt)
    (hh_unbiased : EstimationRisk.IsUnbiased (fun ω => h (S ω)) P tgt) :
    ∀ θ, (fun ω => g (S ω)) =ᵐ[((P θ) : Measure Ω)] fun ω => h (S ω) :=
  hS.ae_eq_of_integral_eq hg hh hg_unbiased.integrable hh_unbiased.integrable fun θ =>
    (hg_unbiased.expect_eq θ).trans (hh_unbiased.expect_eq θ).symm

end MathlibExt.Probability.Statistics.Sufficiency
