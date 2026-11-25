/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# The breeder's equation

In the linear parent–offspring model the offspring value `O` regresses linearly on the parental
(mid-parent) value `P`: `O = μ + h² (P - μ) + e` with `𝔼[e | P] = 0`, i.e.
`𝔼[O | P] = μ + h² (P - μ)`, where `μ` is the population mean and `h²` the (narrow-sense)
heritability, the slope of the regression. If parents are selected on their phenotype, i.e. the
selected group is an event determined by `P` (truncation selection `P ≥ t` is the classical
case), the selection differential is `S = 𝔼[P | selected] - μ` and the response to selection
is `R = 𝔼[O | selected] - μ`. The breeder's equation is the exact identity

  `R = h² S`.

`𝔼[· | selected]` is the expectation under the conditional measure `μ[|s]`. The population is
a probability measure and `mean` is the population mean of the parental value, `𝔼[P] = μ`
(`Model.integral_parent`), so selecting the whole population gives `S = 0` and `R = 0`
(`Model.selectionDifferential_univ`, `Model.response_univ`). The heritability of the biological
model lies in `[0, 1]`, but the identity `R = h² S` holds for every real slope `h²`. The
selected group must have positive mass: otherwise `μ[|s] = 0` and both expectations are the junk
value `0`.

## Main results

* `Model`: the linear parent–offspring model.
* `Model.response_eq`: the breeder's equation `R = h² S`.
* `Model.selectionDifferential_univ`, `Model.response_univ`: no selection, no differential and
  no response.

## References

* J. L. Lush, *Animal Breeding Plans*, Collegiate Press, Ames, Iowa, 1937.
* D. S. Falconer, T. F. C. Mackay, *Introduction to Quantitative Genetics*, 4th ed., Longman,
  1996, ch. 11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Biology.StatisticalGenetics.Breeder

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The linear parent–offspring model on a population described by a probability measure `μ`:
the parental (mid-parent) value `parent` and the offspring value `offspring` are integrable,
`mean` is the population mean of the parental value, and the offspring value regresses linearly
on the parental value, `𝔼[O | P] = mean + h2 * (P - mean)` (equivalently
`O = mean + h2 (P - mean) + e` with `𝔼[e | P] = 0`). Here `h2` is the heritability. -/
structure Model (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The population mean `μ` of the parental value. -/
  mean : ℝ
  /-- The heritability `h²`: the slope of the offspring-on-parent regression. -/
  h2 : ℝ
  /-- The parental (mid-parent) value `P`. -/
  parent : Ω → ℝ
  /-- The offspring value `O`. -/
  offspring : Ω → ℝ
  /-- The parental value is measurable. -/
  measurable_parent : Measurable parent
  /-- The parental value is integrable. -/
  integrable_parent : Integrable parent μ
  /-- The offspring value is integrable. -/
  integrable_offspring : Integrable offspring μ
  /-- `mean` is the population mean of the parental value: `𝔼[P] = μ`. -/
  integral_parent : ∫ ω, parent ω ∂μ = mean
  /-- Linear regression: `𝔼[O | P] = μ + h² (P - μ)`. -/
  condExp_offspring : μ[offspring | MeasurableSpace.comap parent inferInstance] =ᵐ[μ]
    fun ω => mean + h2 * (parent ω - mean)

namespace Model

variable {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model μ)

/-- The selection differential `S = 𝔼[P | selected] - μ` of the selected group `s`. -/
noncomputable def selectionDifferential (s : Set Ω) : ℝ := ∫ ω, M.parent ω ∂μ[|s] - M.mean

/-- The response to selection `R = 𝔼[O | selected] - μ`: the mean offspring value of the
selected parents, relative to the population mean. -/
noncomputable def response (s : Set Ω) : ℝ := ∫ ω, M.offspring ω ∂μ[|s] - M.mean

/-- The breeder's equation (Lush 1937): if the selected group `s` is determined by the parental
value (an event of `σ(P)`) and has positive mass, the response to selection is the heritability
times the selection differential, `R = h² S`. -/
theorem response_eq {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.comap M.parent inferInstance] s) (hs0 : μ s ≠ 0) :
    M.response s = M.h2 * M.selectionDifferential s := by
  have hm : MeasurableSpace.comap M.parent inferInstance ≤ m := M.measurable_parent.comap_le
  have hsm : MeasurableSet s := hm s hs
  have hO : ∫ ω in s, M.offspring ω ∂μ = ∫ ω in s, M.mean + M.h2 * (M.parent ω - M.mean) ∂μ := by
    rw [← setIntegral_condExp hm M.integrable_offspring hs]
    exact setIntegral_congr_ae hsm (M.condExp_offspring.mono fun ω h _ => h)
  have := cond_isProbabilityMeasure (μ := μ) hs0
  have hP : Integrable M.parent μ[|s] :=
    M.integrable_parent.restrict.smul_measure (ENNReal.inv_ne_top.2 hs0)
  have hOs : ∫ ω, M.offspring ω ∂μ[|s] = ∫ ω, M.mean + M.h2 * (M.parent ω - M.mean) ∂μ[|s] := by
    simp only [ProbabilityTheory.cond, integral_smul_measure, hO]
  unfold response selectionDifferential
  have hsub : Integrable (fun ω => M.parent ω - M.mean) μ[|s] := hP.sub (integrable_const _)
  rw [hOs, integral_add (integrable_const _) (hsub.const_mul M.h2), integral_const,
    integral_const_mul, integral_sub hP (integrable_const _), integral_const]
  simp

/-- Selecting the whole population gives no selection differential, `S = 0`. -/
theorem selectionDifferential_univ : M.selectionDifferential Set.univ = 0 := by
  rw [selectionDifferential, cond_univ, M.integral_parent, sub_self]

/-- Selecting the whole population gives no response, `R = 0`. -/
theorem response_univ : M.response Set.univ = 0 := by
  rw [M.response_eq MeasurableSet.univ (by simp), selectionDifferential_univ, mul_zero]

end Model

end MathlibExt.Biology.StatisticalGenetics.Breeder
