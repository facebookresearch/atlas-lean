/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Complete

/-!
# Tests for complete statistics
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.Complete

open MeasureTheory MathlibExt.Probability.Statistics.Sufficiency
open scoped ENNReal

/-- Bernoulli measure on `Bool` with success probability `1/3` (`θ = false`) or `2/3`
(`θ = true`). -/
private noncomputable def bernMeas (θ : Bool) : Measure Bool :=
  (if θ then (1 / 3 : ℝ≥0∞) else 2 / 3) • Measure.dirac false +
    (if θ then (2 / 3 : ℝ≥0∞) else 1 / 3) • Measure.dirac true

private instance isProbabilityMeasure_bernMeas (θ : Bool) : IsProbabilityMeasure (bernMeas θ) :=
  ⟨by
    cases θ <;> simp only [bernMeas, Bool.false_eq_true, ite_true, ite_false,
      Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] <;>
    rw [ENNReal.div_add_div_same] <;> norm_num [ENNReal.div_self]⟩

/-- The Bernoulli family as probability measures. -/
private noncomputable def bernFam (θ : Bool) : ProbabilityMeasure Bool :=
  ⟨bernMeas θ, inferInstance⟩

private theorem integral_bernFam (θ : Bool) (a : Bool → ℝ) :
    ∫ ω, a ω ∂((bernFam θ) : Measure Bool) =
      (if θ then 1 / 3 else 2 / 3) * a false + (if θ then 2 / 3 else 1 / 3) * a true := by
  have hint : Integrable a (bernMeas θ) := Integrable.of_finite
  change ∫ ω, a ω ∂bernMeas θ = _
  unfold bernMeas at hint ⊢
  rw [integral_add_measure (integrable_add_measure.mp hint).1 (integrable_add_measure.mp hint).2,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  cases θ <;> simp

private theorem ae_bernFam_iff (θ : Bool) (p : Bool → Prop) :
    (∀ᵐ ω ∂((bernFam θ) : Measure Bool), p ω) ↔ p false ∧ p true := by
  change (∀ᵐ ω ∂bernMeas θ, p ω) ↔ _
  cases θ <;> simp [bernMeas]

private theorem bernFam_isComplete : IsCompleteStatistic bernFam (id : Bool → Bool) := by
  refine ⟨measurable_id, fun a _ _ hmean θ => ?_⟩
  have h0 := hmean false
  have h1 := hmean true
  norm_num [integral_bernFam] at h0 h1
  have hf : a false = 0 := by linarith
  have ht : a true = 0 := by linarith
  exact (ae_bernFam_iff θ _).2 ⟨hf, ht⟩

/-- Non-vacuity: the identity statistic is complete for the two-point Bernoulli family
(zero mean at two distinct success probabilities forces `a = 0`). -/
example : IsCompleteStatistic bernFam (id : Bool → Bool) := by
  exact bernFam_isComplete

/-- Non-vacuity: a point mass makes the identity statistic complete. -/
example : IsCompleteStatistic
    (fun _ : Unit => (⟨Measure.dirac true, inferInstance⟩ : ProbabilityMeasure Bool))
    (id : Bool → Bool) := by
  refine ⟨measurable_id, fun a _ _ hmean θ => ?_⟩
  have h := hmean ()
  simp only [ProbabilityMeasure.coe_mk, id_eq, integral_dirac] at h
  simp [Filter.EventuallyEq, h]

/-- The quantifier over laws matters: a single Bernoulli(1/3) law is not complete
(`a true = 2`, `a false = -1` has mean zero and is nowhere zero). -/
example : ¬ IsCompleteStatistic (fun _ : Unit => bernFam false) (id : Bool → Bool) := by
  intro hS
  have h := hS.2 (fun b => if b then 2 else -1) Measurable.of_discrete
    (fun _ => Integrable.of_finite) (fun _ => by norm_num [integral_bernFam]) ()
  have := ((ae_bernFam_iff false _).1 h).1
  norm_num at this

/-- Without completeness, uniqueness fails: two measurable functions with the same mean under
the only law that are not almost everywhere equal. -/
example : ∃ g h : Bool → ℝ, Measurable g ∧ Measurable h ∧
    (∫ ω, g (id ω) ∂((bernFam false) : Measure Bool) =
      ∫ ω, h (id ω) ∂((bernFam false) : Measure Bool)) ∧
    ¬ ((fun ω => g (id ω)) =ᵐ[((bernFam false) : Measure Bool)] fun ω => h (id ω)) := by
  refine ⟨fun b => if b then 2 else -1, fun _ => 0, Measurable.of_discrete,
    Measurable.of_discrete, by norm_num [integral_bernFam], fun hae => ?_⟩
  have := ((ae_bernFam_iff false _).1 hae).1
  norm_num at this

/-- The uniqueness theorem applied to the complete Bernoulli family. -/
example {g h : Bool → ℝ}
    (hgh : ∀ θ, ∫ ω, g ω ∂((bernFam θ) : Measure Bool) = ∫ ω, h ω ∂((bernFam θ) : Measure Bool)) :
    ∀ θ, g =ᵐ[((bernFam θ) : Measure Bool)] h := by
  exact bernFam_isComplete.ae_eq_of_integral_eq (g := g) (h := h) Measurable.of_discrete
    Measurable.of_discrete (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite) hgh

end MathlibExtTest.Probability.Statistics.Sufficiency.Complete

#print axioms MathlibExt.Probability.Statistics.Sufficiency.IsCompleteStatistic.ae_eq_of_integral_eq
#print axioms MathlibExt.Probability.Statistics.Sufficiency.IsCompleteStatistic.ae_eq_of_unbiased
