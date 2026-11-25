/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.ConditionalExpectation.FiniteValued

/-!
# Tests for the conditional expectation of a function of a finite-valued random variable

* With constant coefficients: `E[Y | m] = ∑ₐ a · P(Y = a | m)` for a random variable with values
  in `Fin 3`.
* With the trivial σ-algebra: the law of total expectation `E[c Y] = ∑ₐ c a · P(Y = a)`.
-/

namespace MathlibExtTest.FiniteValued

open MeasureTheory

/-- The conditional expectation of a random variable with values in `{0, 1, 2}`. -/
example {Ω : Type*} {m mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {Y : Ω → Fin 3} (hY : ∀ a, MeasurableSet {ω | Y ω = a}) :
    μ[fun ω => ((Y ω : ℕ) : ℝ) | m] =ᵐ[μ]
      fun ω => ∑ a : Fin 3, ((a : ℕ) : ℝ) * μ[{ω | Y ω = a}.indicator (fun _ => (1 : ℝ)) | m] ω :=
  condExp_comp_eq_sum hm hY (g := fun a _ => ((a : ℕ) : ℝ)) (K := 2)
    (fun _ => stronglyMeasurable_const) (fun a _ => by
      have := a.2
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.lt_succ_iff.1 this)

/-- With the trivial σ-algebra the theorem is the law of total expectation. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → Fin 3}
    (hY : ∀ a, MeasurableSet {ω | Y ω = a}) (c : Fin 3 → ℝ) :
    ∫ ω, c (Y ω) ∂μ = ∑ a, c a * μ.real {ω | Y ω = a} := by
  have h := condExp_comp_eq_sum (μ := μ) (m := ⊥) bot_le hY (g := fun a _ => c a)
    (K := ∑ a, |c a|) (fun _ => stronglyMeasurable_const)
    (fun a _ => Finset.single_le_sum (f := fun a => |c a|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a))
  obtain ⟨ω, hω⟩ := h.exists
  simpa [condExp_bot, integral_indicator_const _ (hY _)] using hω

end MathlibExtTest.FiniteValued
