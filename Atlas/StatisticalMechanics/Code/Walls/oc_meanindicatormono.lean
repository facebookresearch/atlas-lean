/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Inequalities.OSSS

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.Walls







section MeasureForm

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)










theorem oc_mean_indicator_mono {s t : Set α} (h : s ⊆ t) :
    ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
      ≤ ∫⁻ x, t.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
  lintegral_mono (Set.indicator_le_indicator_of_subset h (fun _ => zero_le'))





theorem oc_mean_indicator_mono_pred {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∫⁻ x, {x | P x}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ
      ≤ ∫⁻ x, {x | Q x}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
  oc_mean_indicator_mono μ (fun x hx => h x hx)





theorem oc_indicator_mean_eq_measure {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ = μ s := by
  rw [lintegral_indicator_const hs]; simp






theorem oc_measure_mono_of_imp {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    μ {x | P x} ≤ μ {x | Q x} :=
  measure_mono (fun x hx => h x hx)

end MeasureForm










section ExpectForm

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]






theorem oc_expect_indicator_mono (ν : E → Bool → ℝ) (hν : IsProbWeight ν)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ ω, P ω → Q ω) :
    expect ν (fun ω => if P ω then (1 : ℝ) else 0)
      ≤ expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
  apply expect_mono hν
  intro ω
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq]






theorem oc_expect_indicator_mono_set (ν : E → Bool → ℝ) (hν : IsProbWeight ν)
    {A B : Set (ConfigSpace E)} (hAB : A ⊆ B) :
    expect ν (A.indicator (fun _ => (1 : ℝ))) ≤ expect ν (B.indicator (fun _ => (1 : ℝ))) := by
  apply expect_mono hν
  intro ω
  exact Set.indicator_le_indicator_of_subset hAB (fun _ => zero_le_one) ω

end ExpectForm

end StatMech.Walls
