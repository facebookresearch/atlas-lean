/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Transport.SerialTransitLaw
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests of the normalized serial transit-time law

The production index counts stages after the first. The CDF fixture uses the finite Erlang
tail, independently of the lower incomplete gamma integral used in the CDF theorem.
-/

open Chemistry.Transport MeasureTheory ProbabilityTheory Set

/-- One stage is exponential with reciprocal-mean rate, for any positive mean. -/
example {τ : ℝ} (hτ : 0 < τ) : serialTransitLaw 0 τ = expMeasure τ⁻¹ ∧
    cdf (serialTransitLaw 0 τ) τ = 1 - Real.exp (-1) := by
  have h : serialTransitLaw 0 τ = expMeasure τ⁻¹ := by
    simpa [expMeasure, one_div] using serialTransitLaw_eq_gamma 0 τ
  refine ⟨h, ?_⟩
  rw [h, cdf_expMeasure_eq (inv_pos.mpr hτ)]
  simp [hτ.le, hτ.ne']

/-- The density representative includes zero, unlike the CDF which has no atom there. -/
example : serialTransitDensity 0 2 0 = 1 / 2 ∧ serialTransitDensity 1 2 0 = 0 ∧
    serialTransitDensity 0 2 (-1) = 0 ∧ cdf (serialTransitLaw 0 2) 0 = 0 := by
  rw [serialTransitLaw_cdf 0 (by norm_num) le_rfl]
  norm_num [serialTransitDensity]

/-- At two stages and mean two the CDF at one is `1 - 2 / exp 1`, not the survival probability. -/
example : cdf (serialTransitLaw 1 2) 1 = 1 - 2 / Real.exp 1 := by
  have h : serialTransitLaw 1 2 = gammaMeasure 2 1 := by
    norm_num [serialTransitLaw_eq_gamma]
  let : IsProbabilityMeasure (gammaMeasure 2 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) one_pos
  rw [h, cdf_eq_real, ← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi]
  have tail := gammaMeasure_real_Ioi_natCast_add_one 1 (r := 1) (c := 1) one_pos zero_le_one
  norm_num [Finset.sum_range_succ, Real.exp_neg] at tail
  rw [tail]
  ring

/-- One hundred stages, mean one and tolerance one half give an upper bound of one twenty-fifth. -/
example : (serialTransitLaw 99 1).real (Ioo (1 / 2) (3 / 2))ᶜ ≤ 1 / 25 := by
  convert serialTransitLaw_outside_le 99 (τ := 1) (ε := 1 / 2) one_pos (by norm_num) using 1 <;>
    norm_num

/-- Even when the variance ratio exceeds one, the tail bound for one stage stays at one. -/
example : (serialTransitLaw 0 2).real (Ioo (3 / 2) (5 / 2))ᶜ ≤ 1 := by
  convert serialTransitLaw_outside_le 0 (τ := 2) (ε := 1 / 2) (by norm_num) (by norm_num)
    using 1 <;> norm_num

/-- Tripling the time unit does not change the probability for the corresponding interval. -/
example : (serialTransitLaw 99 3).real (Ioo (3 / 2) (9 / 2))ᶜ =
    (serialTransitLaw 99 1).real (Ioo (1 / 2) (3 / 2))ᶜ := by
  convert (serialTransitLaw_changeUnit 99 (τ := 1) (ε := 1 / 2) (c := 3)
    one_pos (by norm_num) (by norm_num)).2.1 using 1 <;> norm_num

/-- For a non-unit rate the variance scales quadratically, not linearly. -/
example : (∫ t, t ∂serialTransitLaw 1 6) = 6 ∧ variance id (serialTransitLaw 1 6) = 18 := by
  have h := serialTransitLaw_moments 1 (τ := 6) (by norm_num)
  norm_num at h
  exact h

/-- At one stage, mean two and initial amount three, it is the normalized output `u(t)/6`,
not the unnormalized profile `u(t)`, that agrees with the density for nonnegative time. -/
example (u : Fin 1 → ℝ → ℝ) (h₀ : u 0 0 = 3)
    (hd : ∀ t, 0 ≤ t → HasDerivAt (u 0) (-(1 / 2) * u 0 t) t) {t : ℝ} (ht : 0 ≤ t) :
    serialTransitDensity 0 2 t = u 0 t / 6 := by
  have h := serialTransitDensity_eq_output 0 (τ := 2) (m := 3) (by norm_num) (by norm_num) u h₀
    (fun j ↦ j.elim0) (by simpa using hd) (fun j ↦ j.elim0) t
  rw [ite_eq_left ht] at h
  rw [h, (show Fin.last 0 = (0 : Fin 1) by decide), Nat.cast_zero]
  ring
