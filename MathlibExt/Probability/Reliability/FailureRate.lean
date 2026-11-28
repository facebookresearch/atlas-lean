/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.MeasureTheory.Measure.Real

/-!
# Increasing failure rate implies new better than used

For a strictly positive lifetime, compare its residual survival at age `s` with residual
survival at age zero. If the lifetime cannot survive to age `s`, then it cannot survive past
`s + t` either. This formulation does not require a density or a hazard function.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- **Increasing failure rate implies new better than used.** For a measurable lifetime `L`
that is strictly positive almost surely under a probability measure `μ`, write `S(t) = P(L > t)`.
Assume that for each `u ≥ 0`, the residual survival `S(s + u) / S(s)` is nonincreasing in
`s` among nonnegative ages with `S(s) > 0`. Then `S(s + t) ≤ S(s) * S(t)` for all `s, t ≥ 0`.
The conclusion includes ages with zero survival, where the residual ratio need not be defined. -/
theorem increasingFailureRate_implies_newBetterThanUsed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : Ω → ℝ) (hL : Measurable L)
    (hpositive : ∀ᵐ ω ∂μ, 0 < L ω) :
    let S := fun t : ℝ => μ.real {ω | t < L ω}
    (∀ u ≥ 0, AntitoneOn (fun s => S (s + u) / S s) {s | 0 ≤ s ∧ 0 < S s}) →
      ∀ s ≥ 0, ∀ t ≥ 0, S (s + t) ≤ S s * S t := by
  intro S hIFR s hs t ht
  have hS₀ : S 0 = 1 := by
    have hmass : μ {ω | 0 < L ω} = 1 :=
      (mem_ae_iff_prob_eq_one (hL measurableSet_Ioi)).mp hpositive
    change (μ {ω | 0 < L ω}).toReal = 1
    rw [hmass, ENNReal.toReal_one]
  by_cases hₛ : S s = 0
  · have hmono : S (s + t) ≤ S s :=
      measureReal_mono fun _ hω => lt_of_le_of_lt (le_add_of_nonneg_right ht) hω
    simpa only [hₛ, zero_mul] using hmono
  · have hpos : 0 < S s := lt_of_le_of_ne measureReal_nonneg (Ne.symm hₛ)
    have hzero : (0 : ℝ) ∈ {r | 0 ≤ r ∧ 0 < S r} := ⟨le_rfl, by rw [hS₀]; exact zero_lt_one⟩
    have h : S (s + t) / S s ≤ S (0 + t) / S 0 := hIFR t ht hzero ⟨hs, hpos⟩ hs
    rw [zero_add, hS₀, div_one] at h
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp h

end ProbabilityTheory
