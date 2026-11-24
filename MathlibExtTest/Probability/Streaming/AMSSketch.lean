/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.AMSSketch
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Streaming.AMS

namespace MathlibExtTest.Probability.Streaming.AMS

/-! ## A non-degenerate instance: four fully independent fair signs

The hypotheses of `integral_sketch_sq` are jointly satisfiable with more than four indices:
independent fair coins on `Fin 5 → Bool`, mapped to `±1`. -/

-- A fair coin on `Bool`.
noncomputable abbrev coin : Measure Bool :=
  (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure coin := by
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [ENNReal.add_halves]

-- Five independent fair coins.
noncomputable abbrev coins : Measure (Fin 5 → Bool) := Measure.pi fun _ => coin

-- The sign of a coin.
def sgn (b : Bool) : ℝ := if b then 1 else -1

-- The sign family read off the coordinates.
def signs (i : Fin 5) (ω : Fin 5 → Bool) : ℝ := sgn (ω i)

theorem signs_measurable (i : Fin 5) : Measurable (signs i) :=
  (measurable_of_finite sgn).comp (measurable_pi_apply i)

theorem signs_sign (i : Fin 5) (ω : Fin 5 → Bool) : signs i ω = 1 ∨ signs i ω = -1 := by
  unfold signs sgn; split_ifs <;> simp

theorem signs_mean (i : Fin 5) : coins[signs i] = 0 := by
  have : ∫ ω, signs i ω ∂coins = ∫ b, sgn b ∂coin :=
    integral_comp_eval (μ := fun _ => coin) (measurable_of_finite sgn).aestronglyMeasurable
  rw [this, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [sgn]
  · exact Integrable.smul_measure Integrable.of_finite (by simp)
  · exact Integrable.smul_measure Integrable.of_finite (by simp)

theorem signs_fourWise : FourWiseIndependent signs coins := by
  intro S _
  have h : iIndepFun (fun i ω => sgn (ω i)) coins :=
    iIndepFun_pi (μ := fun _ => coin) fun _ => (measurable_of_finite sgn).aemeasurable
  exact h.precomp Subtype.val_injective

-- The stream `0, 1, 1` has frequencies `1, 2, 0, 0, 0` and `F₂ = 1 + 4 = 5`.
example : secondMoment ([0, 1, 1] : List (Fin 5)) = 5 := by
  simp [secondMoment, freq, Fin.sum_univ_five, List.count_cons]
  norm_num

-- Unbiasedness on that instance.
example : ∫ ω, sketch signs ([0, 1, 1] : List (Fin 5)) ω ^ 2 ∂coins = 5 := by
  rw [integral_sketch_sq signs_measurable signs_sign signs_mean signs_fourWise]
  simp [secondMoment, freq, Fin.sum_univ_five, List.count_cons]
  norm_num

-- The variance bound `Var(Z²) ≤ 2 F₂² = 50` on that instance.
example : variance (fun ω => sketch signs ([0, 1, 1] : List (Fin 5)) ω ^ 2) coins ≤ 50 := by
  have h := variance_sketch_sq_le signs_measurable signs_sign signs_mean signs_fourWise
    ([0, 1, 1] : List (Fin 5))
  have h5 : secondMoment ([0, 1, 1] : List (Fin 5)) = 5 := by
    simp [secondMoment, freq, Fin.sum_univ_five, List.count_cons]
    norm_num
  rw [h5] at h
  linarith

-- The one-pass sketch is the frequency-weighted sum of signs.
example (ε : Fin 3 → Unit → ℝ) :
    sketch ε ([0, 2, 2] : List (Fin 3)) () = ε 0 () + 2 * ε 2 () := by
  rw [sketch_eq_sum_count_mul]
  simp [freq, Fin.sum_univ_three, List.count_cons]
  norm_num

end MathlibExtTest.Probability.Streaming.AMS
