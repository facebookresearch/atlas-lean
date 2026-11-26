/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedHarmonicGamma
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory MetaMathlibExt

/-! ## The generalized harmonic numbers -/

-- The first generalized harmonic number is `1` for every order.
example (s : ℝ) : generalizedHarmonic s 1 = 1 := by
  simp [generalizedHarmonic]

-- Order two: `H_2^{(2)} = 1 + 1 / 4`.
example : generalizedHarmonic 2 2 = 5 / 4 := by
  rw [generalizedHarmonic_succ, generalizedHarmonic_succ, generalizedHarmonic_zero]
  norm_num

-- Order zero counts the terms: `H_n^{(0)} = n`.
example (n : ℕ) : generalizedHarmonic 0 n = n := by
  simp [generalizedHarmonic]

-- Order one gives Mathlib's harmonic numbers: `H_n^{(1)} = H_n`.
example (n : ℕ) : generalizedHarmonic 1 n = harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [generalizedHarmonic_succ, ih, harmonic_succ, Real.rpow_one]
    push_cast
    rfl

/-! ## The Gamma representation -/

-- Subtracting the cases `n = 1` and `n = 2` of the first identity recovers the Laplace
-- transform `𝔼[exp (-X_s)] = 1 / 2 ^ s` of the Gamma distribution of shape `s` and rate `1`.
example (s : ℝ) (hs : 0 < s) :
    ∫ x, Real.exp (-((1 : ℕ) * x)) ∂gammaMeasure s 1 = ((2 : ℝ) ^ s)⁻¹ := by
  have h₂ := (generalizedHarmonic_eq_gamma_expectation s hs 2).1
  have h₁ := (generalizedHarmonic_eq_gamma_expectation s hs 1).1
  rw [Finset.sum_range_succ, ← h₁, generalizedHarmonic_succ] at h₂
  norm_num at h₂ ⊢
  linarith

-- At `n = 0` the integrand of the second identity vanishes, matching `H_0^{(s)} = 0`.
example (s : ℝ) (hs : 0 < s) :
    ∫ x, (1 - Real.exp (-((0 : ℕ) * x))) / (1 - Real.exp (-x)) ∂gammaMeasure s 1 = 0 := by
  rw [← (generalizedHarmonic_eq_gamma_expectation s hs 0).2, generalizedHarmonic_zero]

-- At `n = 2` the second identity reads `𝔼[(1 - exp (-2 X_s)) / (1 - exp (-X_s))] = 1 + 1 / 2 ^ s`.
example (s : ℝ) (hs : 0 < s) :
    ∫ x, (1 - Real.exp (-((2 : ℕ) * x))) / (1 - Real.exp (-x)) ∂gammaMeasure s 1 =
      1 + ((2 : ℝ) ^ s)⁻¹ := by
  rw [← (generalizedHarmonic_eq_gamma_expectation s hs 2).2, generalizedHarmonic_succ,
    generalizedHarmonic_succ, generalizedHarmonic_zero]
  norm_num

-- For shape `1`, the Gamma distribution is the exponential distribution of rate `1`, and the
-- representation gives the classical identity `H_n = 𝔼[(1 - exp (-n X)) / (1 - exp (-X))]`.
example (n : ℕ) :
    ∫ x, (1 - Real.exp (-(n * x))) / (1 - Real.exp (-x)) ∂expMeasure 1 = harmonic n := by
  have h (m : ℕ) : generalizedHarmonic 1 m = harmonic m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [generalizedHarmonic_succ, ih, harmonic_succ, Real.rpow_one]
      push_cast
      rfl
  rw [← h, (generalizedHarmonic_eq_gamma_expectation 1 one_pos n).2]
  rfl

-- A shift equal to the shape gives order zero, so the weighted sum counts its terms.
example (s : ℝ) (hs : 0 < s) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ s *
      ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 = n := by
  rw [← generalizedHarmonic_sub_eq_gamma_expectation s hs s n]
  simp [generalizedHarmonic]

-- At shape one and degree two, the linear and quadratic Stirling terms have opposite signs.
-- Only the last binomial coefficient survives, giving the Laplace transform at one.
example : ∫ x, Real.exp (-x) ∂gammaMeasure 1 1 = 1 / 2 := by
  have h := stirlingFirst_generalizedHarmonic_eq_gamma_expectation 1 1 one_pos 2
  norm_num [Finset.sum_range_succ, Nat.stirlingFirst, Nat.factorial, Nat.choose,
    generalizedHarmonic_succ, Real.rpow_neg_one] at h
  linarith

/-! ## Binomially weighted sums -/

-- With constant binomial weight, the correction is a single harmonic number of order α - 1.
example (α : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Ico 1 n, generalizedHarmonic α j =
      n * generalizedHarmonic α n - generalizedHarmonic (α - 1) n := by
  simpa [Finset.sum_range_succ, Nat.stirlingFirst] using
    sum_choose_mul_generalizedHarmonic 0 n α

-- When the weight is j, the two shifted orders occur with opposite signs.
example (α : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Ico 1 n, (j : ℝ) * generalizedHarmonic α j =
      (n.choose 2 : ℝ) * generalizedHarmonic α n -
        (generalizedHarmonic (α - 2) n - generalizedHarmonic (α - 1) n) / 2 := by
  have h := sum_choose_mul_generalizedHarmonic 1 n α
  norm_num [Finset.sum_range_succ, Nat.stirlingFirst, Nat.factorial] at h
  rw [h]
  ring
