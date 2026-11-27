/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeZpowValuation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Binomial
import MathlibExt.NumberTheory.AlternatingChooseSums
import MathlibExt.NumberTheory.HigherOrderHarmonic
import MathlibExt.NumberTheory.WolstenholmeBinomialCongruence
import MathlibExt.NumberTheory.WolstenholmeBinomialExtension
import MathlibExt.NumberTheory.WolstenholmeCongruenceEquivalence

/-!
# Tests for the valuation bounds on Taylor remainders

Quadratic and cubic polynomials exercise the two nonzero-step bounds and the zero-step identity.
-/

namespace MathlibExtTest.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeZpowValuation

public section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def quadraticCoeffs (j : ℕ) : ℚ_[5] := if j = 2 then 5 / 2 else 0

private theorem quadratic_coeff_bound (j : ℕ) :
    ‖j.descFactorial 2 • quadraticCoeffs j‖ ≤ (5 : ℝ) ^ (-(1 : ℝ)) := by
  by_cases h : j = 2
  · subst j
    have hn : ‖(5 : ℚ_[5])‖ = (5 : ℝ)⁻¹ := Padic.norm_p
    norm_num [quadraticCoeffs, Nat.descFactorial, nsmul_eq_mul, hn,
      Real.rpow_neg, Real.rpow_one]
  · simp only [quadraticCoeffs, ite_eq_right h, smul_zero, norm_zero]
    positivity

private theorem quadratic_remainder (h : ℚ_[5]) :
    (∑ j ∈ Finset.range 3, (1 + h) ^ j • quadraticCoeffs j -
        ∑ q ∈ Finset.range 2, ∑ j ∈ Finset.range 3,
          ((j.choose q : ℚ_[5]) * 1 ^ (j - q) * h ^ q) • quadraticCoeffs j) =
      h ^ 2 * (5 / 2) := by
  norm_num [quadraticCoeffs, Finset.sum_range_succ, smul_eq_mul]
  ring

example :
    0 < ‖((5 : ℚ_[5]) ^ 2) ^ 2 * (5 / 2)‖ ∧
      ‖((5 : ℚ_[5]) ^ 2) ^ 2 * (5 / 2)‖ ≤ (5 : ℝ) ^ (-(5 : ℝ)) := by
  have result := (MetaMathlibExt.norm_sub_taylor_le_zpow_valuation
    3 2 quadraticCoeffs 1 ((5 : ℚ_[5]) ^ 2) 1 (by norm_num)
    (by norm_num) (by norm_num) (fun j _ => quadratic_coeff_bound j)).1 (by norm_num)
  have hvp : (5 : ℚ_[5]).valuation = 1 := Padic.valuation_p
  have hv : 1 / ((5 : ℝ) - 2) ≤ ((5 : ℚ_[5]) ^ 2).valuation := by
    rw [Padic.valuation_pow, hvp]
    norm_num
  constructor
  · apply norm_pos_iff.mpr
    norm_num
  · have bound := result hv
    rw [quadratic_remainder, Padic.valuation_pow, hvp] at bound
    convert bound using 1
    norm_num

private noncomputable def cubicCoeffs (j : ℕ) : ℚ_[3] := if j = 3 then 1 / 6 else 0

private theorem cubic_coeff_bound (j : ℕ) :
    ‖j.descFactorial 3 • cubicCoeffs j‖ ≤ (3 : ℝ) ^ (-(0 : ℝ)) := by
  by_cases h : j = 3
  · subst j
    norm_num [cubicCoeffs, Nat.descFactorial, nsmul_eq_mul]
  · simp [cubicCoeffs, h]

private theorem cubic_remainder (h : ℚ_[3]) :
    (∑ j ∈ Finset.range 4, (1 + h) ^ j • cubicCoeffs j -
        ∑ q ∈ Finset.range 3, ∑ j ∈ Finset.range 4,
          ((j.choose q : ℚ_[3]) * 1 ^ (j - q) * h ^ q) • cubicCoeffs j) = h ^ 3 / 6 := by
  norm_num [cubicCoeffs, Finset.sum_range_succ, smul_eq_mul]
  ring

example :
    0 < ‖((3 : ℚ_[3]) ^ 2) ^ 3 / 6‖ ∧
      ‖((3 : ℚ_[3]) ^ 2) ^ 3 / 6‖ ≤ (3 : ℝ) ^ (-(5 : ℝ)) := by
  have result := (MetaMathlibExt.norm_sub_taylor_le_zpow_valuation
    4 3 cubicCoeffs 1 ((3 : ℚ_[3]) ^ 2) 0 (by norm_num)
    (by norm_num) (by norm_num) (fun j _ => cubic_coeff_bound j)).2.1 rfl
  have hvp : (3 : ℚ_[3]).valuation = 1 := Padic.valuation_p
  have hv : 1 / (3 : ℝ) ≤ ((3 : ℚ_[3]) ^ 2).valuation := by
    rw [Padic.valuation_pow, hvp]
    norm_num
  constructor
  · apply norm_pos_iff.mpr
    norm_num
  · have bound := result hv
    rw [cubic_remainder, Padic.valuation_pow, hvp] at bound
    convert bound using 1
    norm_num

example :
    ∑ j ∈ Finset.range 4, (2 : ℚ_[3]) ^ j • cubicCoeffs j =
      ∑ q ∈ Finset.range 3, ∑ j ∈ Finset.range 4,
        ((j.choose q : ℚ_[3]) * 2 ^ (j - q) * 0 ^ q) • cubicCoeffs j := by
  have ht : ‖(2 : ℚ_[3])‖ ≤ 1 := Padic.norm_int_le_one 2
  have hz := (MetaMathlibExt.norm_sub_taylor_le_zpow_valuation
    4 3 cubicCoeffs 2 0 0 ht (by norm_num) (by norm_num) (fun j _ => cubic_coeff_bound j)).2.2 rfl
  exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa only [add_zero] using hz))

end

end MathlibExtTest.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeZpowValuation
