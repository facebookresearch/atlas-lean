/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DiscreteMechanisms
import Mathlib.Tactic.NormNum

/-!
# Tests for discrete differential-privacy mechanisms

Numeric instances: randomized response at `p = 3 / 4`, a two-output
exponential mechanism, geometric mass ratios and the normalizing
coefficient at `α = 1 / 2`, and a nonuniform fixed-distribution example.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.DiscreteMechanismsTests

open CSLibExt.Privacy.DifferentialPrivacy
open CSLibExt.Privacy.DiscreteMechanisms
open scoped ENNReal

/-! ## M1 test: randomized response at `p = 3 / 4` -/

/-- Randomized response with `p = 3 / 4` is `log 3`-DP. -/
theorem rr_three_quarters :
    IsDP (rrMech (3 / 4) (by norm_num) (by norm_num)) rrAdj (Real.log 3) := by
  have h3 : (3 / 4 : ℝ) / (1 - 3 / 4) = 3 := by norm_num
  have h := isDP_rrMech (3 / 4) (by norm_num) (by norm_num)
  rw [h3] at h
  exact h

/-! ## M2 test: two-output exponential mechanism -/

/-- Two-output utility depending on the input bit. -/
noncomputable def testUtil (d r : Bool) : ℝ :=
  if r then (if d then 1 else 0) else 0

theorem testUtil_sens :
    ∀ d d', rrAdj d d' → ∀ r, |testUtil d r - testUtil d' r| ≤ 1 := by
  intro d d' hadj r
  simp only [rrAdj] at hadj
  cases d <;> cases d' <;> cases r <;> simp_all [testUtil]

/-- The two-output instance is `2`-DP. -/
theorem exp_two_output : IsDP (expMech testUtil 2 1) rrAdj 2 :=
  isDP_expMech testUtil 2 1 (by norm_num) (by norm_num) rrAdj testUtil_sens

/-- Numeric mass of the two-output instance. -/
theorem exp_two_output_mass :
    expMech testUtil 2 1 true true
      = ENNReal.ofReal (Real.exp 1)
        / (1 + ENNReal.ofReal (Real.exp 1)) := by
  have e1 : testUtil true true = 1 := by simp [testUtil]
  have e0 : testUtil true false = 0 := by simp [testUtil]
  have s1 : (2 : ℝ) * 1 / (2 * 1) = 1 := by norm_num
  have s0 : (2 : ℝ) * 0 / (2 * 1) = 0 := by norm_num
  have hw1 : expWeight 2 1 (testUtil true true)
      = ENNReal.ofReal (Real.exp 1) := by
    rw [e1]
    show ENNReal.ofReal (Real.exp ((2 : ℝ) * 1 / (2 * 1))) = _
    rw [s1]
  have hw0 : expWeight 2 1 (testUtil true false) = 1 := by
    rw [e0]
    show ENNReal.ofReal (Real.exp ((2 : ℝ) * 0 / (2 * 1))) = 1
    rw [s0, Real.exp_zero, ENNReal.ofReal_one]
  have hZ : expZ (testUtil true) 2 1
      = 1 + ENNReal.ofReal (Real.exp 1) := by
    show (∑ r, expWeight 2 1 (testUtil true r)) = _
    rw [Fintype.sum_bool, hw1, hw0]
    exact add_comm _ _
  rw [expMech_apply, hw1, hZ]

/-! ## M4 tests: geometric mass ratios and coefficient -/

/-- Mass ratio chain at `-1, 0, 1`. -/
theorem geom_ratio_chain (ρ : ℝ≥0∞) :
    geomUnnorm ρ (-1) = ρ * geomUnnorm ρ 0
      ∧ geomUnnorm ρ 0 = 1
      ∧ geomUnnorm ρ 1 = ρ * geomUnnorm ρ 0 := by
  have n1 : (-1 : ℤ).natAbs = 1 := by decide
  have n0 : (0 : ℤ).natAbs = 0 := by decide
  have n1' : (1 : ℤ).natAbs = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · show ρ ^ (-1 : ℤ).natAbs = ρ * ρ ^ (0 : ℤ).natAbs
    rw [n1, n0, pow_one, pow_zero, mul_one]
  · show ρ ^ (0 : ℤ).natAbs = 1
    rw [n0, pow_zero]
  · show ρ ^ (1 : ℤ).natAbs = ρ * ρ ^ (0 : ℤ).natAbs
    rw [n1', n0, pow_one, pow_zero, mul_one]

/-- Normalizing coefficient at `α = 1 / 2` equals `1 / 3`. -/
theorem geom_coeff_half :
    (∑' z : ℤ, geomUnnorm (ENNReal.ofReal (1 / 2)) z)⁻¹
      = ENNReal.ofReal (1 / 3) := by
  have hρ0 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_pos.mpr (by norm_num)
  have hρ1 : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)]
    norm_num
  have h := geomUnnorm_inv_tsum (ENNReal.ofReal (1 / 2)) hρ0 hρ1
  rw [h, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 2)]
  congr 1
  norm_num

/-! ## M5 test: nonuniform fixed distribution -/

/-- Database-independent two-output utility. -/
noncomputable def constUtil (_ : Unit) (r : Bool) : ℝ :=
  if r then 1 else 0

theorem constUtil_const : ∀ d d' r, constUtil d r = constUtil d' r :=
  fun _ _ _ => rfl

/-- The fixed distribution is `0`-DP. -/
theorem m5_zero_dp (adj : Unit → Unit → Prop) :
    IsDP (expMech constUtil 2 1) adj 0 :=
  isDP_expMech_const_utility constUtil 2 1 adj constUtil_const

/-- First mass `1 / (1 + e)`. -/
theorem m5_mass_false :
    expMech constUtil 2 1 () false
      = ENNReal.ofReal 1
        / (ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp 1)) := by
  have e0 : constUtil () false = 0 := by simp [constUtil]
  have e1 : constUtil () true = 1 := by simp [constUtil]
  have s0 : (2 : ℝ) * 0 / (2 * 1) = 0 := by norm_num
  have s1 : (2 : ℝ) * 1 / (2 * 1) = 1 := by norm_num
  have hw0 : expWeight 2 1 (constUtil () false) = ENNReal.ofReal 1 := by
    rw [e0]
    show ENNReal.ofReal (Real.exp ((2 : ℝ) * 0 / (2 * 1))) = _
    rw [s0, Real.exp_zero]
  have hw1 : expWeight 2 1 (constUtil () true)
      = ENNReal.ofReal (Real.exp 1) := by
    rw [e1]
    show ENNReal.ofReal (Real.exp ((2 : ℝ) * 1 / (2 * 1))) = _
    rw [s1]
  have hZ : expZ (constUtil ()) 2 1
      = ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp 1) := by
    show (∑ r, expWeight 2 1 (constUtil () r)) = _
    rw [Fintype.sum_bool, hw1, hw0]
    exact add_comm _ _
  rw [expMech_apply, hw0, hZ]

/-- Second mass `e / (1 + e)`. -/
theorem m5_mass_true :
    expMech constUtil 2 1 () true
      = ENNReal.ofReal (Real.exp 1)
        / (ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp 1)) := by
  have e0 : constUtil () false = 0 := by simp [constUtil]
  have e1 : constUtil () true = 1 := by simp [constUtil]
  have s0 : (2 : ℝ) * 0 / (2 * 1) = 0 := by norm_num
  have s1 : (2 : ℝ) * 1 / (2 * 1) = 1 := by norm_num
  have hw0 : expWeight 2 1 (constUtil () false) = ENNReal.ofReal 1 := by
    rw [e0]
    show ENNReal.ofReal (Real.exp ((2 : ℝ) * 0 / (2 * 1))) = _
    rw [s0, Real.exp_zero]
  have hw1 : expWeight 2 1 (constUtil () true)
      = ENNReal.ofReal (Real.exp 1) := by
    rw [e1]
    show ENNReal.ofReal (Real.exp ((2 : ℝ) * 1 / (2 * 1))) = _
    rw [s1]
  have hZ : expZ (constUtil ()) 2 1
      = ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp 1) := by
    show (∑ r, expWeight 2 1 (constUtil () r)) = _
    rw [Fintype.sum_bool, hw1, hw0]
    exact add_comm _ _
  rw [expMech_apply, hw1, hZ]

/-! ## Axiom checks -/

#print axioms isDP_rrMech
#print axioms isDP_expMech
#print axioms isDP_geomMech

end CSLibExtTest.Privacy.DiscreteMechanismsTests
