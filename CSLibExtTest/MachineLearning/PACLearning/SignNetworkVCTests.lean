/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.SignNetworkVC
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for sign-network VC bounds

A definitional check that a zero-layer network is a halfspace of VC
dimension two in dimension one, closed numeric instances of the
exponential-polynomial inversion on both sides of the threshold, an
applied instance of the VC bound at a closed architecture, and axiom
audits for the public theorems of the production module.
-/

namespace Cslib.MachineLearning.PACLearning

/-- Zero hidden layers in dimension one: a single neuron is a halfspace,
of VC dimension two. -/
example : vcDim (networkClass 1 (fun _ => 1) 0) = 2 := by
  rw [vcDim_networkClass_zero]

/-- Above threshold, directly: `(exp 1 * 20) ^ 2 < 2 ^ 20` by an explicit
upper bound on `exp 1`. -/
example : ¬ (2 : ℝ) ^ (20 : ℕ) ≤ (Real.exp 1 * (20 : ℝ)) ^ (2 : ℕ) := by
  have hupper : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hbase : Real.exp 1 * 20 ≤ (2.7182818286 : ℝ) * 20 :=
    mul_le_mul_of_nonneg_right (le_of_lt hupper)
      (show (0 : ℝ) ≤ 20 by norm_num)
  have hpow : (Real.exp 1 * 20) ^ (2 : ℕ) ≤
      ((2.7182818286 : ℝ) * 20) ^ (2 : ℕ) :=
    pow_le_pow_left₀
      (mul_nonneg (le_of_lt (Real.exp_pos 1)) (show (0 : ℝ) ≤ 20 by norm_num))
      hbase 2
  have hnum : ((2.7182818286 : ℝ) * 20) ^ (2 : ℕ) < (2 : ℝ) ^ (20 : ℕ) := by
    norm_num
  intro hle
  exact (not_le_of_gt hnum) (le_trans hle hpow)

/-- Applied VC bound at a closed architecture: `d = 1`, width one,
one hidden layer, `paramCount = 4`. -/
example : (vcDim (networkClass 1 (fun _ => 1) 1) : ℝ) ≤
    4 * ((4 : ℕ) : ℝ) * Real.log (2 * ((4 : ℕ) : ℝ)) / Real.log 2 := by
  have hpc : paramCount 1 (fun _ => 1) 1 = 4 := by decide
  have hw : ∀ i, i < 1 → 0 < (fun _ => 1) i := fun i _ => Nat.zero_lt_one
  have hle := vcDim_networkClass_le 1 (fun _ => 1) 1 hw
  rw [hpc] at hle
  exact hle

/-- The closed-form bound at `E = 4` evaluates to `48`, since
`Real.log 8 = 3 * Real.log 2`. -/
example : 4 * ((4 : ℕ) : ℝ) * Real.log (2 * ((4 : ℕ) : ℝ)) / Real.log 2
    = 48 := by
  have hlog8 : Real.log (2 * ((4 : ℕ) : ℝ)) = 3 * Real.log 2 := by
    rw [show (2 : ℝ) * ((4 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hne : Real.log 2 ≠ 0 :=
    (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'
  rw [hlog8, div_eq_iff hne]
  ring

/-- Applied VC bound at a closed architecture, evaluated: `d = 1`,
width one, one hidden layer, `paramCount = 4`, bound `48`. -/
example : (vcDim (networkClass 1 (fun _ => 1) 1) : ℝ) ≤ 48 := by
  have hpc : paramCount 1 (fun _ => 1) 1 = 4 := by decide
  have hw : ∀ i, i < 1 → 0 < (fun _ => 1) i := fun i _ => Nat.zero_lt_one
  have hle := vcDim_networkClass_le 1 (fun _ => 1) 1 hw
  rw [hpc] at hle
  have hRHS : 4 * ((4 : ℕ) : ℝ) * Real.log (2 * ((4 : ℕ) : ℝ)) / Real.log 2
      = 48 := by
    have hlog8 : Real.log (2 * ((4 : ℕ) : ℝ)) = 3 * Real.log 2 := by
      rw [show (2 : ℝ) * ((4 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hne : Real.log 2 ≠ 0 :=
      (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'
    rw [hlog8, div_eq_iff hne]
    ring
  rw [hRHS] at hle
  exact hle

#print axioms networkClass_hasFiniteVCDim
#print axioms vcDim_networkClass_le
#print axioms vcDim_networkClass_zero

end Cslib.MachineLearning.PACLearning
