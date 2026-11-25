/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.OnlineGradientDescentAnytime
import MathlibExt.Analysis.Convex.OnlineGradientDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Tests for anytime online gradient descent

Concrete numeric checks of the anytime regret bound: a singleton feasible
set with zero regret, linear losses with the identity projection at `T = 1`
and `T = 2`, agreement of constant-schedule iterates with the fixed-step
iterates, and axiom audits of the three main results.
-/

namespace CSLibExtTest.MachineLearning.OnlineGradientDescentAnytime

open Cslib.MachineLearning.OnlineGradientDescentAnytime

/-- A singleton feasible set gives zero regret over any horizon. -/
theorem singleton_zero_regret (xstar : ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ → ℝ)
    (η : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        (f t (ogdIterVarying (fun _ => xstar) g η xstar t) - f t xstar)
      = 0 := by
  have hall : ∀ t, ogdIterVarying (fun _ => xstar) g η xstar t = xstar := by
    intro t
    induction t with
    | zero => rfl
    | succ t _ => simp [ogdIterVarying]
  simp [hall]

/-- The constant projection onto the singleton is nonexpansive. -/
example (xstar : ℝ) : LipschitzWith 1 (fun _ : ℝ => xstar) :=
  (LipschitzWith.const xstar).weaken zero_le_one

/-- The identity projection is nonexpansive. -/
example : LipschitzWith 1 (id : ℝ → ℝ) := LipschitzWith.id

/-- Diameter bound at round `t = 0` for the concrete two-round instance. -/
example : ‖ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
      (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 0 - (-1)‖ ≤ 4 := by
  simp only [ogdIterVarying]
  norm_num [Real.norm_eq_abs]

/-- First iterate of the concrete two-round instance. -/
example : ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
      (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 1 = -1 := by
  show ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
      (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 (0 + 1) = -1
  simp only [ogdIterVarying, Nat.cast_zero, zero_add, Real.sqrt_one, id_eq,
    smul_eq_mul]
  norm_num

/-- Diameter bound at round `t = 1` for the concrete two-round instance. -/
example : ‖ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
      (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 1 - (-1)‖ ≤ 4 := by
  have hiter : ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
      (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 1 = -1 := by
    show ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
        (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 (0 + 1) = -1
    simp only [ogdIterVarying, Nat.cast_zero, zero_add, Real.sqrt_one, id_eq,
      smul_eq_mul]
    norm_num
  rw [hiter]
  norm_num [Real.norm_eq_abs]

/-- Second iterate with varying steps and a state-dependent oracle. -/
example : ogdIterVarying (id : ℝ → ℝ) (fun t x => x - (t : ℝ))
      (fun t => (t : ℝ) + 1) 1 2 = 2 := by
  show ogdIterVarying (id : ℝ → ℝ) (fun t x => x - (t : ℝ))
      (fun t => (t : ℝ) + 1) 1 (1 + 1) = 2
  simp only [ogdIterVarying, Nat.cast_one, Nat.cast_zero, id_eq, smul_eq_mul]
  norm_num

/-- Gradient-norm bound for the concrete two-round instance. -/
example (t : ℕ) (x : ℝ) : ‖(fun _ _ => (1 / 2 : ℝ)) t x‖ ≤ 1 := by
  show ‖(1 / 2 : ℝ)‖ ≤ 1
  norm_num [Real.norm_eq_abs]

/-- Numeric regret check at `T = 1` for the concrete instance. -/
example : ∑ t ∈ Finset.range 1, ((fun _ x : ℝ => (1 / 2 : ℝ) * x) t
      (ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
        (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 t)
      - (fun _ x : ℝ => (1 / 2 : ℝ) * x) t (-1))
      ≤ (3 / 2) * 1 * 4 * Real.sqrt (1 : ℝ) := by
  rw [Finset.sum_range_one]
  simp only [ogdIterVarying, Real.sqrt_one]
  norm_num

/-- Numeric regret check at `T = 2` for the concrete instance. -/
example : ∑ t ∈ Finset.range 2, ((fun _ x : ℝ => (1 / 2 : ℝ) * x) t
      (ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
        (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 t)
      - (fun _ x : ℝ => (1 / 2 : ℝ) * x) t (-1))
      ≤ (3 / 2) * 1 * 4 * Real.sqrt 2 := by
  have hiter : ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
      (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 1 = -1 := by
    show ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
        (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 (0 + 1) = -1
    simp only [ogdIterVarying, Nat.cast_zero, zero_add, Real.sqrt_one, id_eq,
      smul_eq_mul]
    norm_num
  show ∑ t ∈ Finset.range (1 + 1), ((fun _ x : ℝ => (1 / 2 : ℝ) * x) t
      (ogdIterVarying (id : ℝ → ℝ) (fun _ _ => (1 / 2 : ℝ))
        (fun t => 4 / (1 * Real.sqrt ((t : ℝ) + 1))) 1 t)
      - (fun _ x : ℝ => (1 / 2 : ℝ) * x) t (-1))
      ≤ (3 / 2) * 1 * 4 * Real.sqrt 2
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [hiter]
  simp only [ogdIterVarying]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  linarith [hsqrt]

/-- Constant-schedule iterates agree with the fixed-step iterates: both
sides compute to `-1` on a concrete two-round example. -/
example : ogdIterVarying (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (fun _ => 1 / 2) 0 2
      = -1
    ∧ ogdIter (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (1 / 2) 0 2 = -1 := by
  have hstep : ∀ t, ogdIterVarying (fun x : ℝ => x) (fun _ _ => (1 : ℝ))
      (fun _ => 1 / 2) 0 (t + 1)
      = ogdIterVarying (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (fun _ => 1 / 2)
        0 t - 1 / 2 := by
    intro t
    simp only [ogdIterVarying, smul_eq_mul]
    ring
  have gstep : ∀ t, ogdIter (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (1 / 2) 0
      (t + 1)
      = ogdIter (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (1 / 2) 0 t - 1 / 2 := by
    intro t
    simp only [ogdIter, smul_eq_mul]
    ring
  have hz : ogdIterVarying (fun x : ℝ => x) (fun _ _ => (1 : ℝ))
      (fun _ => 1 / 2) 0 0 = 0 := rfl
  have h1 : ogdIterVarying (fun x : ℝ => x) (fun _ _ => (1 : ℝ))
      (fun _ => 1 / 2) 0 1 = -(1 / 2) := by
    have h := hstep 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, hz] at h
    norm_num at h
    exact h
  have h2 : ogdIterVarying (fun x : ℝ => x) (fun _ _ => (1 : ℝ))
      (fun _ => 1 / 2) 0 2 = -1 := by
    have h := hstep 1
    rw [show (1 : ℕ) + 1 = 2 from rfl] at h
    rw [h1] at h
    norm_num at h
    exact h
  have gz : ogdIter (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (1 / 2) 0 0
      = 0 := rfl
  have g1 : ogdIter (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (1 / 2) 0 1
      = -(1 / 2) := by
    have h := gstep 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, gz] at h
    norm_num at h
    exact h
  have g2 : ogdIter (fun x : ℝ => x) (fun _ _ => (1 : ℝ)) (1 / 2) 0 2
      = -1 := by
    have h := gstep 1
    rw [show (1 : ℕ) + 1 = 2 from rfl] at h
    rw [g1] at h
    norm_num at h
    exact h
  exact ⟨h2, g2⟩

#print axioms ogdIterVarying_const
#print axioms ogd_regret_varying
#print axioms ogd_regret_anytime

end CSLibExtTest.MachineLearning.OnlineGradientDescentAnytime
