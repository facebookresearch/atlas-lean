/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Horner polynomial evaluation

MIT 6.046J Spring 2015, Lecture 3, page 1 represents a polynomial by its
coefficients in ascending power order and evaluates it by nested multiply-adds.
`hornerEval` materializes the canonical coefficient list and executes its right
monadic fold, processing the highest coefficient first with an accumulator of zero.

The cost counts one scalar multiplication and one scalar addition per coefficient.
List construction, pointer operations, index arithmetic, control flow, calls and
monadic plumbing are free. Initializing at zero executes both operations even for
the highest coefficient, so the exact count is `2 * n`. This is an arithmetic
operation count; it makes no statement about bit cost or stack space.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {R : Type u} [CommSemiring R]

/-- Execute Horner's nested evaluation on all coefficients, retaining their operation cost. -/
def hornerEval {n : Nat} (x : R) (coefficients : Fin n → R) : TimeM Nat R :=
  (List.ofFn coefficients).foldrM (fun coefficient value => do
    ✓[2]
    pure (coefficient + x * value)) 0

private theorem hornerFold_time (x : R) (coefficients : List R) :
    (coefficients.foldrM (fun coefficient value => do
      ✓[2]
      pure (coefficient + x * value)) 0 : TimeM Nat R).time =
      2 * coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldrM_cons, time_bind, time_tick, time_pure,
        Nat.add_zero, List.length_cons, ih, Nat.mul_add, Nat.mul_one]

/-- Every coefficient executes exactly one multiplication and one addition. -/
@[simp]
theorem hornerEval_time {n : Nat} (x : R) (coefficients : Fin n → R) :
    (hornerEval x coefficients).time = 2 * n := by
  simpa only [hornerEval, List.length_ofFn] using
    hornerFold_time x (List.ofFn coefficients)

/-- The actual fold returns the complete coefficient/power sum in the source order. -/
theorem hornerEval_ret_eq_sum {n : Nat} (x : R) (coefficients : Fin n → R) :
    (hornerEval x coefficients).ret = ∑ i : Fin n, coefficients i * x ^ i.val := by
  induction n with
  | zero => simp [hornerEval]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [hornerEval, List.ofFn_succ, List.foldrM_cons, ret_bind, ret_pure,
        Fin.val_zero, pow_zero, mul_one]
      change coefficients 0 + x *
        (hornerEval x (fun i : Fin n => coefficients i.succ)).ret = _
      rw [ih, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, pow_succ]
      ac_rfl

/-- Erasing the executed cost gives evaluation of the canonical coefficient polynomial. -/
theorem hornerEval_ret_eq_eval [DecidableEq R] {n : Nat} (x : R)
    (coefficients : Fin n → R) :
    (hornerEval x coefficients).ret = (Polynomial.ofFn n coefficients).eval x := by
  rw [hornerEval_ret_eq_sum, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

/-- The total extension to no coefficients computes zero without arithmetic. -/
@[simp]
theorem hornerEval_empty (x : R) (coefficients : Fin 0 → R) :
    hornerEval x coefficients = ⟨0, 0⟩ := by
  apply TimeM.ext
  · simp [hornerEval_ret_eq_sum]
  · simp

/-- Zero initialization retains the two executed operations for a constant polynomial. -/
@[simp]
theorem hornerEval_singleton (x : R) (coefficients : Fin 1 → R) :
    hornerEval x coefficients = ⟨coefficients 0, 2⟩ := by
  apply TimeM.ext
  · simp [hornerEval_ret_eq_sum]
  · simp

/-- At zero a nonempty coefficient vector returns its constant coefficient. -/
@[simp]
theorem hornerEval_zero {n : Nat} (coefficients : Fin (n + 1) → R) :
    (hornerEval 0 coefficients).ret = coefficients 0 := by
  rw [hornerEval_ret_eq_sum, Fin.sum_univ_succ]
  simp

end Cslib.Algorithms.Lean.TimeM
