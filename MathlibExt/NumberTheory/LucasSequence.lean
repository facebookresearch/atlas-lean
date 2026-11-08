/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Lucas sequences

This module defines the two Lucas sequences `U(P, Q)` and `V(P, Q)` for
integer parameters with `Q ≠ 0`.

Sources:

* Christian Ballot, *A Further Generalization of a Congruence of Wolstenholme*,
  Journal of Integer Sequences 15 (2012),
  <https://cs.uwaterloo.ca/journals/JIS/VOL15/Ballot/ballot4.tex>.
* Evis Ieronymou, *Congruences Involving Sums of Ratios of Lucas Sequences*,
  Journal of Integer Sequences 17 (2014),
  <https://cs.uwaterloo.ca/journals/JIS/VOL17/Ieronymou/ier5.tex>.
* Tian-Xiao He, *Impulse Response Sequences and Construction of Number Sequence
  Identities*, Journal of Integer Sequences 16 (2013),
  <https://cs.uwaterloo.ca/journals/JIS/VOL16/He/he13.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Integer parameters for a pair of Lucas sequences. The source convention
requires the second parameter to be nonzero. -/
structure LucasSequenceParams where
  p : ℤ
  q : ℤ
  q_ne_zero : q ≠ 0

/-- The additional coprimality condition imposed in some applications of
Lucas sequences. -/
def LucasSequenceParams.IsCoprime (params : LucasSequenceParams) : Prop :=
  ∃ x y : ℤ, x * params.p + y * params.q = 1

/-- The Lucas sequence `U(P, Q)`, initialized by `0, 1`. -/
def lucasU (params : LucasSequenceParams) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => params.p * lucasU params (n + 1) - params.q * lucasU params n

/-- The companion Lucas sequence `V(P, Q)`, initialized by `2, P`. -/
def lucasV (params : LucasSequenceParams) : ℕ → ℤ
  | 0 => 2
  | 1 => params.p
  | n + 2 => params.p * lucasV params (n + 1) - params.q * lucasV params n

/-- The parameter pair `(P, Q) = (1, -1)` giving the Fibonacci and classical
Lucas-number sequences. -/
def fibonacciLucasParams : LucasSequenceParams where
  p := 1
  q := -1
  q_ne_zero := by decide

/-- The classical Lucas numbers `2, 1, 3, 4, 7, …`. -/
def lucasNumber : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucasNumber (n + 1) + lucasNumber n

/-- The `U` sequence for `(P, Q) = (1, -1)` is the Fibonacci sequence. -/
theorem lucasU_fibonacciLucasParams (n : ℕ) :
    lucasU fibonacciLucasParams n = (Nat.fib n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      calc
        lucasU fibonacciLucasParams (n + 2) =
            lucasU fibonacciLucasParams (n + 1) + lucasU fibonacciLucasParams n := by
          simp [lucasU, fibonacciLucasParams]
        _ = (Nat.fib (n + 1) : ℤ) + (Nat.fib n : ℤ) := by rw [ih1, ih2]
        _ = (Nat.fib (n + 2) : ℤ) := by rw [Nat.fib_add_two, Nat.cast_add, add_comm]

/-- The two-step recurrence for `lucasU`, as a rewrite rule. -/
theorem lucasU_add_two (params : LucasSequenceParams) (n : ℕ) :
    lucasU params (n + 2) =
      params.p * lucasU params (n + 1) - params.q * lucasU params n := rfl

/-- Cassini's identity for `lucasU`:
`U (n + 1) ^ 2 - U n * U (n + 2) = Q ^ n`. -/
theorem lucasU_cassini (params : LucasSequenceParams) (n : ℕ) :
    lucasU params (n + 1) ^ 2 - lucasU params n * lucasU params (n + 2) =
      params.q ^ n := by
  induction n with
  | zero => simp [lucasU]
  | succ n ih =>
    have r1 := lucasU_add_two params n
    have r2 := lucasU_add_two params (n + 1)
    show lucasU params (n + 2) ^ 2 -
        lucasU params (n + 1) * lucasU params (n + 3) = params.q ^ (n + 1)
    linear_combination
      lucasU params (n + 2) * r1 + params.q * ih - lucasU params (n + 1) * r2

/-- The `V` sequence for `(P, Q) = (1, -1)` is the classical Lucas-number
sequence. -/
theorem lucasV_fibonacciLucasParams (n : ℕ) :
    lucasV fibonacciLucasParams n = (lucasNumber n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      calc
        lucasV fibonacciLucasParams (n + 2) =
            lucasV fibonacciLucasParams (n + 1) + lucasV fibonacciLucasParams n := by
          simp [lucasV, fibonacciLucasParams]
        _ = (lucasNumber (n + 1) : ℤ) + (lucasNumber n : ℤ) := by rw [ih1, ih2]
        _ = (lucasNumber (n + 2) : ℤ) := by simp [lucasNumber]

end

end MetaMathlibExt
