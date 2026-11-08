/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedTribonacci
import Mathlib.Tactic.Ring

/-!
# The two-sided Tribonacci sequence

The Tribonacci sequence extended to all integer indices, normalized by `T₀ = 0` and
`T₁ = T₂ = 1`: `tribonacciInt n = generalizedTribonacci 0 1 1 n` for `n ≥ 0`, and the backward
recurrence `T_{n} = T_{n+3} - T_{n+2} - T_{n+1}` for negative indices. It satisfies
`T_{n+3} = T_{n+2} + T_{n+1} + T_n` for all `n : ℤ`, and `T_n = tribonacci (n + 1)` for `n : ℕ`.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci
Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/

namespace MetaMathlibExt

@[expose] public section

/--
The backward half of the normalized Tribonacci sequence: `tribonacciBackward m`
is `T_{-m}`. The first three clauses encode `T₀ = 0`, `T₋₁ = 0`, and
`T₋₂ = 1`; the last clause is the forward recurrence solved for `T_{-m-3}`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public def tribonacciBackward : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | m + 3 =>
      tribonacciBackward m - tribonacciBackward (m + 1) - tribonacciBackward (m + 2)

/--
The two-sided Tribonacci sequence normalized by `T₀ = 0` and `T₁ = T₂ = 1`.
Nonnegative indices use `generalizedTribonacci 0 1 1`; a negative index
`-(m+1)` uses the backward value at `m+1`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public def tribonacciInt : ℤ → ℤ
  | .ofNat n => generalizedTribonacci 0 1 1 n
  | .negSucc m => tribonacciBackward (m + 1)

/--
The normalized two-sided sequence has `T₀ = 0`, the first characteristic
initial value used by Proposition 1.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_zero : tribonacciInt 0 = 0 := by
  rfl

/--
The normalized two-sided sequence has `T₁ = 1`, one of Proposition 1's five
indices whose value lies in `{±1}`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_one : tribonacciInt 1 = 1 := by
  rfl

/--
The normalized two-sided sequence has `T₂ = 1`, one of Proposition 1's five
indices whose value lies in `{±1}`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_two : tribonacciInt 2 = 1 := by
  rfl

/--
The backward extension has `T₋₁ = 0`, fixing the first value across the
negative/nonnegative boundary.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_one : tribonacciInt (-1) = 0 := by
  rfl

/--
The backward extension has `T₋₂ = 1`, one of Proposition 1's five indices
whose value lies in `{±1}`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_two : tribonacciInt (-2) = 1 := by
  rfl

/--
The backward extension has `T₋₃ = -1`, one of Proposition 1's five indices
whose value lies in `{±1}`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_three : tribonacciInt (-3) = -1 := by
  rfl

/--
The backward extension has `T₋₇ = 1`, one of Proposition 1's five indices
whose value lies in `{±1}`.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_seven : tribonacciInt (-7) = 1 := by
  rfl

/--
The two-sided sequence satisfies `T_{n+3} = T_{n+2} + T_{n+1} + T_n` at every
integer index, including the three indices that cross zero.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_add_three (n : ℤ) :
    tribonacciInt (n + 3) =
      tribonacciInt (n + 2) + tribonacciInt (n + 1) + tribonacciInt n := by
  cases n with
  | ofNat n =>
      change generalizedTribonacci 0 1 1 (n + 3) =
        generalizedTribonacci 0 1 1 (n + 2) +
          generalizedTribonacci 0 1 1 (n + 1) + generalizedTribonacci 0 1 1 n
      rw [generalizedTribonacci]
  | negSucc n =>
      rcases n with _ | _ | _ | n
      · change generalizedTribonacci 0 1 1 2 =
          generalizedTribonacci 0 1 1 1 + generalizedTribonacci 0 1 1 0 +
            tribonacciBackward 1
        rfl
      · change generalizedTribonacci 0 1 1 1 =
          generalizedTribonacci 0 1 1 0 + tribonacciBackward 1 +
            tribonacciBackward 2
        rfl
      · change generalizedTribonacci 0 1 1 0 =
          tribonacciBackward 1 + tribonacciBackward 2 + tribonacciBackward 3
        rfl
      · change tribonacciBackward (n + 1) =
          tribonacciBackward (n + 2) + tribonacciBackward (n + 3) +
            tribonacciBackward (n + 4)
        have hrec : tribonacciBackward (n + 4) =
            tribonacciBackward (n + 1) - tribonacciBackward (n + 2) -
              tribonacciBackward (n + 3) := by
          rw [show n + 4 = (n + 1) + 3 by omega, tribonacciBackward]
        rw [hrec]
        ring

/--
For every natural `n`, the normalized two-sided term `T_n` is the integer cast
of the repository Tribonacci term at `n+1`. This is the bridge between
Proposition 1's normalization and Theorem 1's natural-indexed sequence.
Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1 and Proposition 1 notation.
-/
public theorem tribonacciInt_nat_eq (n : ℕ) :
    tribonacciInt (n : ℤ) = (tribonacci (n + 1) : ℤ) := by
  change generalizedTribonacci 0 1 1 n = (tribonacci (n + 1) : ℤ)
  exact generalizedTribonacci_zero_one_one_eq_tribonacci_succ n

end

end MetaMathlibExt
