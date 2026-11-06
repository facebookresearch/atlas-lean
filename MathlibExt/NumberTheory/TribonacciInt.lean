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
**Backward half of the two-sided Tribonacci sequence.** The integer sequence $(B_m)_{m \ge 0}$
is defined by $B_0 = 0$, $B_1 = 0$, $B_2 = 1$ and $B_{m+3} = B_m - B_{m+1} - B_{m+2}$ for
every $m \ge 0$.

Writing $B_m = T_{-m}$, the initial values are $T_0 = 0$, $T_{-1} = 0$, $T_{-2} = 1$, and the
recursion is the Tribonacci recurrence $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ solved for $T_n$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public def tribonacciBackward : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | m + 3 =>
      tribonacciBackward m - tribonacciBackward (m + 1) - tribonacciBackward (m + 2)

/--
**Two-sided Tribonacci sequence.** The integer sequence $(T_n)_{n \in \mathbb{Z}}$ is defined on
the nonnegative indices by $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$
for $n \ge 0$, and on the negative indices by $T_{-1} = 0$, $T_{-2} = 1$ and
$T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for $m \ge 0$, the recurrence solved for its lowest
term.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public def tribonacciInt : ℤ → ℤ
  | .ofNat n => generalizedTribonacci 0 1 1 n
  | .negSucc m => tribonacciBackward (m + 1)

/--
**The two-sided Tribonacci sequence at $0$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_0 = 0$.

This is the first initial value used by Proposition 1.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_zero : tribonacciInt 0 = 0 := by
  rfl

/--
**The two-sided Tribonacci sequence at $1$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_1 = 1$.

This is one of Proposition 1's five indices at which the value lies in $\{\pm 1\}$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_one : tribonacciInt 1 = 1 := by
  rfl

/--
**The two-sided Tribonacci sequence at $2$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_2 = 1$.

This is one of Proposition 1's five indices at which the value lies in $\{\pm 1\}$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_two : tribonacciInt 2 = 1 := by
  rfl

/--
**The two-sided Tribonacci sequence at $-1$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_{-1} = 0$.

This fixes the first value across the boundary between negative and nonnegative indices.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_one : tribonacciInt (-1) = 0 := by
  rfl

/--
**The two-sided Tribonacci sequence at $-2$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_{-2} = 1$.

This is one of Proposition 1's five indices at which the value lies in $\{\pm 1\}$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_two : tribonacciInt (-2) = 1 := by
  rfl

/--
**The two-sided Tribonacci sequence at $-3$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_{-3} = -1$.

This is one of Proposition 1's five indices at which the value lies in $\{\pm 1\}$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_three : tribonacciInt (-3) = -1 := by
  rfl

/--
**The two-sided Tribonacci sequence at $-7$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for
$n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for
$m \ge 0$. Then $T_{-7} = 1$.

This is one of Proposition 1's five indices at which the value lies in $\{\pm 1\}$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Proposition 1.
-/
public theorem tribonacciInt_neg_seven : tribonacciInt (-7) = 1 := by
  rfl

/--
**Tribonacci recurrence for the two-sided sequence.** Let $(T_n)_{n \in \mathbb{Z}}$ be the
two-sided Tribonacci sequence: $T_0 = 0$, $T_1 = T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for $n \ge 0$, while $T_{-1} = 0$, $T_{-2} = 1$ and
$T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for $m \ge 0$. Then
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for every integer $n$, including the three indices
$n = -3, -2, -1$ at which the recurrence crosses zero.

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
**On nonnegative indices the two-sided Tribonacci sequence is the shifted Tribonacci
sequence.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided Tribonacci sequence: $T_0 = 0$,
$T_1 = T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for $n \ge 0$, while $T_{-1} = 0$,
$T_{-2} = 1$ and $T_{-m-3} = T_{-m} - T_{-m-1} - T_{-m-2}$ for $m \ge 0$. Let $(t_n)_{n \ge 0}$
be the Tribonacci sequence with $t_0 = t_1 = 0$, $t_2 = 1$ and $t_{n+3} = t_{n+2} + t_{n+1} + t_n$.
Then $T_n = t_{n+1}$ for every natural number $n$.

This is the bridge between Proposition 1's normalization and Theorem 1's natural-indexed
sequence.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1 and Proposition 1 notation.
-/
public theorem tribonacciInt_nat_eq (n : ℕ) :
    tribonacciInt (n : ℤ) = (tribonacci (n + 1) : ℤ) := by
  change generalizedTribonacci 0 1 1 n = (tribonacci (n + 1) : ℤ)
  exact generalizedTribonacci_zero_one_one_eq_tribonacci_succ n

end

end MetaMathlibExt
