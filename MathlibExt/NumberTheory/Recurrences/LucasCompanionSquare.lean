/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Ring

/-!
# Square of the companion Lucas sequence

The companion sequence satisfies the same recurrence as a linear combination of two
consecutive terms of the fundamental sequence. Cassini's identity gives the square formula.
-/

namespace MetaMathlibExt

private theorem lucasV_eq_two_mul_lucasU_succ_sub (P : LucasSequenceParams) (n : ℕ) :
    lucasV P n = 2 * lucasU P (n + 1) - P.p * lucasU P n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasV, lucasU]
  | one =>
      simp [lucasV, lucasU]
      ring
  | more n ih₀ ih₁ =>
      change P.p * lucasV P (n + 1) - P.q * lucasV P n =
        2 * lucasU P ((n + 1) + 2) - P.p * lucasU P (n + 2)
      rw [ih₀, ih₁, lucasU_add_two P (n + 1), lucasU_add_two P n]
      ring

/-- **Square of the companion Lucas sequence.** Let $x$ and $y \neq 0$ be integers and let
$(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$. Then for every natural
number $n$, $V_n^2 = (x^2 - 4y) U_n^2 + 4 y^n$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vi) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem lucasV_sq_eq (P : LucasSequenceParams) (n : ℕ) :
    lucasV P n ^ 2 = (P.p ^ 2 - 4 * P.q) * lucasU P n ^ 2 + 4 * P.q ^ n := by
  rw [lucasV_eq_two_mul_lucasU_succ_sub]
  calc
    _ = (P.p ^ 2 - 4 * P.q) * lucasU P n ^ 2 +
          4 * (lucasU P (n + 1) ^ 2 - lucasU P n * lucasU P (n + 2)) := by
        rw [lucasU_add_two P n]
        ring
    _ = _ := by rw [lucasU_cassini]

end MetaMathlibExt
