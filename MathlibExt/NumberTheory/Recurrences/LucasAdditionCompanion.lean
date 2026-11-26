/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.LinearCombination

/-!
# Addition formula for the fundamental Lucas sequence

For fixed $m$, the backward term $Q^n U_{m-n}$ satisfies the Lucas recurrence up to $n = m$.
Adding it to $U_{m+n}$ gives a sequence with the same initial values and recurrence as $U_m V_n$.

## References

* Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun,
  *Extension of the Equation $\sum_{j=1}^k j F_j^p = F_n^q$ to a Family of Lucas Sequences*,
  The Fibonacci Quarterly 62 (2024), no. 3, pp. 241–257, Lemma 2.1 (iv).
-/

namespace MetaMathlibExt

/-- **Addition formula for the Lucas sequence $U$.** Let $x$ and $y \neq 0$ be integers and let
$(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$. Then for all natural
numbers $n \leq m$, $U_{m+n} = U_m V_n - y^n U_{m-n}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (iv) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem lucasU_add_eq_mul_lucasV_sub (P : LucasSequenceParams) {m n : ℕ}
    (hnm : n ≤ m) :
    lucasU P (m + n) = lucasU P m * lucasV P n - P.q ^ n * lucasU P (m - n) := by
  apply eq_sub_of_add_eq
  induction n using Nat.twoStepInduction with
  | zero => simp only [Nat.add_zero, Nat.sub_zero, pow_zero, one_mul, lucasV]; ring
  | one =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnm)
    simp only [pow_one, Nat.succ_sub_one, lucasV]
    linear_combination lucasU_add_two P k
  | more n ih₀ ih₁ =>
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    rw [← Nat.add_assoc] at h₁
    -- Weight the recurrence at the backward index by Q^(n+1) to reverse the step.
    have hback := lucasU_add_two P (m - (n + 2))
    rw [show m - (n + 2) + 2 = m - n by omega,
      show m - (n + 2) + 1 = m - (n + 1) by omega] at hback
    have hV : lucasV P (n + 2) = P.p * lucasV P (n + 1) - P.q * lucasV P n := rfl
    rw [← Nat.add_assoc, lucasU_add_two P (m + n), hV]
    simp only [pow_succ] at h₁ ⊢
    linear_combination P.p * h₁ - P.q * h₀ + (P.q ^ n * P.q) * hback

end MetaMathlibExt
