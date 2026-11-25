/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition
import Mathlib.Tactic.LinearCombination

/-!
# The companion Lucas sequence in terms of the fundamental sequence

Each positive-index companion term is the difference of two neighboring fundamental terms,
with the earlier term weighted by the second recurrence parameter.
-/

namespace MetaMathlibExt

open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted in
/-- **The companion Lucas sequence in terms of the fundamental one.** Let $x$ and $y \neq 0$ be
integers and let $(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by
$U_0 = 0$, $U_1 = 1$, $V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$.
Then $V_n = U_{n+1} - y U_{n-1}$ for every $n \geq 1$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (iii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem lucasV_eq_lucasU_succ_sub (P : LucasSequenceParams) {n : ℕ} (hn : 1 ≤ n) :
    lucasV P n = lucasU P (n + 1) - P.q * lucasU P (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [Nat.succ_sub_one]
  have hadd : 2 * lucasU P (k + 2) = lucasU P (k + 1) * P.p + lucasV P (k + 1) * 1 :=
    two_mul_lucasU_add P (k + 1) 1
  linear_combination lucasU_add_two P k - hadd

end MetaMathlibExt
