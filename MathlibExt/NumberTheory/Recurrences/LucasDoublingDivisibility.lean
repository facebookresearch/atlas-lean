/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.NumberTheory.Recurrences.LucasAdditionCompanion
import all MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition
import Mathlib.Tactic.LinearCombination

/-!
# Doubling and divisibility for Lucas sequences

## References

* Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
  Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, pp. 1–41,
  Lemma 1.1 (pp. 3–4). <https://math.colgate.edu/~integers/y36/y36.pdf>
* Dan Kalman and Robert Mena, *The Fibonacci Numbers—Exposed*, Mathematics Magazine 76
  (2003), no. 3, pp. 167–181, p. 174; and T. N. Shorey and R. Tijdeman,
  *Exponential Diophantine Equations*, Cambridge University Press (1986), pp. 33–35.
  Křížek and Somer cite these for the closed forms surrounding their Binet proof;
  the proof here uses recurrence identities instead.
-/

namespace MetaMathlibExt

open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted in
/-- **Doubling formulas and divisibility for Lucas sequences.** Let $U$ and $V$ be the Lucas
sequences with integer parameters $P$ and $Q \neq 0$. Then $U_{2n} = U_n V_n$ and
$U_{2n+1} = -Q U_n^2 + U_{n+1}^2$ for every natural number $n$, and $U_m \mid U_n$ for all
natural numbers $m$ and $n$ with $m \mid n$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Lemma 1.1
(`integers-2024-A36-lem-1-1`). -/
public theorem lucasU_two_mul_and_lucasU_dvd (params : LucasSequenceParams) :
    (∀ n, lucasU params (2 * n) = lucasU params n * lucasV params n) ∧
    (∀ n, lucasU params (2 * n + 1) =
      -params.q * lucasU params n ^ 2 + lucasU params (n + 1) ^ 2) ∧
    (∀ m n, m ∣ n → lucasU params m ∣ lucasU params n) := by
  refine ⟨lucasU_two_mul_eq_lucasU_mul_lucasV params, ?_, ?_⟩
  · intro n
    rw [show 2 * n + 1 = (n + 1) + n by omega,
      lucasU_add_eq_mul_lucasV_sub params (Nat.le_succ n),
      lucasV_eq_two_mul_lucasU_add_one_sub params n,
      show n + 1 - n = 1 by omega, show lucasU params 1 = 1 from rfl]
    linear_combination lucasU_cassini params n + lucasU params n * lucasU_add_two params n
  · rintro m _ ⟨k, rfl⟩
    induction k using Nat.twoStepInduction with
    | zero => simp [lucasU]
    | one => simp
    | more k ih₀ ih₁ =>
      have hm : m ≤ m * (k + 1) := by rw [Nat.mul_succ]; omega
      have hsub : m * (k + 1) - m = m * k := by simp [Nat.mul_succ]
      rw [show m * (k + 2) = m * (k + 1) + m by rw [Nat.mul_succ],
        lucasU_add_eq_mul_lucasV_sub params hm, hsub]
      exact Int.dvd_sub (dvd_mul_of_dvd_left ih₁ _) (dvd_mul_of_dvd_right ih₀ _)

end MetaMathlibExt
