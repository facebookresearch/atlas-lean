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
# Addition formula for Lucas sequences

This module proves the addition formula $2U_{m+n} = U_m V_n + V_m U_n$ for the Lucas sequences
$U(P, Q)$ and $V(P, Q)$ (`two_mul_lucasU_add`). This is the integer specialization of the identity
$2F_{n+m} = F_m L_n + L_m F_n$ for the generalized Fibonacci and Lucas numbers of Kruchinin and
Perminova, stated as Proposition 1 in their preprint arXiv:2406.02937v1, *Identities and
Generating Functions of Products of Generalized Fibonacci numbers, Catalan and Harmonic Numbers*.

The proof is an induction on $n$: both sides satisfy the recurrence
$x_{n+2} = P x_{n+1} - Q x_n$, and the case $n = 1$ is the identity $V_m = 2U_{m+1} - P U_m$.
-/

public section

namespace MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted

open MetaMathlibExt

/-- The companion Lucas sequence in terms of the first one: $V_n = 2U_{n+1} - P U_n$. -/
private theorem lucasV_eq_two_mul_lucasU_add_one_sub (params : LucasSequenceParams) (n : ℕ) :
    lucasV params n = 2 * lucasU params (n + 1) - params.p * lucasU params n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasU, lucasV]
  | one => simp only [lucasU, lucasV]; ring
  | more n ih0 ih1 =>
    have hV : lucasV params (n + 2) =
        params.p * lucasV params (n + 1) - params.q * lucasV params n := rfl
    rw [hV, lucasU_add_two params (n + 1), ih0, ih1]
    linear_combination params.p * lucasU_add_two params n

/-- **Addition formula $2U_{m+n} = U_m V_n + V_m U_n$ for Lucas sequences.** For all integers
$P$ and $Q$ with $Q \neq 0$ and all natural numbers $m$ and $n$, the Lucas sequences
$U_n = U_n(P, Q)$ and $V_n = V_n(P, Q)$ satisfy $2U_{m+n} = U_m V_n + V_m U_n$.

This is the integer specialization of the paper's Proposition 1: its generalized Fibonacci
numbers $F_n$ and Lucas numbers $L_n$, with recurrence $x_{n+2} = a x_{n+1} + b x_n$, are
$U_n(a, -b)$ and $V_n(a, -b)$, and the paper allows real $a$ and $b$.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Proposition 1. -/
theorem two_mul_lucasU_add
    (params : MetaMathlibExt.LucasSequenceParams) (m n : ℕ) :
    2 * MetaMathlibExt.lucasU params (m + n) =
      MetaMathlibExt.lucasU params m * MetaMathlibExt.lucasV params n +
        MetaMathlibExt.lucasV params m * MetaMathlibExt.lucasU params n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [lucasU, lucasV, Nat.add_zero]; ring
  | one =>
    rw [lucasV_eq_two_mul_lucasU_add_one_sub params m]
    simp only [lucasU, lucasV]
    ring
  | more n ih0 ih1 =>
    have hV : lucasV params (n + 2) =
        params.p * lucasV params (n + 1) - params.q * lucasV params n := rfl
    rw [show m + (n + 1) = m + n + 1 by omega] at ih1
    rw [show m + (n + 2) = m + n + 2 by omega, lucasU_add_two params (m + n),
      lucasU_add_two params n, hV]
    linear_combination params.p * ih1 - params.q * ih0

end MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted

namespace MetaMathlibExt

/-- **Doubling formula $U_{2n} = U_n V_n$ for Lucas sequences.** Let $P$ and $Q$ be integers with
$Q \ne 0$, and let $U$ and $V$ be the Lucas sequences $U(P, Q)$ and $V(P, Q)$. Then
$U_{2n} = U_n V_n$ for every natural number $n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (i) (`integers-2025-A107-prop-2-3`). -/
theorem lucasU_two_mul_eq_lucasU_mul_lucasV
    (L : LucasSequenceParams) (n : ℕ) :
    lucasU L (2 * n) = lucasU L n * lucasV L n := by
  have h :=
    MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted.two_mul_lucasU_add
      L n n
  rw [show n + n = 2 * n by omega] at h
  have h2 : 2 * lucasU L (2 * n) = 2 * (lucasU L n * lucasV L n) := by
    linear_combination h
  omega

end MetaMathlibExt
