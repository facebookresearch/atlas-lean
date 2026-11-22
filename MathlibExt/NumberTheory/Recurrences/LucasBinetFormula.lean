/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section
/-- `m * alpha ^ (m - 1) * alpha = m * alpha ^ m`; at `m = 0` both sides vanish. -/
private theorem lucas_binet_aux_mul_pow_pred {K : Type*} [Field K] (alpha : K) (m : ℕ) :
    (m : K) * alpha ^ (m - 1) * alpha = (m : K) * alpha ^ m := by
  cases m with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel]; ring

/-- **Binet formulas for Lucas sequences over any field.** Let $P$ and $Q$ be integers with
$Q \ne 0$, let $U_n = U_n(P, Q)$ and $V_n = V_n(P, Q)$ be the associated Lucas sequences, and let
$\alpha$ and $\beta$ be elements of a field $K$ with $\alpha + \beta = P$ and $\alpha \beta = Q$
in $K$. If $\alpha \ne \beta$, then for every natural number $n$,
$U_n = (\alpha^n - \beta^n) / (\alpha - \beta)$ and $V_n = \alpha^n + \beta^n$ in $K$. If
$\beta = \alpha$, then for every natural number $n$, $U_n = n \alpha^{n-1}$ and $V_n = 2 \alpha^n$
in $K$, where $\alpha^{n-1}$ is read as $1$ when $n = 0$. Here the integers $U_n$, $V_n$, $P$, $Q$
and $n$ are mapped into $K$.

No assumption on the characteristic of $K$ is made; for example $K$ may be $\mathbb{Z}/p\mathbb{Z}$
for a prime $p$, where the coefficient $n$ of the double-root formula is read modulo $p$. -/
theorem lucas_binet_formulas_of_field
    {K : Type*} [Field K]
    (params : LucasSequenceParams) (alpha beta : K)
    (hsum : alpha + beta = (params.p : K))
    (hprod : alpha * beta = (params.q : K)) :
    (alpha ≠ beta → ∀ n : ℕ,
      (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
      (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
      (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
      (lucasV params n : K) = 2 * alpha ^ n) := by
  constructor
  · intro hne n
    have hsub : alpha - beta ≠ 0 := sub_ne_zero.mpr hne
    induction n using Nat.twoStepInduction with
    | zero =>
      constructor
      · simp [lucasU]
      · simp [lucasV, pow_zero, one_add_one_eq_two]
    | one =>
      constructor
      · simp [lucasU, pow_one, div_self hsub]
      · simp [lucasV, ← hsum, pow_one]
    | more n ih1 ih2 =>
      obtain ⟨ihU0, ihV0⟩ := ih1
      obtain ⟨ihU1, ihV1⟩ := ih2
      have hU : (lucasU params (n + 2) : K)
          = (params.p : K) * (lucasU params (n + 1) : K)
            - (params.q : K) * (lucasU params n : K) := by
        simp [lucasU, Int.cast_sub, Int.cast_mul]
      have hV : (lucasV params (n + 2) : K)
          = (params.p : K) * (lucasV params (n + 1) : K)
            - (params.q : K) * (lucasV params n : K) := by
        simp [lucasV, Int.cast_sub, Int.cast_mul]
      rw [← hsum, ← hprod] at hU hV
      constructor
      · rw [hU, ihU1, ihU0]
        field_simp
        ring
      · rw [hV, ihV1, ihV0]
        ring
  · intro hbeta n
    have hP : (params.p : K) = 2 * alpha := by rw [← hsum, hbeta]; ring
    have hQ : (params.q : K) = alpha ^ 2 := by rw [← hprod, hbeta]; ring
    induction n using Nat.twoStepInduction with
    | zero =>
      constructor
      · simp [lucasU]
      · simp [lucasV, pow_zero]
    | one =>
      constructor
      · simp [lucasU]
      · simp [lucasV, hP, pow_one]
    | more n ih1 ih2 =>
      obtain ⟨ihU0, ihV0⟩ := ih1
      obtain ⟨ihU1, ihV1⟩ := ih2
      have hU : (lucasU params (n + 2) : K)
          = (params.p : K) * (lucasU params (n + 1) : K)
            - (params.q : K) * (lucasU params n : K) := by
        simp [lucasU, Int.cast_sub, Int.cast_mul]
      have hV : (lucasV params (n + 2) : K)
          = (params.p : K) * (lucasV params (n + 1) : K)
            - (params.q : K) * (lucasV params n : K) := by
        simp [lucasV, Int.cast_sub, Int.cast_mul]
      rw [hP, hQ] at hU hV
      have e1 : n + 1 - 1 = n := by omega
      have e2 : n + 2 - 1 = n + 1 := by omega
      rw [e1] at ihU1
      have hpow : alpha ^ 2 * ((n : K) * alpha ^ (n - 1))
          = alpha * ((n : K) * alpha ^ n) := by
        have h := lucas_binet_aux_mul_pow_pred alpha n
        rw [pow_two]
        linear_combination alpha * h
      constructor
      · rw [hU, ihU1, ihU0, e2, hpow]
        push_cast
        ring
      · rw [hV, ihV1, ihV0]
        ring

/-- **Binet formulas for Lucas sequences.** Let $P$ and $Q$ be integers with $Q \ne 0$, let
$U_n = U_n(P, Q)$ and $V_n = V_n(P, Q)$ be the associated Lucas sequences, and let $\alpha$ and
$\beta$ be elements of a field $K$ of characteristic zero with $\alpha + \beta = P$ and
$\alpha \beta = Q$ in $K$. If $\alpha \ne \beta$, then for every natural number $n$,
$U_n = (\alpha^n - \beta^n) / (\alpha - \beta)$ and $V_n = \alpha^n + \beta^n$ in $K$. If
$\beta = \alpha$, then for every natural number $n$, $U_n = n \alpha^{n-1}$ and $V_n = 2 \alpha^n$
in $K$, where $\alpha^{n-1}$ is read as $1$ when $n = 0$. Here the integers $U_n$, $V_n$, $P$, $Q$
and $n$ are mapped into $K$.

In the double-root case the hypotheses give $P = 2 \alpha$ and $Q = \alpha^2$.

Proves `Wanted` entry `lucas_binet_formulas`.

Source: Christian Ballot, "A Further Generalization of a Congruence of
Wolstenholme", Journal of Integer Sequences 15 (2012), Article 12.8.6,
sequence definitions and formulas at lines 274–289,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Ballot/ballot4.tex
complete-source SHA-256
`b96be332c67702b765cf4d73089ecb09c1e544c95afec737b8ff1445e4bffa17`;
normalized lines 274–289 SHA-256
`a1f6755e5072c434c537d1e8c874715fad642cdc2f3ecae191f676022d222a5e`;
normalized formula lines 283–289 SHA-256
`955c225b2d2be3f81e25044e2179816a66f1923c22b4b40bf21c9cdef276e0c9`.
-/
theorem lucas_binet_formulas
    {K : Type*} [Field K] [CharZero K]
    (params : LucasSequenceParams) (alpha beta : K)
    (hsum : alpha + beta = (params.p : K))
    (hprod : alpha * beta = (params.q : K)) :
    (alpha ≠ beta → ∀ n : ℕ,
      (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
      (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
      (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
      (lucasV params n : K) = 2 * alpha ^ n) :=
  lucas_binet_formulas_of_field params alpha beta hsum hprod

end

end MetaMathlibExt
