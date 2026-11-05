/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

private lemma tau_prime_pow {p : ℕ} (hp : Nat.Prime p) (j : ℕ) :
    (p ^ j).divisors.card = j + 1 := by
  rw [Nat.divisors_prime_pow hp j, Finset.card_map, Finset.card_range]

private lemma two_mul_sum_range_succ (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

private lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (i + 1)) ^ 2 = ∑ i ∈ Finset.range n, (i + 1) ^ 3 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h2 : 2 * ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) :=
      two_mul_sum_range_succ k
    nlinarith [ih, h2, Nat.zero_le k, sq_nonneg (∑ i ∈ Finset.range k, (i + 1)),
      sq_nonneg (k + 1 : ℕ)]

private noncomputable def tauCube : ArithmeticFunction ℕ :=
  { toFun := fun n => (n.divisors.card) ^ 3
    map_zero' := by simp }

private lemma tauCube_apply (n : ℕ) : tauCube n = (n.divisors.card) ^ 3 := rfl

private lemma tauCube_mul {m n : ℕ} (h : m.Coprime n) :
    tauCube (m * n) = tauCube m * tauCube n := by
  change ((m * n).divisors.card) ^ 3 = (m.divisors.card) ^ 3 * (n.divisors.card) ^ 3
  rw [Nat.Coprime.card_divisors_mul h]
  ring

private lemma tauCube_one : tauCube 1 = 1 := by
  change (Nat.divisors 1).card ^ 3 = 1
  simp

private lemma tauCube_isMult : tauCube.IsMultiplicative :=
  ⟨tauCube_one, fun h => tauCube_mul h⟩

private noncomputable def F : ArithmeticFunction ℕ :=
  ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta
private noncomputable def G : ArithmeticFunction ℕ :=
  tauCube * ArithmeticFunction.zeta

private lemma F_isMult : F.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    ArithmeticFunction.isMultiplicative_sigma ArithmeticFunction.isMultiplicative_zeta
private lemma G_isMult : G.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    tauCube_isMult ArithmeticFunction.isMultiplicative_zeta

private lemma F_apply (x : ℕ) : F x = ∑ i ∈ x.divisors, i.divisors.card := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℕ)
    (f := ArithmeticFunction.sigma 0) (x := x)
  simpa [F, ArithmeticFunction.sigma_zero_apply] using h

private lemma G_apply (x : ℕ) : G x = ∑ i ∈ x.divisors, (i.divisors.card) ^ 3 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℕ) (f := tauCube) (x := x)
  simpa [G, tauCube_apply] using h

private noncomputable def Fsq : ArithmeticFunction ℕ :=
  { toFun := fun n => (F n) ^ 2
    map_zero' := by simp }

private lemma Fsq_apply (n : ℕ) : Fsq n = (F n) ^ 2 := rfl

private lemma Fsq_isMult : Fsq.IsMultiplicative := by
  constructor
  · change (F 1) ^ 2 = 1
    have h1 : F 1 = 1 := F_isMult.1
    rw [h1, one_pow]
  · intro m n h
    change (F (m * n)) ^ 2 = (F m) ^ 2 * (F n) ^ 2
    rw [F_isMult.2 h]
    ring

private lemma prime_pow_eq {p i : ℕ} (hp : Nat.Prime p) : Fsq (p ^ i) = G (p ^ i) := by
  rw [Fsq_apply, F_apply, G_apply]
  rw [Nat.divisors_prime_pow hp i, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have e1 : (∑ x ∈ Finset.range (i + 1), ((p ^ x).divisors.card)) =
      ∑ x ∈ Finset.range (i + 1), (x + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [tau_prime_pow hp x]
  have e2 : (∑ x ∈ Finset.range (i + 1), (((p ^ x).divisors.card) ^ 3)) =
      ∑ x ∈ Finset.range (i + 1), (x + 1) ^ 3 := by
    apply Finset.sum_congr rfl
    intro x _
    rw [tau_prime_pow hp x]
  rw [e1, e2]
  have h := sum_cube_eq_sq_sum (i + 1)
  rw [h]

private lemma FG_eq : Fsq = G := by
  have h := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    Fsq Fsq_isMult G G_isMult).mpr (fun p i hp => prime_pow_eq hp)
  exact h

/-- **Liouville's divisor-function identity for all natural numbers.** For every natural number
$n$, writing $\tau(d)$ for the number of positive divisors of $d$,
$$\left(\sum_{d \mid n} \tau(d)\right)^2 = \sum_{d \mid n} \tau(d)^3,$$
where both sums run over the positive divisors $d$ of $n$. By convention the divisor set of $0$
is empty here, so for $n = 0$ both sides are $0$. -/
theorem liouville_divisor_function_identity_general (n : ℕ) :
    (∑ d ∈ n.divisors, d.divisors.card) ^ 2 =
      ∑ d ∈ n.divisors, (d.divisors.card) ^ 3 := by
  have h := congrArg (fun f => f n) FG_eq
  rw [Fsq_apply, F_apply, G_apply] at h
  exact h

set_option linter.unusedVariables false in
/-- **Liouville's divisor-function identity.** For every positive integer $n$, writing $\tau(d)$
for the number of positive divisors of $d$,
$$\left(\sum_{d \mid n} \tau(d)\right)^2 = \sum_{d \mid n} \tau(d)^3,$$
where both sums run over the positive divisors $d$ of $n$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, “Translations and Extensions of the
Nicomachean Identity,” Journal of Integer Sequences 27 (2024), lines 317–322,
`https://cs.uwaterloo.ca/journals/JIS/VOL27/Kim/kim8.tex` (full TeX SHA-256
`787b1d5e48f218f3b44166059063c4be564a15df0ed18d8793b2aed240aecb1f`; exact quoted
span SHA-256, including its terminal LF,
`5b7c9a7479bb8eb08ba025ed7f94848fd6abef52db394974d3dca55292110351`). Here
`d.divisors.card` is the source's divisor-count function.
It follows from `liouville_divisor_function_identity_general`; the hypothesis `hn` is unused
and keeps the source's shape (at `n = 0` both sides are `0`, since `Nat.divisors 0 = ∅`).
Proves `Wanted` entry `liouville_divisor_function_identity`.
-/
theorem liouville_divisor_function_identity
    (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, d.divisors.card) ^ 2 =
      ∑ d ∈ n.divisors, (d.divisors.card) ^ 3 := by
  exact liouville_divisor_function_identity_general n

end MetaMathlibExt
