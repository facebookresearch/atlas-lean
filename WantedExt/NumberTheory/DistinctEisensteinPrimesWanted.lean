/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of distinct Eisenstein primes: the rational-prime lemmas

Two classical lemmas cited in Elchin Hasanalizade,
"Sums of Distinct Eisenstein Primes", *INTEGERS* 24
(2024), Article A57
(<https://math.colgate.edu/~integers/vol24.html>), where
they are Lemmas 2 (Breusch) and 3 (Makowski) and are the
inputs to the paper's main theorem on sums of distinct
Eisenstein primes. From the journal PDF, Lemma 1, Corollary 1 and
Theorem 1 are stated too: elements `a + bω` of
`E = {a + bω : a, b ≥ 0}` are pairs `(a, b) : ℕ × ℕ`,
sums of distinct elements are sums over a `Finset`, and
"prime in `E`" is the paper's classification into the
types I-III (`IsEisensteinPrimeInE`).

Numerically checked: Lemma 2 (strict inequalities) for
`7 ≤ x ≤ 20000`, Lemma 3 for `162 ≤ n ≤ 500`, where
`161` is indeed the largest nonrepresentable integer,
and Theorem 1 for `a, b ≤ 110`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted

/-- **Lemma 2** (Breusch): if `x ≥ 7`, then between `x`
and `2x` there is at least one prime of the form
`6k - 1`.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", Lemma 2 (citing Breusch). -/
theorem_wanted exists_prime_modEq_five_between (x : ℕ)
    (hx : 7 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5

/-- **Lemma 3** (Makowski): every integer greater than
`161` is the sum of distinct primes of the form
`6k - 1`.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", Lemma 3 (citing Makowski). -/
theorem_wanted eq_sum_distinct_primes_modEq_five (n : ℕ)
    (hn : 161 < n) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 6 = 5) ∧
      (∑ p ∈ S, p) = n

/-- **Lemma 1** (analogue of Kløve's lemma): let `H ⊆ E`
contain the distinct positive integers `x₁, x₂, …` with
`x_{n+1} ≤ 2 x_n`. If, for fixed `b`, every `m + bω` with
`a < m ≤ a + x₁` is a sum of distinct elements of
`H \ X`, then every `m + bω` with `m > a` is a sum of
distinct elements of `H`. The sequence is indexed from
`0` (`x 0 = x₁`).

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Lemma 1. -/
theorem_wanted sum_distinct_of_doubling_seq_real
    (H : Set (ℕ × ℕ)) (x : ℕ → ℕ) (hinj : Function.Injective x)
    (hpos : ∀ n, 0 < x n) (hdouble : ∀ n, x (n + 1) ≤ 2 * x n)
    (hxH : ∀ n, (x n, 0) ∈ H) (a b : ℕ)
    (hbase : ∀ m, a < m → m ≤ a + x 0 →
      ∃ S : Finset (ℕ × ℕ), (↑S ⊆ H \ Set.range (fun n => (x n, 0))) ∧
        ∑ z ∈ S, z = (m, b)) :
    ∀ m, a < m → ∃ S : Finset (ℕ × ℕ), ↑S ⊆ H ∧ ∑ z ∈ S, z = (m, b)

/-- **Corollary 1**: the same with the roles of the
coordinates exchanged: if `H ⊆ E` contains `y₁ω, y₂ω, …`
for distinct positive integers `y_n` with
`y_{n+1} ≤ 2 y_n`, and, for fixed `a`, every `a + mω`
with `b < m ≤ b + y₁` is a sum of distinct elements of
`H \ Y`, then so is every `a + mω` with `m > b`, as a
sum of distinct elements of `H`.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Corollary 1. -/
theorem_wanted sum_distinct_of_doubling_seq_omega
    (H : Set (ℕ × ℕ)) (y : ℕ → ℕ) (hinj : Function.Injective y)
    (hpos : ∀ n, 0 < y n) (hdouble : ∀ n, y (n + 1) ≤ 2 * y n)
    (hyH : ∀ n, (0, y n) ∈ H) (a b : ℕ)
    (hbase : ∀ m, b < m → m ≤ b + y 0 →
      ∃ S : Finset (ℕ × ℕ), (↑S ⊆ H \ Set.range (fun n => (0, y n))) ∧
        ∑ z ∈ S, z = (a, m)) :
    ∀ m, b < m → ∃ S : Finset (ℕ × ℕ), ↑S ⊆ H ∧ ∑ z ∈ S, z = (a, m)

/-- The primes of `E` in the paper's classification,
writing `a + bω` as `(a, b)`: type I, `b = 0` and `a` a
rational prime `≡ 2 (mod 3)`; type II, `a = 0` and `b` a
rational prime `≡ 2 (mod 3)`; type III, `a, b > 0` and
the norm `a² - ab + b²` prime.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Section 2. -/
def IsEisensteinPrimeInE (z : ℕ × ℕ) : Prop :=
  (z.2 = 0 ∧ z.1.Prime ∧ z.1 % 3 = 2) ∨ (z.1 = 0 ∧ z.2.Prime ∧ z.2 % 3 = 2) ∨
    (0 < z.1 ∧ 0 < z.2 ∧ (z.1 ^ 2 + z.2 ^ 2 - z.1 * z.2).Prime)

/-- Membership in the paper's classification of primes of `E` is decidable.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Section 2. -/
instance : DecidablePred IsEisensteinPrimeInE := fun _ => by
  unfold IsEisensteinPrimeInE; infer_instance

/-- Small cases: `2`, `5ω` and `2 + ω` (norm `3`) are
primes of `E`; `3` and `1 + ω` (a unit) are not.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Sections 2 and 3. -/
theorem isEisensteinPrimeInE_small :
    IsEisensteinPrimeInE (2, 0) ∧ IsEisensteinPrimeInE (0, 5) ∧
      IsEisensteinPrimeInE (2, 1) ∧ ¬ IsEisensteinPrimeInE (3, 0) ∧
      ¬ IsEisensteinPrimeInE (1, 1) := by
  decide

/-- The paper's exceptional set
`B = A ∪ A^* ∪ {1 + ω, 2 + 2ω, 2 + 4ω, 4 + 2ω}` with
`A = {1, 3, 4, 6, 8, 9, 10, 12, 14, 15, 20, 21, 26, 27,
32, 37, 38, 44, 50, 67, 79}` and `A^* = {aω : a ∈ A}`.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Section 1. -/
def eisensteinExceptionalSet : Finset (ℕ × ℕ) :=
  let A : Finset ℕ := {1, 3, 4, 6, 8, 9, 10, 12, 14, 15, 20, 21, 26, 27, 32, 37, 38,
    44, 50, 67, 79}
  A.image (fun a => (a, 0)) ∪ A.image (fun a => (0, a)) ∪ {(1, 1), (2, 2), (2, 4), (4, 2)}

/-- **Theorem 1**: every element of `E \ B` is a sum
(empty sum allowed) of distinct primes of `E`.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", INTEGERS 24 (2024), Article A57,
Theorem 1. -/
theorem_wanted exists_sum_distinct_eisensteinPrimes (z : ℕ × ℕ)
    (hz : z ∉ eisensteinExceptionalSet) :
    ∃ S : Finset (ℕ × ℕ), (∀ w ∈ S, IsEisensteinPrimeInE w) ∧ ∑ w ∈ S, w = z

end MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted
