/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largeness of the Maillet / Kronecker / de Polignac sets — wishlist
This file records four largeness theorems for the prime-difference sets as
`theorem_wanted` declarations.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open scoped BigOperators

namespace MathlibExt.NumberTheory.MailletLargenessWanted

/-- A Maillet number: an even number that is a difference of two primes.
Local copy of `OpenConjectures.NumberTheory.MailletConjecture.IsMailletNumber`,
which `WantedExt` may not import. -/
def IsMailletNumber (n : ℕ) : Prop :=
  Even n ∧ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n + q = p

/-- A Kronecker number: an even number that is a difference of two primes
in infinitely many ways.
Local copy of
`OpenConjectures.NumberTheory.KroneckerPrimeDifferenceConjecture.IsKroneckerNumber`,
which `WantedExt` may not import. -/
def IsKroneckerNumber (n : ℕ) : Prop :=
  Even n ∧ Set.Infinite
    {x : ℕ × ℕ | Nat.Prime x.1 ∧ Nat.Prime x.2 ∧ n + x.2 = x.1}

/-- A de Polignac number: a number `m` such that `p_{n+1} - p_n = m` for
infinitely many `n`, where `p_n` is the `n`-th prime. -/
def IsDePolignacNumber (m : ℕ) : Prop :=
  Set.Infinite {n : ℕ |
    Nat.nth Nat.Prime (n + 1) = Nat.nth Nat.Prime n + m}

/-- An IP set: the set of all nonzero finite sums of distinct elements of
some infinite set `M` of positive naturals. Since every element of `M` is
positive, sums over nonempty finite subsets are automatically nonzero.

This is Banks' definition (arXiv:2403.10637, abstract): "For an infinite set
M of natural numbers, let FS(M) be the set of all nonzero finite sums of
distinct numbers in M. An IP set is any set of the form FS(M)." Requiring
`0 < m` loses nothing: removing `0` from `M` leaves `FS(M)` unchanged and `M`
infinite. Some authors call a set IP when it merely contains some `FS(M)`;
`banks_de_polignac_ip` says the same under that reading, because its
conclusion only grows with `A`, and if every element of `A ⊇ FS(M)` is even,
then so is every element of the IP set `FS(M)`. -/
def IsIPSet (A : Set ℕ) : Prop :=
  ∃ M : Set ℕ, Set.Infinite M ∧ (∀ m ∈ M, 0 < m) ∧
    A = {s | ∃ F : Finset ℕ, (∀ i ∈ F, i ∈ M) ∧ F.Nonempty ∧ s = ∑ i ∈ F, i}

/-- A `Δ*_r` set (Huang–Wu, Definition 1.5): a set `A` of naturals that meets
the positive difference set `Δ(S) = {b - a : a ∈ S, b ∈ S, b > a}` of every
`r`-element set `S` of naturals. Allowing `0 ∈ S` changes nothing, since
shifting `S` by one leaves `Δ(S)` unchanged. -/
def IsDeltaStar (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = r → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ b - a ∈ A

/--
Banks' theorem: every IP set of even natural numbers contains infinitely
many de Polignac numbers. In particular the de Polignac numbers meet every
IP set, i.e. they form an IP* set.

Source: William D. Banks, Consecutive primes and IP sets,
arXiv:2403.10637 (2024), abstract.
-/
public theorem_wanted banks_de_polignac_ip :
    ∀ A : Set ℕ, IsIPSet A → (∀ a ∈ A, Even a) →
      Set.Infinite {m | m ∈ A ∧ IsDePolignacNumber m}

/--
Huang–Wu theorem: the Kronecker numbers form a `Δ*_r` set for every
`r ≥ 721`, i.e. any `r ≥ 721` naturals contain two whose difference is a
Kronecker number. Huang and Wu present this as strengthening Pintz's theorem
that the Kronecker numbers are syndetic (their Theorem 1.4).

Their set `D` consists of the numbers that are a difference of two primes in
infinitely many ways. Every element of `D` is even (an odd difference of two
primes needs the prime `2`, so it has at most one representation), so `D` is
the set of positive Kronecker numbers; `IsKroneckerNumber` also admits `0`,
which no `Δ(S)` contains.

Source: Wen Huang and XiaoSheng Wu, On the set of the difference of primes,
Proc. Amer. Math. Soc. 145 (2017), no. 9, 3787–3793; arXiv:1505.00187,
Theorem 1.6, with `Δ*_r` from Definition 1.5. Restated as Theorem 1.2 of
Goswami–Huang–Wu (arXiv:2303.05767).
-/
public theorem_wanted huang_wu_kronecker_deltaStar :
    ∀ r : ℕ, 721 ≤ r → IsDeltaStar r {n | IsKroneckerNumber n}

/--
Goswami–Huang–Wu product theorem: there is a constant `k > 0` and a set
`D` of at most `720` Maillet numbers such that every positive multiple of
`k` is a product of a Kronecker number with a Maillet number in `D`.

The source proves the stronger computable version: `k` and `D` are
explicitly constructed (`k = 720! * m'` for the least suitable `m'`). The
Lean statement records the existential form.

Source: Sayan Goswami, Wen Huang, and XiaoSheng Wu, On the set of Kronecker
numbers, Bull. Aust. Math. Soc. 110 (2024), 262–270, Theorem 1.4
(arXiv:2303.05767).
-/
public theorem_wanted goswami_huang_wu_product :
    ∃ k : ℕ, 0 < k ∧ ∃ D : Finset ℕ, (∀ d ∈ D, IsMailletNumber d) ∧
      D.card ≤ 720 ∧ ∀ n : ℕ, 0 < n → ∃ d ∈ D, ∃ k' : ℕ,
        IsKroneckerNumber k' ∧ k * n = d * k'

/--
Goswami–Huang–Wu ratio theorem: every positive rational number can be
written as a ratio of two Kronecker numbers.

Source: Sayan Goswami, Wen Huang, and XiaoSheng Wu, On the set of Kronecker
numbers, Bull. Aust. Math. Soc. 110 (2024), 262–270, Theorem 1.5
(arXiv:2303.05767).
-/
public theorem_wanted goswami_huang_wu_ratio :
    ∀ q : ℚ, 0 < q → ∃ k₁ k₂ : ℕ, IsKroneckerNumber k₁ ∧
      IsKroneckerNumber k₂ ∧ 0 < k₂ ∧ q = (k₁ : ℚ) / (k₂ : ℚ)

end MathlibExt.NumberTheory.MailletLargenessWanted
