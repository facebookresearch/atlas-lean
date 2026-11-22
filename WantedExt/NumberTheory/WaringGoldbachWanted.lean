/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Waring–Goldbach theorem — wishlist
This file records Hua's theorem on the Waring–Goldbach problem as a
`theorem_wanted` declaration.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.WaringGoldbachWanted

/--
A consequence of Hua's theorem on the Waring–Goldbach problem: for every
`k ≥ 1` there are constants `s` and `N` such that every `n ≥ N` is a sum
of at most `s` `k`-th powers of primes.

Hua's theorem itself says every sufficiently large `n ≡ s (mod K(k))` is a
sum of exactly `s` `k`-th powers of primes, for `s ≥ 2 ^ k + 1` and a
constant `K(k)`; the statement here is the at-most-`s` corollary, obtained
by choosing the number of summands congruent to `n` modulo `K(k)`.

Source: L.-K. Hua, Some results in additive prime number theory,
Quart. J. Math. Oxford 9 (1938), 68–80; Hua, Additive theory of prime
numbers, AMS Translations of Mathematical Monographs 13 (1965).
-/
public theorem_wanted waring_goldbach (k : ℕ) (hk : 0 < k) :
    ∃ s N : ℕ, ∀ n : ℕ, N ≤ n → ∃ t : ℕ, t ≤ s ∧
      ∃ p : Fin t → ℕ, (∀ i, Nat.Prime (p i)) ∧ n = ∑ i, (p i) ^ k

end MathlibExt.NumberTheory.WaringGoldbachWanted
