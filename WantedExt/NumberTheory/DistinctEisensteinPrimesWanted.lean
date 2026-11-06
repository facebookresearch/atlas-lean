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
Eisenstein primes. Only these two self-contained
statements about rational primes `≡ -1 (mod 6)` are
formalized here; the paper's auxiliary Lemmas 1 and
Corollary 1 and its Theorem 1 are not stated, since
they refer to the paper's set `E` of Eisenstein
integers, its exceptional set `B`, and hypotheses on
the summand set `H` that are not part of the extracted
statements (see the source audit table).

Numerically checked: Lemma 2 (strict inequalities) for
`7 ≤ x ≤ 20000`, and Lemma 3 for `162 ≤ n ≤ 500`, where
`161` is indeed the largest nonrepresentable integer.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted

/-- **Breusch's theorem for primes of the form $6k - 1$.** For every natural number $x \ge 7$
there is a prime $p$ with $x < p < 2x$ and $p \equiv 5 \pmod 6$, that is, a prime of the form
$6k - 1$ strictly between $x$ and $2x$.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", Lemma 2 (citing Breusch). -/
theorem_wanted exists_prime_modEq_five_between (x : ℕ)
    (hx : 7 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p < 2 * x ∧ p % 6 = 5

/-- **Makowski's theorem on sums of distinct primes of the form $6k - 1$.** Every natural number
$n > 161$ is the sum of the elements of some finite set of primes $p$ with $p \equiv 5 \pmod 6$;
that is, $n$ is a sum of distinct primes of the form $6k - 1$.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", Lemma 3 (citing Makowski). -/
theorem_wanted eq_sum_distinct_primes_modEq_five (n : ℕ)
    (hn : 161 < n) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 6 = 5) ∧
      (∑ p ∈ S, p) = n

end MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted
