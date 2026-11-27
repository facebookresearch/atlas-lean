/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.Data.Set.Density
public import Batteries.Util.ProofWanted

@[expose] public section

/-!
# Erdős Problem #851

Romanoff's theorem gives positive lower density for the integers of the form
`2 ^ k + p` with `p` prime. Moreover, for every `ε > 0` there is `r` such that
the integers of the form `2 ^ k + n` with `n` having at most `r` distinct prime
divisors have lower density at least `1 - ε`.
-/

namespace MathlibExt.NumberTheory.ErdosProblem851Wanted

/-- **Natural numbers with at most $r$ distinct prime factors.** For natural numbers $n$ and $r$,
$n$ has at most $r$ distinct prime factors when $n = 0$ or at most $r$ distinct primes divide $n$;
the number $0$ is counted as having no prime factors.

Source: EP-851 [Erdős Problems]. -/
def HasAtMostRPrimeFactors (n r : ℕ) : Prop :=
  n.primeFactors.card ≤ r

/-- **Sums of a power of two and a number with few prime factors.** For a natural number $r$, a
natural number $m$ is of this form when $m = 2^k + n$ for some natural numbers $k$ and $n$ such
that $n = 0$ or at most $r$ distinct primes divide $n$.

Source: EP-851 [Erdős Problems]. -/
def Representable (r m : ℕ) : Prop :=
  ∃ k n : ℕ, m = 2 ^ k + n ∧ HasAtMostRPrimeFactors n r

/-- **Sums of a power of two and a prime.** A natural number $m$ is of this form when
$m = 2^k + p$ for some natural number $k$ and some prime $p$.

Source: Romanoff's theorem in EP-851 [Erdős Problems]. -/
def PrimeRepresentable (m : ℕ) : Prop :=
  ∃ k p : ℕ, m = 2 ^ k + p ∧ p.Prime

/-- **Erdős Problem 851.** The proposition asserts two things. First, the set of natural numbers
of the form $2^k + p$, with $k$ a natural number and $p$ prime, has positive lower density
(Romanoff's theorem). Second, for every real number $\varepsilon > 0$ there is a natural number
$r$ such that the set of natural numbers of the form $2^k + n$, with $k$ and $n$ natural numbers
and with $n = 0$ or at most $r$ distinct primes dividing $n$, has lower density at least
$1 - \varepsilon$.

Source: EP-851 [Erdős Problems]. -/
noncomputable def Statement : Prop :=
  0 < Set.lowerDensity {m | PrimeRepresentable m} ∧
    ∀ (ε : ℝ), ε > 0 → ∃ r : ℕ, 1 - ε ≤ Set.lowerDensity {m | Representable r m}

/--
**Erdős Problem 851 is true.** The set of natural numbers of the form $2^k + p$, with $k$ a natural
number and $p$ prime, has positive lower density. Moreover, for every real number
$\varepsilon > 0$ there is a natural number $r$ such that the set of natural numbers of the form
$2^k + n$, with $k$ and $n$ natural numbers and with $n = 0$ or at most $r$ distinct primes dividing
$n$, has lower density at least $1 - \varepsilon$.

Romanoff proved the positive-density clause in 1934; Price and GPT-5.2 Pro proved the near-one
density statement affirmatively in 2026.

Source: Lean proof of Erdős Problem 851,
pinned revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos851.lean#L37;
Yuchen Ding and Wenguang Zhai, A generalization of the Romanoff theorem, arXiv:2401.15892v3
(2024), https://arxiv.org/abs/2401.15892v3. Moved from
`OpenConjectures/NumberTheory/ErdosProblem851`.
-/
public theorem_wanted Statement_holds : Statement

end MathlibExt.NumberTheory.ErdosProblem851Wanted
