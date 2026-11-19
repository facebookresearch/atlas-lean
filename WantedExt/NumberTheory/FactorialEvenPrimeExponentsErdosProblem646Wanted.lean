/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Even prime exponents in `n!` (Erdős Problem 646)

Erdős Problem 646 (Erdős and Graham): let `p₁, …, p_k` be distinct primes. Are there infinitely many
`n` such that `n!` is divisible by an even power of each of the `p_i`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.FactorialEvenPrimeExponentsErdosProblem646Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #646, https://www.erdosproblems.com/646 (status PROVED
(LEAN)). UnsolvedMath record UM-30006966 (`EP-646`), dataset ulamai/UnsolvedMath v1.8.0.

'Divisible by an even power of `p`' means that the exact power of `p` dividing `n!` is even
(`padicValNat p n!` even); the primes form a finite set. Compared with the formal-conjectures
statement `ErdosProblems/646.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 646 (Erdős and Graham): for any finite set `S` of primes there are infinitely
many `n` such that every `p ∈ S` divides `n!` to an even power. -/
def factorialEvenExponentsInfinite : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    {n : ℕ | ∀ p ∈ S, Even (padicValNat p n.factorial)}.Infinite

/--
Resolved true: Berend proved that for any finite set of primes the `n` for which every exponent
`v_p(n!)` is even form an infinite set with bounded gaps; erdosproblems.com/646 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #646, https://www.erdosproblems.com/646 (status
PROVED (LEAN)); resolution: D. Berend, On the parity of exponents in the factorization of n!, J.
Number Theory (1997), 13-19, erdosproblems.com/646: the answer is yes, proved by Berend, who further
proved that the sequence of such n has bounded gaps, https://www.erdosproblems.com/646.
-/
public theorem_wanted factorialEvenExponentsInfinite_holds : factorialEvenExponentsInfinite

end MathlibExt.NumberTheory.FactorialEvenPrimeExponentsErdosProblem646Wanted
