/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ulam's three-prime closure process (Erdős Problem 471)

Erdős Problem 471 (Ulam): starting from a finite set of primes `Q₀`, let `Qᵢ₊₁` be `Qᵢ` together
with every prime that is a sum of three distinct elements of `Qᵢ`. Is there `Q₀` for which the `Qᵢ`
become arbitrarily large?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.UlamThreePrimeSumClosureErdosProblem471Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #471, https://www.erdosproblems.com/471 (status
PROVED). UnsolvedMath record UM-30006886 (`EP-471`), dataset ulamai/UnsolvedMath v1.8.0.

`Qᵢ = ulamStep^[i] Q₀`; "arbitrarily large" is unbounded cardinality. Ulam's specific question about
`Q₀ = {3, 5, 7, 11}` appears in the page commentary, not in the recorded problem.
-/

/-- One step of Ulam's process: `Q` together with every prime that is the sum of three distinct
elements of `Q`. -/
def ulamStep (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ ((Q ×ˢ Q ×ˢ Q).filter fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
    (t.1 + t.2.1 + t.2.2).Prime).image fun t => t.1 + t.2.1 + t.2.2

/-- Erdős Problem 471: some finite set `Q₀` of primes has `Qᵢ = ulamStep^[i] Q₀` of unbounded
size. -/
def threePrimeSumClosureUnbounded : Prop :=
  ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) ∧ ∀ M : ℕ, ∃ i : ℕ, M ≤ (ulamStep^[i] Q).card

/--
Resolved true: by Vinogradov's three-primes theorem there is `N` such that every prime `> N` is a
sum of three distinct smaller primes; with `Q₀` the primes up to `N`, every prime eventually enters
some `Qᵢ` (Mrazović and Kovač, and Alon, on erdosproblems.com/471). Source: T. F. Bloom, Erdős
Problems, Problem #471, https://www.erdosproblems.com/471 (status PROVED); resolution: Observation
of R. Mrazović and V. Kovač, and independently N. Alon, recorded on erdosproblems.com/471, from
Vinogradov's theorem that every large odd integer is a sum of three distinct primes,
erdosproblems.com/471: there is N such that every prime > N is a sum of three distinct smaller
primes; take Q₀ = primes ≤ N, https://www.erdosproblems.com/471.
-/
public theorem_wanted threePrimeSumClosureUnbounded_holds : threePrimeSumClosureUnbounded

end MathlibExt.NumberTheory.UlamThreePrimeSumClosureErdosProblem471Wanted
