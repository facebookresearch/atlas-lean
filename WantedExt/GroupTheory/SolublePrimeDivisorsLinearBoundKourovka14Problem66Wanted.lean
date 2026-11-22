/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Prime divisors of soluble groups and of element orders (Kourovka Notebook Problem 14.66)

Kourovka Notebook, Archive of Solved Problems, Problem 14.66 (A. Moretó): for a finite soluble group
`G` let `π(G)` be the set of primes dividing `|G|` and `ν(G)` the largest number of primes dividing
the order of one element. Is `|π(G)|` bounded linearly in `ν(G)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SolublePrimeDivisorsLinearBoundKourovka14Problem66Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.66 (A.
Moretó). UnsolvedMath record UM-00701051 (`KOU-14.66`), dataset ulamai/UnsolvedMath v1.8.0.

A linear bound is `|π(G)| ≤ a ν(G) + b` with absolute constants `a`, `b`; it is stated with any `m`
bounding the number of prime divisors of every element order, which is equivalent.
-/

/-- Kourovka 14.66 (A. Moretó): there are constants `a`, `b` such that every finite soluble group
`G` satisfies `|π(G)| ≤ a ν(G) + b`, where `ν(G)` is the largest number of distinct primes dividing
the order of a single element (stated with any `m ≥ ν(G)`). -/
def solublePrimeCountLinearInElementPrimeCount : Prop :=
  ∃ a b : ℕ, ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ∀ m : ℕ,
    (∀ g : G, (orderOf g).primeFactors.card ≤ m) → (Nat.card G).primeFactors.card ≤ a * m + b

/--
Resolved true: the Kourovka Archive answers 14.66 "Yes, it does", citing Keller: `|π(G)| ≤ a ν(G) +
b` for absolute constants `a`, `b` and every finite soluble `G`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.66 (A. Moretó); resolution: T. M.
Keller, J. Algebra 178 (1995), no. 2, 643-652, Kourovka Archive, Problem 14.66 (answer: Yes, it
does).
-/
public theorem_wanted solublePrimeCountLinearInElementPrimeCount_holds :
    solublePrimeCountLinearInElementPrimeCount

end MathlibExt.GroupTheory.SolublePrimeDivisorsLinearBoundKourovka14Problem66Wanted
