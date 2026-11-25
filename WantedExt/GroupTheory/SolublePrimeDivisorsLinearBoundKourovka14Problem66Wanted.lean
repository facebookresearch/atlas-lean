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

/-- **Linear bound on the prime divisors of a finite soluble group (Kourovka 14.66).** The
statement, posed by A. Moretó, that there are natural numbers $a$ and $b$ such that for every
finite soluble group $G$ and every natural number $m$, if the order of every element of $G$ has at
most $m$ distinct prime divisors, then $|G|$ has at most $am + b$ distinct prime divisors.

Equivalently, $|\pi(G)| \le a\,\nu(G) + b$ for every finite soluble group $G$, where $\pi(G)$ is
the set of primes dividing $|G|$ and $\nu(G)$ is the largest number of distinct primes dividing
the order of a single element of $G$. -/
def solublePrimeCountLinearInElementPrimeCount : Prop :=
  ∃ a b : ℕ, ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → ∀ m : ℕ,
    (∀ g : G, (orderOf g).primeFactors.card ≤ m) → (Nat.card G).primeFactors.card ≤ a * m + b

/--
**Finite soluble groups satisfy a linear prime-divisor bound.** There are natural numbers $a$ and
$b$ such that for every finite soluble group $G$ and every natural number $m$, if the order of
every element of $G$ has at most $m$ distinct prime divisors, then $|G|$ has at most $am + b$
distinct prime divisors. That is, Kourovka Problem 14.66 has a positive answer.

Resolved true: the Kourovka Archive answers 14.66 "Yes, it does", citing Keller.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.66 (A. Moretó); resolution: T. M.
Keller, J. Algebra 178 (1995), no. 2, 643-652, Kourovka Archive, Problem 14.66 (answer: Yes, it
does).
-/
public theorem_wanted solublePrimeCountLinearInElementPrimeCount_holds :
    solublePrimeCountLinearInElementPrimeCount

end MathlibExt.GroupTheory.SolublePrimeDivisorsLinearBoundKourovka14Problem66Wanted
