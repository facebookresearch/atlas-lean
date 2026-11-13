/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Divisors forming irreducible covering sets (Erdős Problem 1189)

Erdős Problem 1189: call a set of distinct integers `1 < n₁ < ⋯ < n_k` a covering set if there is
a choice of `a_i (mod n_i)` for `1 ≤ i ≤ k` such that every integer satisfies at least one of
these congruences. A set is an irreducible covering set if no proper subset is a covering set. How
many irreducible covering sets of size `k` are there? What is the minimum and maximum that `n_k`
can be? Determine or estimate `max ∑ 1/n_i`, where the maximum ranges over all irreducible
covering sets of size `k`. Are there infinitely many `n` such that the divisors of `n` (which are
`> 1`) form an irreducible covering set?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.CoveringSystem

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorIrreducibleCoveringSetErdosProblem1189Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1189, https://www.erdosproblems.com/1189 (status
OPEN). UnsolvedMath record UM-30007230 (`EP-1189`), dataset ulamai/UnsolvedMath v1.8.0.

A covering set is a finite set `S` of naturals `> 1` with residues `a n`, `n ∈ S`, such that the
classes `(a n, n)` form an `Int.IsCoveringSystem` (MathlibExt). The divisors `> 1` of `n` are
`n.divisors.erase 1`. Only the last question is stated; the other three ask for counts and
estimates with no conjectured value. formal-conjectures has no statement of this problem.
-/

/-- A finite set `S` of integers `n > 1` is a covering set if residues `a n (mod n)`, `n ∈ S`, can
be chosen so that every integer satisfies at least one of the congruences (the classes
`(a n, n)` form an `Int.IsCoveringSystem`). -/
def IsCoveringSet (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 1 < n) ∧ ∃ a : ℕ → ℤ, Int.IsCoveringSystem (S.image fun n => (a n, n))

/-- An irreducible covering set: a covering set no proper subset of which is a covering set. -/
def IsIrreducibleCoveringSet (S : Finset ℕ) : Prop :=
  IsCoveringSet S ∧ ∀ T ⊂ S, ¬ IsCoveringSet T

/-- The last question of Erdős Problem 1189: there are infinitely many `n` such that the divisors
of `n` that are `> 1` form an irreducible covering set. -/
def divisorsIrreducibleCoveringInfinitelyOften : Prop :=
  {n : ℕ | IsIrreducibleCoveringSet (n.divisors.erase 1)}.Infinite

/--
Resolved true: Sun proved that for every odd prime `p` the divisors `> 1` of `2^{p-1} p` form an
irreducible covering set, so there are infinitely many such `n`. Source: T. F. Bloom, Erdős
Problems, Problem #1189, https://www.erdosproblems.com/1189 (status OPEN); resolution: Z.-W. Sun,
On covering numbers, in Combinatorial Number Theory (B. Landman et al., eds.), de Gruyter, 2007,
443-453, abstract: 'In 1980 P. Erdős asked whether there are infinitely many positive integers n
such that among the subsets of D_n = {d ≥ 2 : d | n} only D_n can be the set of all the moduli in
a cover of Z with distinct moduli; we answer this question affirmatively'; erdosproblems.com/1189:
for any odd prime p the divisors (which are > 1) of 2^{p-1} p form an irreducible covering set,
'settling the final question', https://doi.org/10.1515/9783110925098.443.
-/
public theorem_wanted divisorsIrreducibleCoveringInfinitelyOften_holds :
    divisorsIrreducibleCoveringInfinitelyOften

end MathlibExt.NumberTheory.DivisorIrreducibleCoveringSetErdosProblem1189Wanted
