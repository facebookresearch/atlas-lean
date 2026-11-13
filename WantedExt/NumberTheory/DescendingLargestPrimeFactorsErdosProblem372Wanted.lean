/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three consecutive integers with descending largest prime factors (Erdős Problem 372)

Erdős Problem 372: with `P(n)` the largest prime factor of `n`, there are infinitely many `n` with
`P(n) > P(n + 1) > P(n + 2)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.DescendingLargestPrimeFactorsErdosProblem372Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #372, https://www.erdosproblems.com/372 (status
PROVED). UnsolvedMath record UM-30006843 (`EP-372`), dataset ulamai/UnsolvedMath v1.8.0.

`P(n)` is written `n.primeFactors.sup id`, the maximum of `n.primeFactors` (`0` for `n ≤ 1`).
Compared with the formal-conjectures statement `ErdosProblems/372.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 372: there are infinitely many `n` with `P(n) > P(n + 1) > P(n + 2)`. -/
def infinitelyManyDescendingLargestPrimeFactors : Prop :=
  {n : ℕ | (n + 1).primeFactors.sup id < n.primeFactors.sup id ∧
    (n + 2).primeFactors.sup id < (n + 1).primeFactors.sup id}.Infinite

/--
Resolved true: Balog proved that `P(n) > P(n + 1) > P(n + 2)` for `≫ √x` integers `n ≤ x` for all
large `x`, answering the conjecture of Erdős and Pomerance; erdosproblems.com/372 lists the problem
as proved. Source: T. F. Bloom, Erdős Problems, Problem #372, https://www.erdosproblems.com/372
(status PROVED); resolution: A. Balog, On triplets with descending largest prime factors, Studia
Sci. Math. Hungar. (2001), 45-50, the inequalities hold for ≫ √x integers n ≤ x for all large x
(erdosproblems.com/372).
-/
public theorem_wanted infinitelyManyDescendingLargestPrimeFactors_holds :
    infinitelyManyDescendingLargestPrimeFactors

end MathlibExt.NumberTheory.DescendingLargestPrimeFactorsErdosProblem372Wanted
