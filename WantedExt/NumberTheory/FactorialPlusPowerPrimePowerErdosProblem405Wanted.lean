/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The equation (p - 1)! + a^(p-1) = p^k (Erdős Problem 405)

Erdős Problem 405: let `p` be an odd prime. Does `(p - 1)! + a^{p-1} = p^k` have only finitely many
solutions?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.FactorialPlusPowerPrimePowerErdosProblem405Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #405, https://www.erdosproblems.com/405 (status PROVED
(LEAN)). UnsolvedMath record UM-30006858 (`EP-405`), dataset ulamai/UnsolvedMath v1.8.0.

The statement counts all solutions `(a, k, p)` with `p` an odd prime; finiteness of this set implies
finiteness for each fixed `p`, so it is the stronger form, and it is what Brindza and Erdős proved:
their Theorem 2 bounds every solution in positive integers `a, k` and primes `p > 2` by an absolute
constant, and there is no solution with `a = 0` (`(p - 1)! > 1` is prime to `p`) or `k = 0` (the
left side exceeds `1`). (For `p = 2` there are infinitely many solutions.) Compared with the
formal-conjectures statement `ErdosProblems/405.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 405: the equation `(p - 1)! + a ^ (p - 1) = p ^ k`, with `p` an odd prime, has
only finitely many solutions `(a, k, p)`. -/
def finitelyManyFactorialPowerSolutions : Prop :=
  {(a, k, p) : ℕ × ℕ × ℕ | p.Prime ∧ Odd p ∧ Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k}.Finite

/--
Resolved true: Brindza and Erdős proved that there are only finitely many solutions, and Yu and Liu
showed that the only ones are `2! + 1² = 3`, `2! + 5² = 3³` and `4! + 1⁴ = 5²`;
erdosproblems.com/405 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#405, https://www.erdosproblems.com/405 (status PROVED (LEAN)); resolution: B. Brindza and P. Erdős,
On some Diophantine problems involving powers and factorials, J. Austral. Math. Soc. Ser. A (1991),
1-7; K. Yu and D. Liu, A complete resolution of a problem of Erdős and Graham, Rocky Mountain J.
Math. (1996), 1235-1244, Brindza-Erdős, Theorem 2: all solutions in positive integers a, k and
primes p > 2 are bounded by an effective absolute constant; Yu-Liu: the only ones are 2! + 1² = 3,
2! + 5² = 3³, 4! + 1⁴ = 5².
-/
public theorem_wanted finitelyManyFactorialPowerSolutions_holds :
    finitelyManyFactorialPowerSolutions

end MathlibExt.NumberTheory.FactorialPlusPowerPrimePowerErdosProblem405Wanted
