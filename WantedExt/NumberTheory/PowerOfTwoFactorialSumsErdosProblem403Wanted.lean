/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Powers of two that are sums of distinct factorials (Erdős Problem 403)

Erdős Problem 403: does `2^m = a₁! + ⋯ + a_k!` with `a₁ < a₂ < ⋯ < a_k` have only finitely many
solutions?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.PowerOfTwoFactorialSumsErdosProblem403Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #403, https://www.erdosproblems.com/403 (status PROVED
(LEAN)). UnsolvedMath record UM-30006857 (`EP-403`), dataset ulamai/UnsolvedMath v1.8.0.

A solution is a pair `(m, {a₁, …, a_k})` with positive `aᵢ` (allowing `aᵢ = 0` would only add the
finitely many variants with `0! = 1! = 1`). Compared with the formal-conjectures statement
`ErdosProblems/403.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 403: `2^m = a₁! + ⋯ + a_k!` with `1 ≤ a₁ < ⋯ < a_k` has only finitely many
solutions `(m, {a₁, …, a_k})`. -/
def finitelyManyPowerOfTwoFactorialSums : Prop :=
  {p : ℕ × Finset ℕ | (∀ a ∈ p.2, 0 < a) ∧ 2 ^ p.1 = ∑ a ∈ p.2, Nat.factorial a}.Finite

/--
Resolved true: Frankl and Lin independently showed that there are only finitely many solutions, the
largest being `2^7 = 2! + 3! + 5!`; erdosproblems.com/403 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #403, https://www.erdosproblems.com/403 (status PROVED (LEAN));
resolution: S. Lin, On two problems of Erdős concerning sums of distinct factorials, Bell
Laboratories internal memorandum; P. Frankl (independently), only finitely many solutions, the
largest being 2^7 = 2! + 3! + 5! (erdosproblems.com/403).
-/
public theorem_wanted finitelyManyPowerOfTwoFactorialSums_holds :
    finitelyManyPowerOfTwoFactorialSums

end MathlibExt.NumberTheory.PowerOfTwoFactorialSumsErdosProblem403Wanted
