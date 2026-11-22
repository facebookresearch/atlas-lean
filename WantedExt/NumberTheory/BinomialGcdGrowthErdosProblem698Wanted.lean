/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Common divisors of binomial coefficients (Erdős Problem 698)

Erdős Problem 698: is there some `h(n) → ∞` such that for all `2 ≤ i < j ≤ n / 2`, `gcd(C(n, i),
C(n, j)) ≥ h(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.BinomialGcdGrowthErdosProblem698Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #698, https://www.erdosproblems.com/698 (status PROVED
(LEAN)). UnsolvedMath record UM-30006983 (`EP-698`), dataset ulamai/UnsolvedMath v1.8.0.

`j ≤ n / 2` is `2 j ≤ n` (equivalent for integers); `h : ℕ → ℕ`. Compared with the
formal-conjectures statement `ErdosProblems/698.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 698: there is `h(n) → ∞` with `gcd(C(n, i), C(n, j)) ≥ h(n)` for all
`2 ≤ i < j ≤ n / 2`. -/
def binomialGcdLowerBoundTendsToInfinity : Prop :=
  ∃ h : ℕ → ℕ, Filter.Tendsto h Filter.atTop Filter.atTop ∧
    ∀ n i j : ℕ, 2 ≤ i → i < j → 2 * j ≤ n → h n ≤ Nat.gcd (n.choose i) (n.choose j)

/--
Resolved true: Bergman proved `gcd(C(n, i), C(n, j)) ≫ n^{1/2} 2^i / i^{3/2}` for all `2 ≤ i < j ≤ n
/ 2` with an absolute implied constant, a lower bound tending to infinity with `n`;
erdosproblems.com/698 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#698, https://www.erdosproblems.com/698 (status PROVED (LEAN)); resolution: G. M. Bergman, On common
divisors of multinomial coefficients, Bull. Aust. Math. Soc. 83 (2011), 138-157, §2 (abstract: a
lower bound on the common divisor tending to infinity, as Erdős and Szekeres suggested);
erdosproblems.com/698: gcd(C(n, i), C(n, j)) ≫ n^{1/2} 2^i / i^{3/2} for all 2 ≤ i < j ≤ n/2, with
an absolute implied constant, https://doi.org/10.1017/S0004972710001723.
-/
public theorem_wanted binomialGcdLowerBoundTendsToInfinity_holds :
    binomialGcdLowerBoundTendsToInfinity

end MathlibExt.NumberTheory.BinomialGcdGrowthErdosProblem698Wanted
