/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Representations n = 2^a + 3^b + 2^c 3^d (Erdős Problem 407)

Erdős Problem 407: let `w(n)` count the solutions of `n = 2^a + 3^b + 2^c 3^d` with integers `a, b,
c, d ≥ 0`. Is `w(n)` bounded by an absolute constant?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.NumberTheory.TwoThreePowerRepresentationsErdosProblem407Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #407, https://www.erdosproblems.com/407 (status
PROVED). UnsolvedMath record UM-30006859 (`EP-407`), dataset ulamai/UnsolvedMath v1.8.0.

Solutions are ordered quadruples `(a, b, c, d)`. Boundedness is stated as "every finite set of
solutions has at most `C` elements", which also rules out an infinite solution set (each set of
solutions is in fact finite). Compared with the formal-conjectures statement
`ErdosProblems/407.lean` (equivalent; there `w(n)` is an `ncard`; no code imported).
-/

/-- `(a, b, c, d)` solves `n = 2 ^ a + 3 ^ b + 2 ^ c * 3 ^ d`. -/
def IsTwoThreeRepresentation (n : ℕ) (x : ℕ × ℕ × ℕ × ℕ) : Prop :=
  2 ^ x.1 + 3 ^ x.2.1 + 2 ^ x.2.2.1 * 3 ^ x.2.2.2 = n

/-- Erdős Problem 407: the number `w(n)` of solutions `(a, b, c, d)` of
`n = 2^a + 3^b + 2^c 3^d` is bounded by an absolute constant: every finite set of solutions has at
most `C` elements. -/
def twoThreeRepresentationCountBounded : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∀ S : Finset (ℕ × ℕ × ℕ × ℕ), (∀ x ∈ S, IsTwoThreeRepresentation n x) →
    S.card ≤ C

/--
Resolved true: Evertse, Győry, Stewart and Tijdeman proved Newman's conjecture that `w(n)` is
bounded, from finiteness results for `S`-unit equations; Bajpai and Bennett made it effective (at
most 9 distinct sets `{2^a, 3^b, 2^c 3^d}` for every `n`). erdosproblems.com/407 lists the problem
as proved. Source: T. F. Bloom, Erdős Problems, Problem #407, https://www.erdosproblems.com/407
(status PROVED); resolution: J.-H. Evertse, K. Győry, C. L. Stewart and R. Tijdeman, S-unit
equations and their applications, in: New advances in transcendence theory (Durham, 1986) (1988),
110-174, Newman's conjecture: w(n) is bounded (erdosproblems.com/407).
-/
public theorem_wanted twoThreeRepresentationCountBounded_holds : twoThreeRepresentationCountBounded

end MathlibExt.NumberTheory.TwoThreePowerRepresentationsErdosProblem407Wanted
