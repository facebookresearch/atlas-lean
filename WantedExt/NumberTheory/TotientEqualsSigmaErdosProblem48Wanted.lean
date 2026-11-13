/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Common values of the totient and divisor-sum functions (Erdős Problem 48)

Erdős Problem 48: are there infinitely many integers `n, m` with `φ(n) = σ(m)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

namespace MathlibExt.NumberTheory.TotientEqualsSigmaErdosProblem48Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #48, https://www.erdosproblems.com/48 (status PROVED
(LEAN)). UnsolvedMath record UM-30006697 (`EP-48`), dataset ulamai/UnsolvedMath v1.8.0.

Read as infinitely many pairs of positive integers `(n, m)`; this is equivalent to infinitely many
common values, since each value of `φ` is taken finitely often. Compared with the formal-conjectures
statement `ErdosProblems/48.lean` (the same up to the positivity of n and m; no code imported).
-/

/-- Erdős Problem 48: there are infinitely many pairs of positive integers `(n, m)` with
`φ(n) = σ(m)`. -/
def totientEqSigmaInfinite : Prop :=
  {nm : ℕ × ℕ | 0 < nm.1 ∧ 0 < nm.2 ∧ nm.1.totient = ArithmeticFunction.sigma 1 nm.2}.Infinite

/--
Resolved true: Ford, Luca and Pomerance proved that at least `exp((log log x) ^ c)` integers `a ≤ x`
are of the form `a = φ(n) = σ(m)`, for an absolute `c > 0`. Source: T. F. Bloom, Erdős Problems,
Problem #48, https://www.erdosproblems.com/48 (status PROVED (LEAN)); resolution: K. Ford, F. Luca
and C. Pomerance, Common values of the arithmetic functions φ and σ, Bull. Lond. Math. Soc. (2010),
478-488, erdosproblems.com/48: at least exp((log log x)^c) values a ≤ x with a = φ(n) = σ(m),
https://www.erdosproblems.com/48.
-/
public theorem_wanted totientEqSigmaInfinite_holds : totientEqSigmaInfinite

end MathlibExt.NumberTheory.TotientEqualsSigmaErdosProblem48Wanted
