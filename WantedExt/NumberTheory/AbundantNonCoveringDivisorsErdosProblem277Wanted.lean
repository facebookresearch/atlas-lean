/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abundant numbers whose divisors carry no covering system (Erdős Problem 277)

Erdős Problem 277: is it true that for every `c` there is `n` with `σ(n) > c n` but no covering
system whose moduli are distinct divisors of `n` greater than `1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

namespace MathlibExt.NumberTheory.AbundantNonCoveringDivisorsErdosProblem277Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #277, https://www.erdosproblems.com/277 (status PROVED
(LEAN)). UnsolvedMath record UM-30006802 (`EP-277`), dataset ulamai/UnsolvedMath v1.8.0.

A covering system with distinct moduli among the divisors `d > 1` of `n` exists exactly when some
choice of one class `a d (mod d)` for every such `d` covers `ℤ` (extra congruences only help), so
the negation is stated for all choices `a`. `σ = ArithmeticFunction.sigma 1`. Compared with the
formal-conjectures statement `ErdosProblems/277.lean` (equivalent, via strict covering systems; no
code imported).
-/

/-- Erdős Problem 277: for every `c` there is `n` with `σ(n) > c n` such that no covering system
has distinct moduli that are divisors `d > 1` of `n`; equivalently, no choice of one residue class
`a d (mod d)` for every divisor `d > 1` of `n` covers `ℤ`. -/
def abundantNonCoveringNumbers : Prop :=
  ∀ c : ℝ, ∃ n : ℕ, c * n < (ArithmeticFunction.sigma 1 n : ℝ) ∧
    ∀ a : ℕ → ℤ, ∃ x : ℤ, ∀ d ∈ n.divisors, 1 < d → ¬ x ≡ a d [ZMOD d]

/--
Resolved true: Haight proved that `σ(n)/n` can be arbitrarily large while the divisors `d > 1` of
`n` support no covering system; Filaseta, Ford, Konyagin, Pomerance and Yu gave a stronger form.
erdosproblems.com/277 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#277, https://www.erdosproblems.com/277 (status PROVED (LEAN)); resolution: J. A. Haight, Covering
systems of congruences, a negative result, Mathematika (1979), 53-61, erdosproblems.com/277:
answered affirmatively by Haight; a stronger form is proved in Section 2 of Filaseta, Ford,
Konyagin, Pomerance and Yu, J. Amer. Math. Soc. (2007), 495-517, https://www.erdosproblems.com/277.
-/
public theorem_wanted abundantNonCoveringNumbers_holds : abundantNonCoveringNumbers

end MathlibExt.NumberTheory.AbundantNonCoveringDivisorsErdosProblem277Wanted
