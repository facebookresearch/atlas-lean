/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Terms of the square of a sparse polynomial (Erdős Problem 485)

Erdős Problem 485: let `f(k)` be the least number of nonzero terms of `P(x) ^ 2` over `P ∈ ℚ[x]`
with exactly `k` nonzero terms. Does `f(k) → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.SquareOfSparsePolynomialErdosProblem485Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #485, https://www.erdosproblems.com/485 (status
PROVED). UnsolvedMath record UM-30006895 (`EP-485`), dataset ulamai/UnsolvedMath v1.8.0.

`f` is not defined: `f(k) → ∞` is unfolded as "for every `M` there is `K` such that every `P` with
at least `K` nonzero terms has `P ^ 2` with at least `M` nonzero terms", which is equivalent.
Compared with the formal-conjectures statement `ErdosProblems/485.lean` (equivalent; it defines `f`
by `sInf`; no code imported).
-/

/-- Erdős Problem 485: `f(k) → ∞`, where `f(k)` is the least number of nonzero terms of `P ^ 2`
over `P ∈ ℚ[x]` with exactly `k` nonzero terms. Unfolded: for every `M` there is `K` such that the
square of every rational polynomial with at least `K` nonzero terms has at least `M` nonzero
terms. -/
def squareTermCountTendsToInfinity : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ P : Polynomial ℚ, K ≤ P.support.card → M ≤ (P ^ 2).support.card

/--
Resolved true: Schinzel proved `f(k) > log log k / log 2` (for coefficients in any field of
characteristic `0` or large characteristic); Schinzel and Zannier improved this to `f(k) ≫ log k`.
Source: T. F. Bloom, Erdős Problems, Problem #485, https://www.erdosproblems.com/485 (status
PROVED); resolution: A. Schinzel, On the number of terms of a power of a polynomial, Acta Arith.
(1987), 55-70, erdosproblems.com/485: Schinzel proved f(k) > log log k / log 2; Schinzel and Zannier
improved this to f(k) ≫ log k, https://www.erdosproblems.com/485.
-/
public theorem_wanted squareTermCountTendsToInfinity_holds : squareTermCountTendsToInfinity

end MathlibExt.NumberTheory.SquareOfSparsePolynomialErdosProblem485Wanted
