/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derivatives of entire functions vanishing on discrete sets (Erdős Problem 229)

Erdős Problem 229: let `(S_n)_{n ≥ 1}` be sets of complex numbers without finite limit points. Is
there a transcendental entire `f` with integers `k_n ≥ 0` such that `f^{(k_n)}(z) = 0` for all `z ∈
S_n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.DerivedSet

@[expose] public section

namespace MathlibExt.Analysis.EntireDerivativesVanishingOnSetsErdosProblem229Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #229, https://www.erdosproblems.com/229 (status PROVED
(LEAN)). UnsolvedMath record UM-30006781 (`EP-229`), dataset ulamai/UnsolvedMath v1.8.0.

No finite limit point is `derivedSet (S n) = ∅`; transcendental means not a polynomial function (for
a polynomial, large `k_n` make the question trivial). The sequence is indexed by `n ∈ ℕ`. Compared
with the formal-conjectures statement `ErdosProblems/229.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 229: for every sequence `(S_n)` of subsets of `ℂ` without finite limit points
there are a transcendental (non-polynomial) entire function `f` and integers `k_n ≥ 0` with
`f^{(k_n)} = 0` on `S_n` for every `n`. -/
def entireDerivativesVanishOnDiscreteSets : Prop :=
  ∀ S : ℕ → Set ℂ, (∀ n, derivedSet (S n) = ∅) →
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) ∧
      ∀ n, ∃ k : ℕ, ∀ z ∈ S n, iteratedDeriv k f z = 0

/--
Resolved true: Barth and Schneider (Theorem 1) proved that for any sequence `(S_k)` of subsets of
`ℂ` without finite limit points there are positive integers `n_k` and a transcendental entire
function `f` with `f^{(n_k)}(z) = 0` for `z ∈ S_k`; erdosproblems.com/229 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #229, https://www.erdosproblems.com/229 (status
PROVED (LEAN)); resolution: K. F. Barth and W. J. Schneider, On a problem of Erdős concerning the
zeros of the derivatives of an entire function, Proc. Amer. Math. Soc. 32 (1972), 229-232, Theorem
1: for any sequence of sets without finite limit points there are positive integers n_k and a
transcendental entire f with f^{(n_k)} = 0 on S_k,
https://doi.org/10.1090/S0002-9939-1972-0293089-7.
-/
public theorem_wanted entireDerivativesVanishOnDiscreteSets_holds :
    entireDerivativesVanishOnDiscreteSets

end MathlibExt.Analysis.EntireDerivativesVanishingOnSetsErdosProblem229Wanted
