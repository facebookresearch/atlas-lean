/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Entire functions preserving rationality (Erdős Problem 226)

Erdős Problem 226: is there an entire non-linear function `f` such that, for all `x ∈ ℝ`, `x` is
rational if and only if `f(x)` is?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

namespace MathlibExt.Analysis.EntireFunctionPreservingRationalsErdosProblem226Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #226, https://www.erdosproblems.com/226 (status PROVED
(LEAN)). UnsolvedMath record UM-30006778 (`EP-226`), dataset ulamai/UnsolvedMath v1.8.0.

Non-linear means not of the form `z ↦ a z + b`; `f(x)` is rational when it is the image of a
rational number in `ℂ`. Compared with the formal-conjectures statement `ErdosProblems/226.lean`
(there `f` is also real on `ℝ` and non-affine as a real function, which the Barth-Schneider function
also satisfies; no code imported).
-/

/-- Erdős Problem 226: there is an entire function `f`, not of the form `z ↦ a z + b`, such that
for every real `x`, `x` is rational if and only if `f(x)` is rational. -/
def nonlinearEntireRationalIff : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (¬ ∃ a b : ℂ, ∀ z, f z = a * z + b) ∧
    ∀ x : ℝ, x ∈ Set.range ((↑) : ℚ → ℝ) ↔ f x ∈ Set.range ((↑) : ℚ → ℂ)

/--
Resolved true: Barth and Schneider proved that for countable dense sets `A, B ⊆ ℝ` there is a
transcendental entire function `f` with `f(z) ∈ B` exactly when `z ∈ A`; `A = B = ℚ` answers the
question. erdosproblems.com/226 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #226, https://www.erdosproblems.com/226 (status PROVED (LEAN)); resolution: K. F. Barth and
W. J. Schneider, Entire functions mapping countable dense subsets of the reals onto each other
monotonically, J. London Math. Soc. (2) 2 (1970), 620-626, erdosproblems.com/226: for countable
dense A, B ⊆ ℝ there is a transcendental entire f with f(z) ∈ B if and only if z ∈ A,
https://doi.org/10.1112/jlms/2.part_4.620.
-/
public theorem_wanted nonlinearEntireRationalIff_holds : nonlinearEntireRationalIff

end MathlibExt.Analysis.EntireFunctionPreservingRationalsErdosProblem226Wanted
