/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook91Wanted

/-- **Mazur's Problem 91 (Scottish Book), Banach-space form.** This is the proposition that
every finite-dimensional real normed space $E$ that is linearly isometric to its dual
space $E^*$ (the continuous linear functionals on $E$ with the operator norm) is an inner
product space, that is, its norm is induced by some inner product on $E$.

Mazur's original formulation asks whether, for every $n$, a convex body in $\mathbb{R}^n$
that is affinely equivalent to its conjugate (polar) body is necessarily an ellipsoid. -/
def ScottishBookProblem91Claim : Prop :=
  ∀ (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E],
    Module.finrank ℝ E = n →
    (∃ _ : E ≃ₗᵢ[ℝ] StrongDual ℝ E, True) →
    ∃ _ : InnerProductSpace ℝ E, True

/--
**Mazur's Problem 91 has a negative answer.** There is a finite-dimensional real normed
space $E$ that is linearly isometric to its dual space $E^*$ (the continuous linear
functionals on $E$ with the operator norm) but whose norm is not induced by any inner
product on $E$. Thus the Banach-space form of Mazur's Problem 91 is false.

Source: S. Mazur, Problem 91 of the Scottish Book. The typescript itself
records the negative answer when `n` is even (for example, `ℓ¹ 2`, whose unit
ball is a diamond, is linearly isometric to its dual `ℓ^∞ 2` but is not a
Hilbert space, since its norm does not satisfy the parallelogram law); the
odd-dimensional case is not needed to refute the universal claim.
-/
theorem_wanted mazur91_refuted : ¬ ScottishBookProblem91Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook91Wanted
