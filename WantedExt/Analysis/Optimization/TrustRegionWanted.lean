/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Optimization.TrustRegion
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Wanted: necessary optimality conditions for the trust-region subproblem
-/

@[expose] public section

namespace WantedExt.Analysis.Optimization.TrustRegionWanted

open scoped RealInnerProductSpace
open MathlibExt.Analysis.Optimization.TrustRegion

/-- **Necessary optimality conditions for the trust-region subproblem.** Let `E` be a
finite-dimensional real inner product space, `B` a symmetric operator and `Δ > 0`. If `s` with
`‖s‖ ≤ Δ` minimises the model `q(p) = ⟪g, p⟫ + ½ ⟪B p, p⟫` over the ball `‖p‖ ≤ Δ`, then there is
`μ ≥ 0` with `B s + μ • s = -g`, `B + μ I` positive semidefinite and `μ (‖s‖ - Δ) = 0`.

This is Theorem 2.1 of N. I. M. Gould, D. P. Robinson and H. S. Thorne, *On solving trust-region
and other regularised subproblems in optimization*, Math. Program. Comput. 2 (2010), with the
identity as the norm matrix `M`; that source credits the result to Gay (1981) and to Moré and
Sorensen (1983). The converse is `trustRegionModel_le_of_optimality`. -/
theorem_wanted exists_optimality_of_isMinOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {g s : E} {B : E →L[ℝ] E} {Δ : ℝ}
    (hΔ : 0 < Δ) (hsymm : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) (hs : ‖s‖ ≤ Δ)
    (hmin : ∀ p : E, ‖p‖ ≤ Δ → trustRegionModel g B s ≤ trustRegionModel g B p) :
    ∃ μ : ℝ, 0 ≤ μ ∧ B s + μ • s = -g ∧ (∀ v, 0 ≤ ⟪B v + μ • v, v⟫) ∧ μ * (‖s‖ - Δ) = 0

end WantedExt.Analysis.Optimization.TrustRegionWanted
