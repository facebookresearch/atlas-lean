/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Optimization.BarzilaiBorwein
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Wanted: global convergence of the Barzilai–Borwein method on strictly convex quadratics
-/

@[expose] public section

namespace WantedExt.Analysis.Optimization.BarzilaiBorweinWanted

open scoped RealInnerProductSpace
open Filter Topology MathlibExt.Analysis.Optimization.BarzilaiBorwein

/-- **Raydan's theorem.** Let `A` be a symmetric positive definite operator on a
finite-dimensional real inner product space and `f(x) = ½ ⟪A x, x⟫ - ⟪b, x⟫`, with gradient
`A x - b`. Run the two-point step-size gradient method `x (k + 1) = x k - α k • (A (x k) - b)`
from any `x 0`, with any `α 0 > 0` and the Barzilai–Borwein step
`α (k + 1) = ‖s‖² / ⟪s, y⟫`, `s = x (k + 1) - x k`, `y = (A (x (k + 1)) - b) - (A (x k) - b)`.
Then the gradients converge to zero, i.e. `x k` converges to the minimiser `A⁻¹ b`.

M. Raydan, *On the Barzilai and Borwein choice of steplength for the gradient method*, IMA J.
Numer. Anal. 13 (1993), 321-326, as reported in Section 1 of Y. H. Dai, J. Y. Yuan and Y. Yuan,
Comput. Optim. Appl. 22 (2002), 103-109. (If some gradient vanishes, the iterates stop moving, and
the conclusion holds trivially.) -/
theorem_wanted raydan_tendsto_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} (hsymm : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hpos : ∀ v, v ≠ 0 → 0 < ⟪A v, v⟫) (b : E) {x : ℕ → E} {α : ℕ → ℝ} (hα0 : 0 < α 0)
    (hx : ∀ k, x (k + 1) = x k - α k • (A (x k) - b))
    (hα : ∀ k, α (k + 1) = bbStep (x (k + 1) - x k) ((A (x (k + 1)) - b) - (A (x k) - b))) :
    Tendsto (fun k => A (x k) - b) atTop (𝓝 0)

end WantedExt.Analysis.Optimization.BarzilaiBorweinWanted
