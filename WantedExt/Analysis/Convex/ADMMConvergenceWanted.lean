/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Convergence of the alternating direction method of multipliers (ADMM)

ADMM solves `minimize f x + g z subject to A x + B z = c` by alternately minimizing the augmented
Lagrangian `L_ρ(x, z, y) = f x + g z + ⟪y, A x + B z - c⟫ + (ρ / 2) ‖A x + B z - c‖²` over `x`
and over `z`, followed by the dual ascent step `y ← y + ρ (A x + B z - c)`. The basic convergence
theorem (Boyd, Parikh, Chu, Peleato and Eckstein, §3.2, proved in Appendix A) says that if `f`
and `g` are closed, proper and convex and the unaugmented Lagrangian `L₀` has a saddle point, then
the residual `A xᵏ + B zᵏ - c` tends to `0` and the objective `f xᵏ + g zᵏ` tends to the optimal
value. The statement below is the special case of real-valued convex `f` and `g` on
finite-dimensional real inner product spaces (real-valued convex functions there are continuous,
hence closed and proper); the iterates are taken as given minimizers, so no claim is made about
the solvability of the subproblems.
-/

@[expose] public section

namespace WantedExt.Analysis.Convex.ADMMConvergenceWanted

/-- **Convergence of ADMM.** Let `E`, `F`, `P` be finite-dimensional real inner product spaces,
`f : E → ℝ` and `g : F → ℝ` convex, `A : E →L[ℝ] P`, `B : F →L[ℝ] P`, `c : P` and `ρ > 0`, and
write `L_ρ(x, z, y) = f x + g z + ⟪y, A x + B z - c⟫ + (ρ / 2) ‖A x + B z - c‖²`. Suppose the
unaugmented Lagrangian `L₀` has a saddle point `(x⋆, z⋆, y⋆)`:
`L₀(x⋆, z⋆, y) ≤ L₀(x⋆, z⋆, y⋆) ≤ L₀(x, z, y⋆)` for all `x, z, y`. If the sequences `xᵏ, zᵏ, yᵏ`
satisfy the ADMM iteration — `xᵏ⁺¹` minimizes `L_ρ(·, zᵏ, yᵏ)`, `zᵏ⁺¹` minimizes
`L_ρ(xᵏ⁺¹, ·, yᵏ)`, and `yᵏ⁺¹ = yᵏ + ρ (A xᵏ⁺¹ + B zᵏ⁺¹ - c)` — then the primal residual
`A xᵏ + B zᵏ - c` tends to `0` and the objective `f xᵏ + g zᵏ` tends to `p⋆ = f x⋆ + g z⋆`, the
optimal value.

Source: S. Boyd, N. Parikh, E. Chu, B. Peleato and J. Eckstein, "Distributed Optimization and
Statistical Learning via the Alternating Direction Method of Multipliers", *Foundations and
Trends in Machine Learning* 3(1), 2011, §3.1 (eqs. (3.1)–(3.4)), §3.2 (Assumptions 1 and 2,
residual and objective convergence) and Appendix A (proof);
https://stanford.edu/~boyd/papers/pdf/admm_distr_stats.pdf.
Real-valued `f`, `g` are a special case of Assumption 1. -/
public theorem_wanted admm_residual_and_objective_convergence
    {E F P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    {f : E → ℝ} {g : F → ℝ} (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g)
    (A : E →L[ℝ] P) (B : F →L[ℝ] P) (c : P) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : E} {zs : F} {ys : P}
    (hsaddle : ∀ (x : E) (z : F) (y : P),
      f xs + g zs + inner ℝ y (A xs + B zs - c) ≤ f xs + g zs + inner ℝ ys (A xs + B zs - c) ∧
        f xs + g zs + inner ℝ ys (A xs + B zs - c) ≤ f x + g z + inner ℝ ys (A x + B z - c))
    {x : ℕ → E} {z : ℕ → F} {y : ℕ → P}
    (hx : ∀ k (x' : E),
      f (x (k + 1)) + g (z k) + inner ℝ (y k) (A (x (k + 1)) + B (z k) - c) +
          ρ / 2 * ‖A (x (k + 1)) + B (z k) - c‖ ^ 2 ≤
        f x' + g (z k) + inner ℝ (y k) (A x' + B (z k) - c) + ρ / 2 * ‖A x' + B (z k) - c‖ ^ 2)
    (hz : ∀ k (z' : F),
      f (x (k + 1)) + g (z (k + 1)) + inner ℝ (y k) (A (x (k + 1)) + B (z (k + 1)) - c) +
          ρ / 2 * ‖A (x (k + 1)) + B (z (k + 1)) - c‖ ^ 2 ≤
        f (x (k + 1)) + g z' + inner ℝ (y k) (A (x (k + 1)) + B z' - c) +
          ρ / 2 * ‖A (x (k + 1)) + B z' - c‖ ^ 2)
    (hy : ∀ k, y (k + 1) = y k + ρ • (A (x (k + 1)) + B (z (k + 1)) - c)) :
    Filter.Tendsto (fun k => A (x k) + B (z k) - c) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => f (x k) + g (z k)) Filter.atTop (nhds (f xs + g zs))

end WantedExt.Analysis.Convex.ADMMConvergenceWanted
