/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-! # Uncoupled dynamics do not lead to Nash equilibrium

A dynamic `ẋ = F(x; Γ)` on mixed-strategy profiles is *uncoupled* when each player's component
`Fⁱ` depends on the game only through that player's own payoff function (Hart and Mas-Colell
2003). Regret matching and fictitious play are uncoupled; Hart and Mas-Colell showed that no
uncoupled dynamic can guarantee convergence to Nash equilibrium, even on a neighbourhood of a
single game with a unique equilibrium, whereas uncoupled dynamics do reach the set of correlated
equilibria (regret matching).

## References

* S. Hart and A. Mas-Colell, "Uncoupled dynamics do not lead to Nash equilibrium", Amer. Econ.
  Rev. 93(5) (2003), 1830–1836: §I (definitions), Theorem 1, §III (Jordan's game).
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: §8, Theorem 3.
-/

namespace MathlibExt.GameTheory.UncoupledDynamicsWanted

/-- The Nash equilibrium of the game of Jordan's family with parameters `a` close to `1`, where
it is unique (Hart and Mas-Colell 2003, §III): player `i` (with `i − 1` taken mod 3) plays its
first action with probability `a (i − 1) / (a (i − 1) + 1)`. -/
noncomputable def jordanEq (a : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  a (i - 1) / (a (i - 1) + 1)

/-- **Uncoupled dynamics do not lead to Nash equilibrium** (Hart and Mas-Colell 2003,
Theorem 1, finite case of §III; Hart 2005, Theorem 3). Let `0 < ε < 1` (Hart and Mas-Colell's
"some small ε > 0"). Consider Jordan's three-player two-action games with parameters
`a i ∈ (1 − ε, 1 + ε)`, in which player `i`'s payoff depends on the parameters only through
`a i`, and dynamics `ẋ = F(x; a)` on the vector `x` of the probabilities of the players' first
actions. No dynamic is simultaneously uncoupled on this family (`F i` depends on the game only
through `a i`) and, for every game of the family, `C¹` with the Nash equilibrium `jordanEq a` as
a rest point whose Jacobian has only eigenvalues with negative real part.

This is stronger than Theorem 1 as worded: it drops the convergence of trajectories from the
hypotheses and asks for uncoupledness only on Jordan's family. It is exactly what the argument of
§III proves: `F¹(y¹, ½, ½; a) = 0` for the games with `a³ = y¹ / (1 − y¹)` forces
`∂F¹/∂x¹ = 0` at the equilibrium, and likewise for the other players, so the Jacobian has trace
`0` and its eigenvalues cannot all have negative real part (Hart and Mas-Colell note, footnote 15,
that `det J ≠ 0` already suffices). -/
theorem_wanted not_exists_uncoupled_stable_dynamic {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ¬ ∃ F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ),
      (∀ x a a' i, (∀ j, |a j - 1| < ε) → (∀ j, |a' j - 1| < ε) → a i = a' i →
        F x a i = F x a' i) ∧
      ∀ a, (∀ j, |a j - 1| < ε) →
        ContDiff ℝ 1 (fun x => F x a) ∧ F (jordanEq a) a = 0 ∧
        ∀ z ∈ spectrum ℂ ((LinearMap.toMatrix'
          (fderiv ℝ (fun x => F x a) (jordanEq a) : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ)).map
          (algebraMap ℝ ℂ)), z.re < 0


end MathlibExt.GameTheory.UncoupledDynamicsWanted
