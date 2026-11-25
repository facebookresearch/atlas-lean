/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Uncoupled dynamics do not lead to Nash equilibrium

A dynamic `ẋ = F(x; Γ)` on mixed-strategy profiles is *uncoupled* when each player's component
`Fⁱ` depends on the game only through that player's own payoff function (Hart and Mas-Colell
2003). Regret matching and fictitious play are uncoupled; Hart and Mas-Colell showed that no
uncoupled dynamic can guarantee convergence to Nash equilibrium, even on a neighbourhood of a
single game with a unique equilibrium, whereas uncoupled dynamics do reach the set of correlated
equilibria (regret matching).

The theorem `not_exists_uncoupled_stable_dynamic` rules out a strictly stable rest point at the
Nash equilibrium of every game in Jordan's family for an uncoupled dynamic.

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

open Filter
open scoped Topology

private theorem jordanEq_update (i : Fin 3) (t : ℝ) :
    jordanEq (Function.update 1 (i - 1) t) = Function.update (jordanEq 1) i (t / (t + 1)) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [jordanEq]
  · simp [jordanEq, Function.update_of_ne h, Function.update_of_ne (sub_left_inj.not.mpr h)]

private theorem trace_re_neg {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (h : ∀ z ∈ spectrum ℂ A, z.re < 0) : A.trace.re < 0 := by
  classical
  rw [A.trace_eq_sum_roots_charpoly]
  change Complex.reAddGroupHom A.charpoly.roots.sum < 0
  rw [map_multiset_sum, Multiset.sum_map_eq_sum_toEnumFinset]
  apply Finset.sum_neg
  · intro p hp
    exact h _ (A.mem_spectrum_of_isRoot_charpoly
      (Polynomial.isRoot_of_mem_roots (Multiset.mem_of_mem_toEnumFinset hp)))
  · apply Finset.card_pos.mp
    simpa [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
      using Fintype.card_pos (α := n)

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
theorem not_exists_uncoupled_stable_dynamic {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ¬ ∃ F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ),
      (∀ x a a' i, (∀ j, |a j - 1| < ε) → (∀ j, |a' j - 1| < ε) → a i = a' i →
        F x a i = F x a' i) ∧
      ∀ a, (∀ j, |a j - 1| < ε) →
        ContDiff ℝ 1 (fun x => F x a) ∧ F (jordanEq a) a = 0 ∧
        ∀ z ∈ spectrum ℂ ((LinearMap.toMatrix'
          (fderiv ℝ (fun x => F x a) (jordanEq a) : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ)).map
          (algebraMap ℝ ℂ)), z.re < 0 := by
  rintro ⟨F, hunc, hgame⟩
  have hone (j : Fin 3) : |(1 : Fin 3 → ℝ) j - 1| < ε := by simpa using hε
  obtain ⟨hsmooth, _, hspec⟩ := hgame 1 hone
  let q := jordanEq 1
  have hhalf (i : Fin 3) : q i = 1 / 2 := by norm_num [q, jordanEq]
  let D := fderiv ℝ (fun x => F x 1) q
  have hdiag (i : Fin 3) : D (Pi.single i 1) i = 0 := by
    -- The inverse of the equilibrium probability y = t / (t + 1) gives a nearby game.
    let param (y : ℝ) := y / (1 - y)
    have hcont : ContinuousAt param (q i) := by
      rw [hhalf]
      exact continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have hnear : ∀ᶠ y in 𝓝 (q i), |param y - 1| < ε :=
      ((hcont.sub continuousAt_const).abs.eventually_lt continuousAt_const)
        (by norm_num [param, hhalf]; exact hε)
    have hzero : (fun y => F (Function.update q i y) 1 i) =ᶠ[𝓝 (q i)] fun _ => 0 := by
      have hlt : q i < 1 := by rw [hhalf]; norm_num
      filter_upwards [hnear, eventually_lt_nhds hlt] with y hy hy1
      let a : Fin 3 → ℝ := Function.update 1 (i - 1) (param y)
      have ha (j : Fin 3) : |a j - 1| < ε := by
        by_cases hj : j = i - 1
        · simpa [a, hj] using hy
        · simpa [a, Function.update_of_ne hj] using hε
      have hpos : 0 < param y := by linarith [(abs_lt.mp hy).1]
      have hinv : param y / (param y + 1) = y := by
        apply (div_eq_iff (by positivity : param y + 1 ≠ 0)).2
        dsimp [param]
        field_simp [ne_of_gt (sub_pos.mpr hy1)]
        ring
      have heq : jordanEq a = Function.update q i y := (jordanEq_update i _).trans (by rw [hinv])
      have hpred : i ≠ i - 1 := by fin_cases i <;> decide
      rw [← heq, hunc _ 1 a i hone ha (by simp [a, Function.update_of_ne hpred])]
      exact congrFun (hgame a ha).2.1 i
    have hD : HasFDerivAt (fun x => F x 1) D q :=
      (hsmooth.differentiable (by norm_num) q).hasFDerivAt
    have hslice := (hasFDerivAt_pi'.mp hD i).comp_hasDerivAt_of_eq (q i)
      (hasDerivAt_update q i (q i)) (Function.update_eq_self i q).symm
    exact hslice.unique ((hasDerivAt_const _ _).congr_of_eventuallyEq hzero)
  let A := (LinearMap.toMatrix' D.toLinearMap).map (algebraMap ℝ ℂ)
  have htrace : A.trace = 0 := by simp [A, Matrix.trace, Matrix.diag, hdiag]
  have hneg := trace_re_neg A hspec
  simp [htrace] at hneg

end MathlibExt.GameTheory.UncoupledDynamicsWanted
