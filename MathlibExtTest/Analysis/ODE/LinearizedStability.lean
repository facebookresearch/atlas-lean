/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.LinearizedStability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Tests for linearized stability on the scalar equation `x' = -x` in `ℝ¹`: the Jacobian
`-1` is Hurwitz, `x(t) = e^{-t} v` is a solution (non-vacuity witness for the solution
hypothesis), and Lyapunov's indirect method applies. -/

open Matrix

namespace MathlibExtTest.Analysis.ODE.LinearizedStability

open MathlibExt.Analysis.ODE.LinearizedStability

/-- `-1` is Hurwitz: its only eigenvalue is `-1`. -/
theorem isHurwitz_neg_one : (-1 : Matrix (Fin 1) (Fin 1) ℝ).IsHurwitz := by
  have h : (-1 : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (-1) := by
    ext i j
    fin_cases i; fin_cases j
    simp
  intro μ hμ
  rw [h, spectrum.scalar_eq, Set.mem_singleton_iff] at hμ
  simp [hμ]

/-- The vector field `x ↦ -x` is its own linearization, with Jacobian matrix `-1`. -/
theorem hasFDerivAt_neg (x₀ : Fin 1 → ℝ) :
    HasFDerivAt (fun x : Fin 1 → ℝ => -x)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (-1 : Matrix (Fin 1) (Fin 1) ℝ))) x₀ := by
  have h : (fun x : Fin 1 → ℝ => -x) =
      LinearMap.toContinuousLinearMap (Matrix.toLin' (-1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    ext x i
    simp
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt _

/-- **Non-vacuity witness** for the solution hypothesis: `x(t) = e^{-t} v` solves `x' = -x`. -/
theorem hasDerivAt_exp_smul (v : Fin 1 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s) • v) (-(Real.exp (-t) • v)) t := by
  have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const v
  simpa [neg_smul] using this

/-- **Lyapunov's indirect method on `x' = -x`**: conditional exponential decay for global
solutions (not by itself stability, since existence is not proved by the theorem). -/
example : ∃ δ C α : ℝ, 0 < δ ∧ 0 < C ∧ 0 < α ∧ ∀ x : ℝ → Fin 1 → ℝ,
    (∀ t, 0 ≤ t → HasDerivAt x (-x t) t) → ‖x 0 - 0‖ < δ →
      ∀ t, 0 ≤ t → ‖x t - 0‖ ≤ C * Real.exp (-(α * t)) * ‖x 0 - 0‖ :=
  globalSolution_decay_of_hasFDerivAt (f := fun x => -x) neg_zero
    (hasFDerivAt_neg 0) isHurwitz_neg_one

/-- The exponential bound for the Hurwitz matrix `-1`. -/
example : ∃ M α : ℝ, 0 < M ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : Fin 1 → ℝ,
    ‖NormedSpace.exp (t • (-1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ v‖ ≤
      M * Real.exp (-(α * t)) * ‖v‖ :=
  isHurwitz_neg_one.exists_norm_exp_smul_mulVec_le

end MathlibExtTest.Analysis.ODE.LinearizedStability
