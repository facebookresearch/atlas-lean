/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringModel

/-! Tests for the Turing system as a semilinear flow: the species maps, the diffusion semigroup
built from the trivial scalar semigroup (the zero-diffusion/kinetic limit), the homogeneous
Neumann mode `n = 0` as an eigenfunction, the Schnakenberg steady state as the unique mild
solution from itself, local well-posedness on `C([0, 1], ℝ²)`, and the Gierer–Meinhardt boundary
case. -/

open Set
open scoped NNReal unitInterval

namespace MathlibExtTest.Biology.Dynamics.TuringModel

open MathlibExt.Analysis.PDE.SemilinearFlow MathlibExt.Biology.Dynamics.TuringPatterns
open MathlibExt.Biology.Dynamics.TuringModel

/-- The trivial scalar semigroup `H τ = 1` on `C(I, ℝ)` is C₀. -/
theorem isC0Semigroup_one : IsC0Semigroup fun _ : ℝ≥0 => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ)) :=
  ⟨rfl, fun _ _ => by ext; rfl, fun _ => continuous_const,
    fun _ => ⟨1, fun _ _ => ContinuousLinearMap.norm_id_le⟩⟩

/-- Built from `H = 1`, the Turing diffusion semigroup is the identity for every `d_u, d_v`. -/
theorem diffusionSemigroup_one (du dv t : ℝ≥0) :
    diffusionSemigroup (fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ))) du dv t = 1 := by
  ext w x k
  rw [diffusionSemigroup_apply_apply]
  rfl

/-- Species maps: projecting a single-species field back. -/
example (φ : C(I, ℝ)) : speciesProj I 0 (speciesEmb I 0 φ) = φ := by
  simp [speciesProj_speciesEmb]

example (φ : C(I, ℝ)) : speciesProj I 1 (speciesEmb I 0 φ) = 0 := by
  simp [speciesProj_speciesEmb]

/-- The C₀ property transfers to the two-species semigroup. -/
example (du dv : ℝ≥0) : IsC0Semigroup
    (diffusionSemigroup (fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ))) du dv) :=
  isC0Semigroup_diffusionSemigroup isC0Semigroup_one du dv

/-- The homogeneous Neumann mode `n = 0` on `[0, L]` (wavenumber `k_0 = 0`, rate `k_0² = 0`) is
fixed by the diffusion semigroup. -/
example (L : ℝ) (φ : C(I, ℝ)) (du dv t : ℝ≥0) :
    diffusionSemigroup (fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ))) du dv t (speciesEmb I 1 φ) =
      speciesEmb I 1 φ := by
  have h := diffusionSemigroup_apply_speciesEmb (H := fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ)))
    (q := neumannWavenumber L 0 ^ 2) (φ := φ) (fun τ => by simp [neumannWavenumber]) du dv t 1
  simpa [neumannWavenumber] using h

/-- Schnakenberg kinetics are Lipschitz on balls. -/
example (a b R : ℝ) : ∃ L : ℝ≥0, LipschitzOnWith L (schnakenberg a b) (Metric.closedBall 0 R) :=
  exists_lipschitzOnWith_closedBall_of_contDiff (contDiff_schnakenberg a b) R

/-- The constant field at the Schnakenberg steady state `(1, 9 / 10)` (`a = 1 / 10`,
`b = 9 / 10`). -/
noncomputable def steady : C(I, Fin 2 → ℝ) :=
  ContinuousMap.const I (schnakenbergSteadyState (1 / 10) (9 / 10))

/-- Non-vacuity: the steady state is a mild solution of the Schnakenberg system (with `H = 1`). -/
theorem isMildSolution_steady (du dv : ℝ≥0) (T : ℝ) :
    IsMildSolution (diffusionSemigroup (fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ))) du dv)
      (nemytskii (schnakenberg (1 / 10) (9 / 10))
        (contDiff_schnakenberg (1 / 10) (9 / 10) (n := 1)).continuous) steady T
      fun _ => steady := by
  have hF : nemytskii (schnakenberg (1 / 10) (9 / 10))
      (contDiff_schnakenberg (1 / 10) (9 / 10) (n := 1)).continuous steady = 0 := by
    ext x : 1
    exact schnakenberg_steadyState (by norm_num)
  refine ⟨continuousOn_const, fun t _ => ?_, fun t _ => ?_⟩
  · simp only [hF, map_zero]
    exact intervalIntegrable_const
  · simp only [hF, map_zero, duhamel, intervalIntegral.integral_zero, add_zero,
      diffusionSemigroup_one]
    rfl

/-- Uniqueness: every mild solution from the steady state stays there. -/
example (du dv : ℝ≥0) (T : ℝ) (u : ℝ → C(I, Fin 2 → ℝ))
    (hu : IsMildSolution (diffusionSemigroup (fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ))) du dv)
      (nemytskii (schnakenberg (1 / 10) (9 / 10))
        (contDiff_schnakenberg (1 / 10) (9 / 10) (n := 1)).continuous) steady T u) :
    ∀ t ∈ Icc 0 T, u t = steady :=
  fun _ ht => isMildSolution_unique isC0Semigroup_one (contDiff_schnakenberg _ _) hu
    (isMildSolution_steady du dv T) ht

/-- Local well-posedness on `C([0, 1], ℝ²)` for the Schnakenberg kinetics: the solution from
the steady state (inside the ball of radius `2`) is the steady state. -/
example (du dv : ℝ≥0) : ∃ T > 0, ∃ sol : C(I, Fin 2 → ℝ) → ℝ → C(I, Fin 2 → ℝ),
    ∀ t ∈ Icc 0 T, sol steady t = steady := by
  obtain ⟨T, hT, R, C, -, sol, hsol, -⟩ :=
    schnakenberg_localFlow isC0Semigroup_one du dv (1 / 10) (9 / 10) 2
  have hs : ‖steady‖ ≤ 2 := by
    rw [ContinuousMap.norm_le _ zero_le_two]
    intro x
    rw [pi_norm_le_iff_of_nonneg zero_le_two]
    intro i
    fin_cases i <;> norm_num [steady, schnakenbergSteadyState]
  exact ⟨T, hT, sol, fun t ht => isMildSolution_unique isC0Semigroup_one
    (contDiff_schnakenberg _ _) (hsol steady hs).2.1 (isMildSolution_steady du dv T) ht⟩

/-- Boundary case: Gierer–Meinhardt kinetics are not Lipschitz on the unit ball. -/
example : ¬ LipschitzOnWith 100 (giererMeinhardt 1 1) (Metric.closedBall 0 1) :=
  not_lipschitzOnWith_giererMeinhardt 1 1 100

end MathlibExtTest.Biology.Dynamics.TuringModel
