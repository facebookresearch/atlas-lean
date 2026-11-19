/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringModel

/-! Tests for the Turing system as a semilinear flow: the species maps, the diffusion semigroup
built from the trivial scalar semigroup (the zero-diffusion/kinetic limit), two
nontrivial semigroups `e^{-τ}` (which pins which species gets which coefficient) and
`P + e^{-τ}(1 - P)` (which fixes constants), the Schnakenberg steady state as the unique mild
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
example (du dv t : ℝ≥0) :
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

/-- A nontrivial scalar semigroup: `H τ = e^{-τ} • 1` (the exponential of the bounded generator
`-1`). -/
noncomputable def Hd : ℝ≥0 → C(I, ℝ) →L[ℝ] C(I, ℝ) := fun τ => Real.exp (-(τ : ℝ)) • 1

theorem isC0Semigroup_Hd : IsC0Semigroup Hd := by
  refine ⟨by simp [Hd], fun s t => ?_, fun x => ?_, fun T => ⟨1, fun t _ => ?_⟩⟩
  · ext x y
    simp [Hd, NNReal.coe_add, Real.exp_add, mul_comm, smul_smul]
  · simp only [Hd, smul_apply, one_apply_eq_self]
    fun_prop
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simp only [Hd, smul_apply, one_apply_eq_self, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (by simp))

/-- With `d_v = 0`, species `v` does not diffuse even though `H` is nontrivial; species `u`
(with `d_u = 1`) decays like `e^{-t}`. Fails if the coefficients are attached to the wrong
species. -/
example (φ : C(I, ℝ)) (t : ℝ≥0) :
    diffusionSemigroup Hd 1 0 t (speciesEmb I 1 φ) = speciesEmb I 1 φ ∧
    diffusionSemigroup Hd 1 0 t (speciesEmb I 0 φ) = Real.exp (-(t : ℝ)) • speciesEmb I 0 φ := by
  have hφ : ∀ τ : ℝ≥0, Hd τ φ = Real.exp (-(1 * τ)) • φ := fun τ => by simp [Hd]
  refine ⟨?_, ?_⟩
  · rw [diffusionSemigroup_apply_speciesEmb hφ]; simp
  · rw [diffusionSemigroup_apply_speciesEmb hφ]; simp

/-- Evaluation at `0` followed by the constant map: a bounded projection onto the constants. -/
noncomputable def P : C(I, ℝ) →L[ℝ] C(I, ℝ) :=
  ContinuousLinearMap.const ℝ I ∘L ContinuousMap.evalCLM ℝ (0 : I)

/-- A nontrivial scalar semigroup that fixes constants (like the Neumann heat semigroup):
`H τ = P + e^{-τ} (1 - P)`, which relaxes every field to its value at `0`. -/
noncomputable def Hn : ℝ≥0 → C(I, ℝ) →L[ℝ] C(I, ℝ) := fun τ => P + Real.exp (-(τ : ℝ)) • (1 - P)

theorem Hn_apply (τ : ℝ≥0) (w : C(I, ℝ)) (x : I) :
    Hn τ w x = w 0 + Real.exp (-(τ : ℝ)) * (w x - w 0) := rfl

theorem isC0Semigroup_Hn : IsC0Semigroup Hn := by
  refine ⟨?_, fun s t => ?_, fun w => ?_, fun T => ⟨‖P‖ + ‖1 - P‖, fun t _ => ?_⟩⟩
  · ext w x
    simp [Hn_apply]
  · ext w x
    simp only [ContinuousLinearMap.comp_apply, Hn_apply, NNReal.coe_add, neg_add, Real.exp_add]
    ring
  · exact continuous_const.add ((Real.continuous_exp.comp
      (NNReal.continuous_coe.neg)).smul continuous_const)
  · refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (by simp))

theorem Hn_const (τ : ℝ≥0) : Hn τ (ContinuousMap.const I 1) = ContinuousMap.const I 1 := by
  ext x
  simp [Hn_apply]

/-- `Hn` is genuinely nontrivial: it moves the identity field `x ↦ x` at positive times. -/
example : Hn 1 ⟨fun x : I => (x : ℝ), continuous_subtype_val⟩ ≠
    ⟨fun x : I => (x : ℝ), continuous_subtype_val⟩ := by
  intro h
  have := congrArg (fun w : C(I, ℝ) => w 1) h
  simp only [Hn_apply] at this
  norm_num at this

/-- Schnakenberg kinetics are Lipschitz on balls. -/
example (a b R : ℝ) : ∃ L : ℝ≥0, LipschitzOnWith L (schnakenberg a b) (Metric.closedBall 0 R) :=
  exists_lipschitzOnWith_closedBall_of_contDiff (contDiff_schnakenberg a b) R

/-- The constant field at the Schnakenberg steady state `(1, 9 / 10)` (`a = 1 / 10`,
`b = 9 / 10`). -/
noncomputable def steady : C(I, Fin 2 → ℝ) :=
  ContinuousMap.const I (schnakenbergSteadyState (1 / 10) (9 / 10))

/-- Non-vacuity with diffusion: the steady state is a mild solution of the Schnakenberg system
for the nontrivial constant-fixing semigroup `Hn` and any diffusion coefficients. -/
example (du dv : ℝ≥0) (T : ℝ) :
    IsMildSolution (diffusionSemigroup Hn du dv)
      (nemytskii (schnakenberg (1 / 10) (9 / 10))
        (contDiff_schnakenberg (1 / 10) (9 / 10) (n := 1)).continuous) steady T
      fun _ => steady :=
  isMildSolution_const Hn_const du dv _ (schnakenberg_steadyState (by norm_num)) T

/-- The steady state is a mild solution of the Schnakenberg system with `H = 1`. -/
theorem isMildSolution_steady (du dv : ℝ≥0) (T : ℝ) :
    IsMildSolution (diffusionSemigroup (fun _ => (1 : C(I, ℝ) →L[ℝ] C(I, ℝ))) du dv)
      (nemytskii (schnakenberg (1 / 10) (9 / 10))
        (contDiff_schnakenberg (1 / 10) (9 / 10) (n := 1)).continuous) steady T
      fun _ => steady :=
  isMildSolution_const (fun _ => rfl) du dv _ (schnakenberg_steadyState (by norm_num)) T

/-- The constant-fixing hypothesis matters: `Hd` does not fix constants, and with `d_u = 1` the
diffusion semigroup moves the steady state. -/
example : diffusionSemigroup Hd 1 1 1 steady ≠ steady := by
  intro h
  have := congrArg (fun w : C(I, Fin 2 → ℝ) => w 0 0) h
  simp only [diffusionSemigroup_apply_apply] at this
  simp [Hd, steady, schnakenbergSteadyState] at this
  norm_num at this

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
