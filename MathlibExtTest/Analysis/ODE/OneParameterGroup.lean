/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.OneParameterGroup
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

import Mathlib.Tactic

open OneParameterGroup

/-- The constant one-parameter group `φ ≡ 1`. -/
theorem oneParamGroup_const :
    IsOneParameterGroup 2 (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  ⟨rfl, fun _ _ => (mul_one (1 : Matrix (Fin 2) (Fin 2) ℂ)).symm, differentiable_const 1⟩

/-- The generator of the constant one-parameter group is the zero matrix. -/
theorem const_generator_eq_zero {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ t : ℝ, (1 : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp ((↑t : ℂ) • A)) :
    A = 0 := by
  obtain ⟨A₀, -, huniq⟩ := one_param_subgroup_form 2 _ oneParamGroup_const
  have h0 : (0 : Matrix (Fin 2) (Fin 2) ℂ) = A₀ := huniq 0 (fun _ => by simp)
  have hA' : A = A₀ := huniq A (fun t => by simpa using hA t)
  rw [← h0] at hA'
  exact hA'

/-- The exponential curve for the identity matrix is a one-parameter group. -/
example : IsOneParameterGroup 1
    (fun t : ℝ => NormedSpace.exp ((↑t : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))) :=
  isOneParameterGroup_exp_smul 1 1

/-- The generator of an exponential curve is unique: if `exp (t • A) = exp (t • B)`
for all `t`, then `B = A`. -/
theorem exp_smul_generator_unique (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    {B : Matrix (Fin m) (Fin m) ℂ}
    (hB : ∀ t : ℝ, NormedSpace.exp ((↑t : ℂ) • A) = NormedSpace.exp ((↑t : ℂ) • B)) :
    B = A := by
  obtain ⟨A₀, -, huniq⟩ := one_param_subgroup_form m _ (isOneParameterGroup_exp_smul m A)
  have h1 : A = A₀ := huniq A (fun _ => rfl)
  have h2 : B = A₀ := huniq B hB
  rw [← h1] at h2
  exact h2

namespace OneParameterGroupSubgroupTests

open OneParameterGroup

private abbrev slSubgroup : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) ℂ →* ℂˣ).ker

private def upperCurve (t : ℝ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.upperRightHom (t : ℂ)

/-- The canonical unipotent curve satisfies the original matrix API. -/
theorem upperCurve_isOneParameterGroup :
    IsOneParameterGroup 2 (fun t => (upperCurve t : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperCurve, Matrix.GeneralLinearGroup.upperRightHom]
  · intro s t
    change (Matrix.GeneralLinearGroup.upperRightHom (↑(s + t) : ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) =
        (Matrix.GeneralLinearGroup.upperRightHom (↑s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        (Matrix.GeneralLinearGroup.upperRightHom (↑t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    rw [Complex.ofReal_add]
    exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ))
      (Matrix.GeneralLinearGroup.upperRightHom.map_add_eq_mul (s : ℂ) (t : ℂ))
  · change Differentiable ℝ (fun t : ℝ => !![1, (t : ℂ); 0, 1])
    apply differentiable_pi.mpr
    intro i
    apply differentiable_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact differentiable_const _
      | exact fun x => Complex.ofRealCLM.hasDerivAt.differentiableAt

/-- The nonconstant unipotent curve lies in the special linear subgroup. -/
theorem upperCurve_isOneParameterGroupIn : IsOneParameterGroupIn slSubgroup upperCurve := by
  refine ⟨upperCurve_isOneParameterGroup, ?_⟩
  intro t
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [upperCurve, Matrix.GeneralLinearGroup.upperRightHom, Matrix.det_fin_two]

/-- The special linear subgroup is a proper subgroup of `GL₂(ℂ)`. -/
theorem slSubgroup_ne_top :
    slSubgroup ≠ (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℂ)) := by
  intro h
  let g := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (2 : ℂ) (by norm_num))
  have hg : g ∈ slSubgroup := by rw [h]; exact Subgroup.mem_top _
  have hdet := MonoidHom.mem_ker.mp hg
  have hval := congrArg (fun u : ℂˣ => (u : ℂ)) hdet
  norm_num [g, Matrix.GeneralLinearGroup.det_scalar] at hval

/-- The proper-subgroup fixture varies with the real parameter. -/
theorem upperCurve_nonconstant : upperCurve 1 ≠ upperCurve 0 := by
  intro h
  have hval := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ =>
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) h
  norm_num [upperCurve, Matrix.GeneralLinearGroup.upperRightHom] at hval

/-- The membership field excludes this same valid curve from the trivial subgroup. -/
theorem upperCurve_not_in_bot :
    ¬ IsOneParameterGroupIn (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℂ)) upperCurve := by
  intro h
  have h1 := Subgroup.mem_bot.mp (h.mem 1)
  have hval := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) ℂ =>
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) h1
  norm_num [upperCurve, Matrix.GeneralLinearGroup.upperRightHom] at hval

/-- The unique-generator theorem applies to the nonconstant proper-subgroup curve. -/
example : ∃! A : Matrix (Fin 2) (Fin 2) ℂ,
    ∀ t : ℝ, (upperCurve t : Matrix (Fin 2) (Fin 2) ℂ) =
      NormedSpace.exp ((↑t : ℂ) • A) :=
  one_param_subgroup_form 2 _ upperCurve_isOneParameterGroupIn.toIsOneParameterGroup

/-- Existing matrix-valued clients lift to the same proper subgroup. -/
example : IsOneParameterGroupIn slSubgroup upperCurve_isOneParameterGroup.toGL := by
  refine ⟨upperCurve_isOneParameterGroup, ?_⟩
  intro t
  have hlift : upperCurve_isOneParameterGroup.toGL t = upperCurve t := Units.ext rfl
  rw [hlift]
  exact upperCurve_isOneParameterGroupIn.mem t

#print axioms upperCurve_isOneParameterGroup
#print axioms upperCurve_isOneParameterGroupIn
#print axioms slSubgroup_ne_top
#print axioms upperCurve_nonconstant
#print axioms upperCurve_not_in_bot

end OneParameterGroupSubgroupTests

#print axioms oneParamGroup_const
#print axioms const_generator_eq_zero
#print axioms exp_smul_generator_unique
