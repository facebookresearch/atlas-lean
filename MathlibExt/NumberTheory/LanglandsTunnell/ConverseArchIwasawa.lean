/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_
  iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero.lean`,
`Definitions/Def_LanglandsTunnell_JLConverse.lean`,
`Definitions/Def_LanglandsTunnell_ArchParam.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_
  iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.MellinArchDatum
public import MathlibExt.NumberTheory.AutomorphicForm.FnTwist

import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace LanglandsTunnell

namespace Converse

namespace ArchR

private def gM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y₁ * Real.cos θ + x * y₂ * Real.sin θ,
      -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
     y₂ * Real.sin θ, y₂ * Real.cos θ]

private def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

private theorem det_rotM (θ : ℝ) : (rotM θ).det = 1 := by
  rw [rotM, Matrix.det_fin_two_of]
  have h := Real.sin_sq_add_cos_sq θ
  nlinarith [h]

private def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM θ) (by rw [det_rotM]; exact one_ne_zero)

private theorem rotGL_coe (θ : ℝ) :
    ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ :=
  rfl

private theorem rotGL_mem (θ : ℝ) :
    rotGL θ ∈ AutomorphicForm.rowIsometrySubgroup₀ ℝ := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [AutomorphicForm.mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM], by rw [rotGL_coe, det_rotM, norm_one], ?_⟩
  intro x y
  simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
  linear_combination (x ^ 2 + y ^ 2) * h

private theorem diagOne_mul_gM (c x y₁ y₂ θ : ℝ) (hy₂ : y₂ ≠ 0) :
    diagOne c * gM x y₁ y₂ θ
      = unip (c * x) * (y₂ • (diagOne (c * y₁ / y₂) * rotM θ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagOne, gM, unip, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

end ArchR

open ArchR in
/-- Iwasawa-coordinate evaluation of an archimedean Whittaker function
of weight zero: right invariance under the determinant-one row-isometry
subgroup, together with the unipotent and central laws of the datum,
evaluates `W` on a diagonal times an Iwasawa matrix as the additive
character at `c * x`, times the central factor at `y₂`, times `W` on
the remaining diagonal matrix. -/
theorem ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
    {P : RealArchParam} (D : ArchDatumR P)
    (hDW0 : ∀ (r : AutomorphicForm.rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (ArchR.diagOne c * !![y₁ * Real.cos θ + x * y₂ * Real.sin θ,
         -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
         y₂ * Real.sin θ, y₂ * Real.cos θ]) =
      ArchR.psi (c * x) * (ArchR.centralChar P y₂ * ((|y₂| : ℝ) : ℂ))
        * D.W (ArchR.diagOne (c * y₁ / y₂)) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ArchR.diagOne (c * y₁ / y₂))
    (by rw [ArchR.diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ArchR.diagOne (c * y₁ / y₂) :=
    rfl
  have hK : D.W (ArchR.diagOne (c * y₁ / y₂) * ArchR.rotM θ)
      = D.W (ArchR.diagOne (c * y₁ / y₂)) := by
    have h := hDW0 ⟨ArchR.rotGL θ, ArchR.rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc, ArchR.rotGL_coe] at h
    exact h
  have hmain : D.W (ArchR.diagOne c * ArchR.gM x y₁ y₂ θ)
      = ArchR.psi (c * x) * (ArchR.centralChar P y₂ * ((|y₂| : ℝ) : ℂ))
        * D.W (ArchR.diagOne (c * y₁ / y₂)) := by
    rw [ArchR.diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law,
      D.central_law y₂ _ hy₂.ne', hK]
    ring
  simpa only [ArchR.gM] using hmain

end Converse

end LanglandsTunnell
