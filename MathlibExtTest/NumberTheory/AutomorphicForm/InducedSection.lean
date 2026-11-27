/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The example on `etaFst * etaSnd` reproduces the theorem type of `etaFst_mul_etaSnd` from
`Definitions/Def_AutomorphicForm_EtaFamily.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

import MathlibExt.NumberTheory.AutomorphicForm.InducedSection

open NumberField MeasureTheory AutomorphicForm

namespace AutomorphicFormInducedSectionTest

section Borel

/-- An upper-triangular matrix over `ℚ` with diagonal `(2, 3)`. -/
private def b₀ : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 1; 0, 3] (by simp [Matrix.det_fin_two])

private theorem b₀_mem : b₀ ∈ borelSubgroup ℚ := rfl

/-- The first diagonal character reads the upper-left entry. -/
example : ((borelDiagFst ⟨b₀, b₀_mem⟩ : ℚˣ) : ℚ) = 2 := rfl

/-- The second diagonal character reads the lower-right entry. -/
example : ((borelDiagSnd ⟨b₀, b₀_mem⟩ : ℚˣ) : ℚ) = 3 := rfl

/-- The Weyl element is not upper triangular. -/
example : (gl2Weyl : GL (Fin 2) ℚ) ∉ borelSubgroup ℚ := by
  simp

/-- The Weyl element is an involution. -/
example : (gl2Weyl : GL (Fin 2) ℚ) * gl2Weyl = 1 := by
  conv_lhs => enter [2]; rw [← gl2Weyl_inv]
  exact mul_inv_cancel _

end Borel

section Characters

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- At `s = 0` the complex power of a positive character is trivial. -/
example (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) :
    cpowChar α hα 0 = 1 := by
  ext x
  simp

/-- At `s = 1` the complex power of a positive character is the character itself. -/
example (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (x : (AdeleRing R K)ˣ) :
    ((cpowChar α hα 1 x : ℂˣ) : ℂ) = ((α x : ℝˣ) : ℝ) := by
  simp

/-- The two characters of the principal series multiply to `μ ν`: the powers of `α` cancel. -/
example (μ ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    etaFst μ α hα s x * etaSnd ν α hα s x = μ x * ν x := by
  ext
  have hc : ((((α x : ℝˣ) : ℝ) : ℂ)) ^ (s + 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (hα x).ne'))
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val, Complex.cpow_neg]
  rw [mul_mul_mul_comm, mul_inv_cancel₀ hc, mul_one]

/-- The trivial character is unitary. -/
example : IsUnitaryChar R K 1 := fun x => by simp

/-- The inverse of a unitary character is unitary. -/
example (χ : (AdeleRing R K)ˣ →* ℂˣ) (h : IsUnitaryChar R K χ) : IsUnitaryChar R K χ⁻¹ :=
  fun x => by simp [h x]

/-- `g ↦ χ (det g)` is a section induced from the pair `(χ, χ)`. -/
example (χ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ χ fun g => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) := by
  intro b hb g
  have h10 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0 := hb
  have hdet : Matrix.GeneralLinearGroup.det b =
      borelDiagFst (⟨b, hb⟩ : adelicBorel R K) * borelDiagSnd (⟨b, hb⟩ : adelicBorel R K) := by
    ext
    simp [Matrix.det_fin_two, h10]
  simp only [map_mul, hdet, Units.val_mul]

/-- The Weyl intertwining integral of the zero function vanishes. -/
example [MeasurableSpace (AdeleRing R K)] (ν : Measure (AdeleRing R K)) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν (fun _ => 0) g = 0 := by
  simp [weylIntertwiningIntegral]

end Characters

end AutomorphicFormInducedSectionTest
