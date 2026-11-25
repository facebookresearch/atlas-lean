/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.QExpansion

@[expose] public section

open scoped Manifold

/-- exactSource consumer: `T p` acts on coefficients by `coeffHeckeT`. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeT k p f) n =
      ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n :=
  ModularFormClass.qCoeff_heckeT f hΓ hp n

/-- exactSource consumer: `U p` acts on coefficients by `coeffHeckeU`. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeU k p f) n =
      ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n :=
  ModularFormClass.qCoeff_heckeU f hΓ hp n

/-- exactSource consumer: a modular form is determined by its coefficients. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq hΓ h

/-- exactSource consumer: `T p` preserves holomorphy. -/
example {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (ModularForm.heckeT k p f) :=
  ModularForm.mdifferentiable_heckeT k p hf

/-- Higher-universe consumer: the form type may live in any universe. -/
example {F : Type 3} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeU k 1 f) n = ModularFormClass.qCoeff f n := by
  rw [ModularFormClass.qCoeff_heckeU f hΓ one_ne_zero n, ModularForm.coeffHeckeU_apply,
    mul_one]
