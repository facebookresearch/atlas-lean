/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.QCoeffExt
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

@[expose] public section

/-- exactSource consumer: a modular form is determined by its coefficients. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq hΓ h

/-- Higher-universe consumer: the form type may live in any universe. -/
example {F : Type 3} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq hΓ h

/-- Concrete group: cusp forms on `Γ₀(N)` with equal coefficients are equal, since `1` is a
strict period of `Γ₀(N)`. -/
example {N : ℕ} {k : ℤ} {f g : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) h
