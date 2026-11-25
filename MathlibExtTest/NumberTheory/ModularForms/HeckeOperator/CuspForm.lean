/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.CuspForm

@[expose] public section

/-- exactSource consumer: `T p` preserves `S_k(Γ₀(N))` for `p ∤ N`. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f :=
  CuspForm.exists_coe_eq_heckeT f hp hpN

/-- exactSource consumer: `U p` preserves `S_k(Γ₀(N))` for `p ∣ N`. -/
example {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ}
    (hpN : p ∣ N) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  CuspForm.exists_coe_eq_heckeU f hpN

/-- exactSource consumer: vanishing of `T p f` at the cusps of an arithmetic group. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k :=
  CuspFormClass.isZeroAt_heckeT f p hc

/-- Higher-universe consumer for the cusp-vanishing statement. -/
example {F : Type 2} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeU k p ⇑f) k :=
  CuspFormClass.isZeroAt_heckeU f p hc
