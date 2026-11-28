/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspFormRescale

@[expose] public section

open CongruenceSubgroup

/-- Consumer with the original binders: the rescaled coefficient formula. -/
private theorem exactSource {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.rescaleLin hdRM k f) n
      = if d ∣ n then (d : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / d)
        else 0 :=
  CuspForm.qCoeff_rescaleLin hdRM k f n

/-- Boundary example: when `d ∤ n`, the rescaled coefficient is `0`,
so the divisibility hypothesis in the coefficient formula matters. -/
example {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) {n : ℕ} (hn : ¬ d ∣ n) :
    ModularFormClass.qCoeff (CuspForm.rescaleLin hdRM k f) n = 0 := by
  rw [CuspForm.qCoeff_rescaleLin, ite_eq_right hn]

universe u v

/-- Higher-universe consumer of the general composition formula. -/
example {F : Type (max u v)} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n
      = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f hΓ hd n
