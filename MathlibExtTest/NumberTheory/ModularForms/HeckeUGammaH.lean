/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeUGammaH

@[expose] public section

open scoped MatrixGroups ModularForm

/-- Source-shaped consumer: the original binders; the operators take the primality and
divisibility hypotheses of their indices. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    CuspForm.heckeULinH k hq hqM (CuspForm.heckeULinH k hq' hq'M f) =
      CuspForm.heckeULinH k hq' hq'M (CuspForm.heckeULinH k hq hqM f) :=
  CuspForm.heckeULinH_comm M H k hq hqM hq' hq'M f

/-- The zero cusp form is fixed by both composites: a boundary check that the
operators are the stated linear maps on cusp forms. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M) :
    CuspForm.heckeULinH k hq hqM (CuspForm.heckeULinH k hq' hq'M
      (0 : CuspForm (CongruenceSubgroup.GammaH M H) k)) = 0 := by
  simp

/-- Coefficients after applying `heckeULinH`: the `n`-th coefficient is the
`(n * q)`-th coefficient of the original form. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULinH k hq hqM f) n =
      ModularFormClass.qCoeff f (n * q) :=
  CuspForm.qCoeff_heckeULinH M H k hq hqM f n

/-- `heckeULinH` is `heckeU` on the underlying function, with no default value. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ⇑(CuspForm.heckeULinH k hq hqM f) = ModularForm.heckeU k q ⇑f :=
  CuspForm.coe_heckeULinH_apply k hq hqM f

/-- The prime-index Hecke formula at the prime `2`: for even `n = 2 * m`, the `n`-th
coefficient of `heckeTPrime k 2 f` is `a (2 * m * 2) + 2 ^ (k - 1) * a m`. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (m : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeTPrime k 2 f) (2 * m) =
      ModularFormClass.qCoeff f (2 * m * 2) + 2 ^ (k - 1) * ModularFormClass.qCoeff f m := by
  rw [ModularFormHeckeUQExp.qCoeff_heckeTPrime_class f hΓ,
    ModularForm.coeffHeckeTPrime_of_dvd k (dvd_mul_right 2 m),
    Nat.mul_div_cancel_left m two_pos]
  norm_num
