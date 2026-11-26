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

/-- Source-shaped consumer: the original binders, in the original form. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    CuspForm.heckeULinH k q (CuspForm.heckeULinH k q' f) =
      CuspForm.heckeULinH k q' (CuspForm.heckeULinH k q f) :=
  CuspForm.heckeULinH_comm M H k hq hqM hq' hq'M f

/-- Coefficients after applying `heckeULinH`: the `n`-th coefficient is the
`(n * q)`-th coefficient of the original form. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULinH k q f) n =
      ModularFormClass.qCoeff f (n * q) :=
  CuspForm.qCoeff_heckeULinH M H k hq hqM f n

/-- At a prime dividing the level, `stableU` discharges the stability hypothesis of
`heckeULinH`, which is then `heckeU` on the underlying function, not its zero default. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ⇑(CuspForm.heckeULinH k q f) = ModularForm.heckeU k q ⇑f :=
  CuspForm.coe_heckeULinH_apply k (CuspForm.stableU M H k hq hqM) f

/-- Membership in `GammaHUpper`, defined through `HeckeEis.heckeUpperSL`, is still the upper-right
entry vanishing modulo `ℓ`. -/
example (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) (γ : CongruenceSubgroup.GammaH M H) :
    γ ∈ CongruenceSubgroup.GammaHUpper M H ℓ ↔ (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) = 0 :=
  Subgroup.mem_subgroupOf.trans CongruenceSubgroup.mem_heckeUpperSL_iff_intCast_eq_zero

/-- `conjL` acts on the underlying matrix by `HeckeEis.heckeConjMat`. -/
example (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (γ : CongruenceSubgroup.GammaHUpper M H ℓ) :
    (((CongruenceSubgroup.conjL M H ℓ γ : CongruenceSubgroup.GammaH M H) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) =
      HeckeEis.heckeConjMat ℓ
        (((γ : CongruenceSubgroup.GammaH M H) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
  rfl
