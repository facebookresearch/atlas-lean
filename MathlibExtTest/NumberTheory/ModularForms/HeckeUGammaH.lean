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

/-- The zero cusp form is fixed by both composites: a boundary check that the
operators are the stated linear maps on cusp forms. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M) :
    CuspForm.heckeULinH k q (CuspForm.heckeULinH k q'
      (0 : CuspForm (CongruenceSubgroup.GammaH M H) k)) = 0 := by
  simp [CuspForm.heckeULinH_comm M H k hq hqM hq' hq'M
    (0 : CuspForm (CongruenceSubgroup.GammaH M H) k)]

/-- Coefficients after applying `heckeULinH`: the `n`-th coefficient is the
`(n * q)`-th coefficient of the original form. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULinH k q f) n =
      ModularFormClass.qCoeff f (n * q) :=
  CuspForm.qCoeff_heckeULinH M H k hq hqM f n
