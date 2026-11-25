/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.EigenformWith

@[expose] public section

open CongruenceSubgroup ModularFormClass

/-- Consumer with the original binders. -/
example {M : ℕ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) : ModularFormClass.qCoeff h 1 = 1 :=
  hh.qCoeff_one

/-- The Hecke recurrence away from the level, with the original binders. -/
example {M : ℕ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) {p : ℕ} (hp : p.Prime)
    (hpM : ¬ p ∣ M) (n : ℕ) :
    ModularFormClass.qCoeff h (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (2 - 1) *
          (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) =
      ModularFormClass.qCoeff h p * ModularFormClass.qCoeff h n :=
  hh.hecke_of_not_dvd hp hpM n

/-- A primitive form is an eigenform, with the original binders. -/
example {M : ℕ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h) : CuspForm.IsEigenformWith ε h :=
  hh.isEigenformWith

/-- Boundary: the nebentypus component is part of the eigenform package;
dropping it would lose the transformation law under `Gamma0 M`.  The
projection recovering it is definitional here. -/
example {M : ℕ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h) : CuspForm.HasNebentypus ε h :=
  hh.hasNebentypus
