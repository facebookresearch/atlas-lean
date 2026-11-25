/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

/-- Modules over the universe lift of `ℤ` are equivalent to additive commutative groups. -/
noncomputable def uliftIntAddCommGrpEquivalence :
    ModuleCat.{u} (ULift.{u} ℤ) ≌ AddCommGrpCat.{u} :=
  (restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ)).trans
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

/-- Forgetting a module over the universe lift of `ℤ` is an equivalence with
additive commutative groups. -/
noncomputable instance forget₂UliftIntAddCommGrpIsEquivalence :
    (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).IsEquivalence := by
  change uliftIntAddCommGrpEquivalence.functor.IsEquivalence
  infer_instance

end ModuleCat
