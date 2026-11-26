/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Lifted integer modules and abelian groups

Let ℤ̃ be the lift of the integer ring to universe u. Modules over ℤ̃ with carrier universe u
are equivalent to abelian groups in that universe. Restriction along the ring isomorphism ℤ≅ℤ̃
identifies them with ordinary integer modules, whose scalar multiplication is determined by
their additive group structure.

The equivalence has the abelian-group forgetful functor as its forward functor. Its inverse
gives an abelian group the action ñ•a=(down ñ)•a, and additive homomorphisms are precisely the
resulting module morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

/-- Let ℤ̃ be the integer ring lifted to universe u. There is an equivalence
ModuleCat_u(ℤ̃)≃AddCommGrpCat_u obtained by restricting scalars along ℤ≅ℤ̃ and forgetting the
integer module structure. The forward functor preserves the coefficient group and additive maps,
and the inverse uses lifted integer multiplication on each abelian group. -/
noncomputable def uliftIntAddCommGrpEquivalence :
    ModuleCat.{u} (ULift.{u} ℤ) ≌ AddCommGrpCat.{u} :=
  (restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ)).trans
    (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

/-- For the integer ring ℤ̃ lifted to universe u, the forgetful functor from ℤ̃-modules with
carriers in u to abelian groups in u is an equivalence. Every abelian group has its canonical
lifted integer action, and every additive homomorphism is ℤ̃-linear. -/
noncomputable instance forget₂UliftIntAddCommGrpIsEquivalence :
    (forget₂ (ModuleCat.{u} (ULift.{u} ℤ)) AddCommGrpCat.{u}).IsEquivalence := by
  change uliftIntAddCommGrpEquivalence.functor.IsEquivalence
  infer_instance

end ModuleCat
