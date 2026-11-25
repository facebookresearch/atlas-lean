/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Logic.Small.Basic

/-!
# Discrete colimits for sheaves of modules

The theorem below fixes the coefficient-group and module universes in the
standard colimit constructors. It can be registered locally to supply public
initial-object and coproduct types with public colimit evidence, including in
contexts with both global and slice-site sheafification hypotheses.
-/

public section

universe u v₁ u₁ wI

open CategoryTheory Limits

namespace SheafOfModules

/-- Discrete colimits indexed by a `u`-small type exist in `SheafOfModules.{u} S`.
The proof explicitly uses Mathlib's additive-group, presheaf-module and
sheaf-module colimit constructors at the same module universe. -/
theorem hasColimitsOfShape_discrete
    {D : Type u₁} [Category.{v₁} D] {L : GrothendieckTopology D}
    (S : Sheaf L RingCat.{u}) [HasWeakSheafify L AddCommGrpCat.{u}]
    [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type wI) [Small.{u} I] :
    HasColimitsOfShape (Discrete I) (SheafOfModules.{u} S) := by
  let : Small.{u} (Discrete I) := inferInstance
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
    AddCommGrpCat.hasColimitsOfShape
  let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{u} S.obj) :=
    PresheafOfModules.hasColimitsOfShape S.obj (Discrete I)
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    S (Discrete I)

end SheafOfModules

end
