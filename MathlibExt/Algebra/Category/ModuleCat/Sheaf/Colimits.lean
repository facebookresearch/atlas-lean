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
# Small coproducts of module sheaves

Let `(D,L)` be a site and `S : Sheaf L RingCat.{u}` a sheaf of rings. Assume weak
sheafification of `AddCommGrpCat.{u}`-valued presheaves and the characterization of
sheafification equivalences as locally bijective maps. For any index type `I` admitting an
equivalent type in `Type u`, the category `SheafOfModules.{u} S` has colimits of shape
`Discrete I`, hence coproducts indexed by `I`.
-/

public section

universe u v₁ u₁ wI

open CategoryTheory Limits

namespace SheafOfModules

/-- Let `D : Type u₁` have morphism universe `v₁`, `L` be a Grothendieck topology, and `S : Sheaf
L RingCat.{u}`. Assume `HasWeakSheafify L AddCommGrpCat.{u}` and `L.WEqualsLocallyBijective
AddCommGrpCat.{u}`. For `I : Type wI` with `Small.{u} I`, `SheafOfModules.{u} S` has colimits
of shape `Discrete I`. Thus all coproducts with an index set of size at most `u` exist. -/
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
