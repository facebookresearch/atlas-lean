/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementCoindCochainComparison

/-! # The same actual original Godement/coinduction comparison preserves coaugmentation -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC u w
open CategoryTheory AlgebraicTopology

namespace CategoryTheory.Monad

set_option backward.isDefEq.respectTransparency.types false in
private theorem actualCoresolutionZeroCoordinates
    {C : Type uC} [Category.{vC} C] (T : Monad C) (A : C) :
    (coresolutionObjIso T A 0).hom = 𝟙 (T.obj A) := by
  rw [coresolutionObjIso_hom]
  rfl

end CategoryTheory.Monad

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual original Godement/coinduction degree comparison sends
the original geometric unit coaugmentation to the canonical coinduction unit. -/
theorem fieldGodementCoindCoresolutionTermIso_coaugmentation
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    J.map ((Monad.coresolutionAugmented T F).hom.app (SimplexCategory.mk 0)) ≫
        (fieldGodementCoindCoresolutionTermIso.{u, w} k Ω F 0).hom =
      (Monad.coresolutionAugmented S (J.obj F)).hom.app (SimplexCategory.mk 0) := by
  intro T S J
  let a := Monad.coresolutionObjIso T F 0
  let b := Monad.coresolutionObjIso S (J.obj F) 0
  have ha : a.hom = 𝟙 (T.obj F) := Monad.actualCoresolutionZeroCoordinates T F
  have hbi : b.inv = 𝟙 (S.obj (J.obj F)) := by rfl
  rw [Monad.coresolutionAugmented_hom_zero, Monad.coresolutionAugmented_hom_zero]
  change J.map (T.η.app F) ≫
      (J.map a.hom ≫
        (fieldGodementCoindPowerIso.{u, w} k Ω 1 F).hom ≫ b.inv) =
    S.η.app (J.obj F)
  rw [ha, J.map_id, hbi]
  change J.map (T.η.app F) ≫
      (𝟙 _ ≫ ((𝟙 _ ≫ (fieldGodementCoindFunctorIso.{u, w} k Ω).hom.app F) ≫ 𝟙 _)) = _
  simpa only [Category.id_comp, Category.comp_id] using
    fieldGodementCoindFunctorIso_unit.{u, w} k Ω F

end AlgebraicGeometry.Scheme.DerivedSections
