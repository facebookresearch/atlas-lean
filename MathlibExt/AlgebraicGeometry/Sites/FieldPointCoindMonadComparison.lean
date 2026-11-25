/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementPrescribedTensorPairing
public import MathlibExt.AlgebraicGeometry.Sites.FieldGaloisSkyscraperComparison
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoresolution

/-!
# Actual prescribed point monad and continuous coinduction

The actual original field equivalence and point skyscraper adjunction give
the same diagonal coinduction objects, including the original unit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual prescribed point monad, under the fixed original field equivalence, is naturally the
original coinduction functor. -/
def fieldPrescribedPointCoindFunctorIso :
    (fieldPrescribedPointMonad.{u, w} k Ω).toFunctor ⋙ fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ DiscreteAbelianAction.coind.{u, w} :=
  Functor.isoWhiskerLeft
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
      (A := AddCommGrpCat.{max u w}))
    (fieldGaloisSkyscraperCoindIso.{u, w} k Ω) ≪≫
      Functor.isoWhiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (DiscreteAbelianAction.coindUntwistNatIso.{u, w} Gal(Ω/k))

set_option backward.isDefEq.respectTransparency.types false in
/-- Each original sheaf coefficient map satisfies the actual point/coinduction naturality square. -/
theorem fieldGaloisPointCoindIso_naturality
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldPrescribedPointMonad.{u, w} k Ω).map f) ≫
      (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.app G =
    (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.app F ≫
      DiscreteAbelianAction.coind.{u, w}.map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) :=
  (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.naturality f

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual comparison carries the original prescribed point unit to the original coinduction
monad unit. -/
theorem fieldPrescribedPointCoindFunctorIso_unit
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldPrescribedPointMonad.{u, w} k Ω).η.app F) ≫
      (fieldPrescribedPointCoindFunctorIso.{u, w} k Ω).hom.app F =
    (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)).η.app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F) := by
  rw [DiscreteAbelianAction.coindMonad_unit]
  exact fieldGaloisPointCoindIso_unit.{u, w} k Ω F

end AlgebraicGeometry.Scheme.DerivedSections
