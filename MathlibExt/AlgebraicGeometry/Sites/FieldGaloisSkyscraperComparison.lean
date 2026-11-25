/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionAdjunction
public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# The original field skyscraper and continuous coinduction

The actual field-sheaf equivalence transports the prescribed geometric-point
adjunction to the original forgetful Galois-module functor. Uniqueness of right
adjoints identifies the original skyscraper fiber with continuous left-shift
coinduction. The actual untwist recovers diagonal coinduction and sends the
original point unit to the existing constant-function inclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u w c d b v₁ v₂ v₃

set_option backward.isDefEq.respectTransparency.types false in
private theorem equivalenceUnitMap {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] (E : C ≌ D) (Q : C) :
    E.functor.map (E.unitIso.hom.app Q) = E.counitIso.inv.app (E.functor.obj Q) := by
  apply (cancel_mono (E.counitIso.hom.app (E.functor.obj Q))).1
  exact (E.functor_unitIso_comp Q).trans
    (E.counitIso.inv_hom_id_app (E.functor.obj Q)).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem transportedPointCounit {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] {B : Type b} [Category.{v₃} B]
    (E : C ≌ D) (U : D ⥤ B) (H : B ⥤ C) (adj : E.functor ⋙ U ⊣ H)
    (e : E.inverse ⋙ (E.functor ⋙ U) ≅ U)
    (he : ∀ A : D, e.hom.app A = U.map (E.counitIso.hom.app A)) (M : B) :
    ((E.symm.toAdjunction.comp adj).ofNatIsoLeft e).counit.app M = adj.counit.app M := by
  have hi (A : D) : e.inv.app A = U.map (E.counitIso.inv.app A) := by
    apply (cancel_mono (e.hom.app A)).1
    rw [e.inv_hom_id_app, he A, ← U.map_comp, E.counitIso.inv_hom_id_app, U.map_id]
    rfl
  change e.inv.app (E.functor.obj (H.obj M)) ≫
    (E.symm.toAdjunction.comp adj).counit.app M = adj.counit.app M
  rw [Adjunction.comp_counit_app]
  change e.inv.app (E.functor.obj (H.obj M)) ≫
    (U.map (E.functor.map (E.unitIso.inv.app (H.obj M))) ≫ adj.counit.app M) =
      adj.counit.app M
  rw [hi, ← equivalenceUnitMap E (H.obj M), ← Category.assoc,
    ← U.map_comp, ← E.functor.map_comp, E.unitIso.hom_inv_id_app,
    E.functor.map_id]
  dsimp only [Functor.id_obj]
  exact (congrArg
    (fun f : U.obj (E.functor.obj (H.obj M)) ⟶ U.obj (E.functor.obj (H.obj M)) =>
      f ≫ adj.counit.app M) (U.map_id (E.functor.obj (H.obj M)))).trans
    (Category.id_comp (adj.counit.app M))

set_option backward.isDefEq.respectTransparency.types false in
private theorem transportedPointUnit {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] {B : Type b} [Category.{v₃} B]
    (E : C ≌ D) (U : D ⥤ B) (H : B ⥤ C) (adj : E.functor ⋙ U ⊣ H)
    (e : E.inverse ⋙ (E.functor ⋙ U) ≅ U)
    (he : ∀ A : D, e.hom.app A = U.map (E.counitIso.hom.app A)) (Q : C) :
    ((E.symm.toAdjunction.comp adj).ofNatIsoLeft e).unit.app (E.functor.obj Q) =
      E.functor.map (adj.unit.app Q) := by
  change (E.symm.toAdjunction.comp adj).unit.app (E.functor.obj Q) ≫
    E.functor.map (H.map (e.hom.app (E.functor.obj Q))) = E.functor.map (adj.unit.app Q)
  rw [Adjunction.comp_unit_app]
  change (E.counitIso.inv.app (E.functor.obj Q) ≫
    E.functor.map (adj.unit.app (E.inverse.obj (E.functor.obj Q)))) ≫
      E.functor.map (H.map (e.hom.app (E.functor.obj Q))) = E.functor.map (adj.unit.app Q)
  have hn : E.unitIso.hom.app Q ≫ adj.unit.app (E.inverse.obj (E.functor.obj Q)) =
      adj.unit.app Q ≫ H.map (U.map (E.functor.map (E.unitIso.hom.app Q))) :=
    adj.unit.naturality (E.unitIso.hom.app Q)
  rw [he, ← equivalenceUnitMap E Q, ← E.functor.map_comp, hn, E.functor.map_comp,
    Category.assoc, ← E.functor.map_comp, ← H.map_comp, ← U.map_comp,
    E.functor_unitIso_comp, U.map_id]
  dsimp only [Functor.id_obj]
  have hi := (congrArg E.functor.map (H.map_id (U.obj (E.functor.obj Q)))).trans
    (E.functor.map_id (H.obj (U.obj (E.functor.obj Q))))
  exact (congrArg
    (fun f : E.functor.obj (H.obj (U.obj (E.functor.obj Q))) ⟶
        E.functor.obj (H.obj (U.obj (E.functor.obj Q))) =>
      E.functor.map (adj.unit.app Q) ≫ f) hi).trans
    (Category.comp_id (E.functor.map (adj.unit.app Q)))

private theorem rightAdjointUnitComparison {C : Type c} [Category.{v₁} C]
    {D : Type d} [Category.{v₂} D] {F : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : F ⊣ R₁) (adj₂ : F ⊣ R₂) (A B : C)
    (η : A ⟶ R₁.obj (F.obj A)) (i : R₂.obj (F.obj A) ⟶ B) (j : A ⟶ B)
    (hη : η = adj₁.unit.app A) (hi : adj₂.unit.app A ≫ i = j) :
    η ≫ ((Adjunction.rightAdjointUniq adj₁ adj₂).hom.app (F.obj A) ≫ i) = j := by
  rw [hη, ← Category.assoc]
  exact (congrArg (fun f : A ⟶ R₂.obj (F.obj A) => f ≫ i)
    (Adjunction.unit_rightAdjointUniq_hom_app adj₁ adj₂ A)).trans hi

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual field equivalence transports the point skyscraper adjunction to original
forgetting. -/
def fieldGaloisSkyscraperAdjunction :
    DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k) ⊣
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ⋙ fieldGeometricStalkGaloisFunctor.{u, w} k Ω :=
  (((fieldSheafGaloisEquivalence.{u, w} k Ω).symm.toAdjunction).comp
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))).ofNatIsoLeft (fieldModuleForgetIso.{u, w} k Ω)

set_option backward.isDefEq.respectTransparency.types false in
/-- The transported counit is the same original geometric-point evaluation counit. -/
theorem fieldGaloisSkyscraperAdjunction_counit (M : AddCommGrpCat.{max u w}) :
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω).counit.app M =
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app M := by
  exact transportedPointCounit (fieldSheafGaloisEquivalence.{u, w} k Ω)
    (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)) _
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))
    (fieldModuleForgetIso.{u, w} k Ω) (fieldModuleForgetIso_hom.{u, w} k Ω) M

set_option backward.isDefEq.respectTransparency.types false in
/-- The transported unit is exactly the Galois fiber of the original point unit. -/
theorem fieldGaloisSkyscraperAdjunction_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω).unit.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
            (A := AddCommGrpCat.{max u w})).unit.app Q) := by
  exact transportedPointUnit (fieldSheafGaloisEquivalence.{u, w} k Ω)
    (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)) _
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))
    (fieldModuleForgetIso.{u, w} k Ω) (fieldModuleForgetIso_hom.{u, w} k Ω) Q

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual field skyscraper fiber is naturally the original left-shift coinduction. -/
def fieldGaloisSkyscraperCoindIso :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ⋙ fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
      DiscreteAbelianAction.forgetCoindFunctor.{u, w} Gal(Ω/k) :=
  Adjunction.rightAdjointUniq (fieldGaloisSkyscraperAdjunction.{u, w} k Ω)
    (DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k))

set_option backward.isDefEq.respectTransparency.types false in
/-- Identity evaluation after the comparison is the original point counit. -/
theorem fieldGaloisSkyscraperCoindIso_counit_apply (M : AddCommGrpCat.{max u w})
    (z : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj M))) :
    DiscreteAbelianAction.coindFunction.{u, w} (DiscreteAbelianAction.trivialObject Gal(Ω/k) M)
        (DiscreteAbelianAction.homToAdd
            ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z) 1 =
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app M).hom z := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω)
    (DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k)) M
  have hv := ConcreteCategory.congr_hom h z
  change ((DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k)).counit.app M).hom
      (DiscreteAbelianAction.homToAdd ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z) =
    ((fieldGaloisSkyscraperAdjunction.{u, w} k Ω).counit.app M).hom z at hv
  exact (DiscreteAbelianAction.forgetCoindAdjunction_counit_apply.{u, w} Gal(Ω/k) M _).symm.trans
    (hv.trans (congrArg (fun f => f.hom z) (fieldGaloisSkyscraperAdjunction_counit.{u, w} k Ω M)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original coinduction coordinate is the point counit on the same inverse Galois orbit. -/
theorem fieldGaloisSkyscraperCoindIso_apply (M : AddCommGrpCat.{max u w})
    (z : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj M)))
    (g : Gal(Ω/k)) :
    DiscreteAbelianAction.coindFunction.{u, w} (DiscreteAbelianAction.trivialObject Gal(Ω/k) M)
        (DiscreteAbelianAction.homToAdd
            ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z) g =
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app M).hom (g⁻¹ • z) := by
  have h := DiscreteAbelianAction.forgetCoindEquivariantValue.{u, w} Gal(Ω/k) _ M
    ((fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M) z g
  exact h.symm.trans (fieldGaloisSkyscraperCoindIso_counit_apply.{u, w} k Ω M (g⁻¹ • z))

/-- Every original additive coefficient arrow commutes with the same comparison. -/
theorem fieldGaloisSkyscraperCoindIso_naturality {M N : AddCommGrpCat.{max u w}} (f : M ⟶ N) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).map f) ≫
      (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app N =
    (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M ≫
      DiscreteAbelianAction.coind.{u, w}.map (DiscreteAbelianAction.trivialMap Gal(Ω/k) f) :=
  (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.naturality f

set_option backward.isDefEq.respectTransparency.types false in
/-- Untwist the actual original point skyscraper fiber to diagonal coinduction of its Galois
fiber. -/
def fieldGaloisPointCoindIso
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
              (A := AddCommGrpCat.{max u w})).obj Q)) ≅
      DiscreteAbelianAction.coind.{u, w}.obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
  (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).app
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
          (A := AddCommGrpCat.{max u w})).obj Q) ≪≫
    DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k)
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)

set_option backward.isDefEq.respectTransparency.types false in
private theorem fieldGaloisPointCoindIsoHomModel
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGaloisPointCoindIso.{u, w} k Ω Q).hom =
      (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app
        ((DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) ≫
        (DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k)
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original point unit becomes the existing constant coinduction inclusion. -/
theorem fieldGaloisPointCoindIso_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let A : FieldCohomologyModule.{u, w} k Ω := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q
    let T : FieldCohomologyModule.{u, w} k Ω :=
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
          (A := AddCommGrpCat.{max u w})).obj
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
            (A := AddCommGrpCat.{max u w})).obj Q))
    let η : A ⟶ T := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
        (A := AddCommGrpCat.{max u w})).unit.app Q)
    let i : T ≅ DiscreteAbelianAction.coind.{u, w}.obj A := fieldGaloisPointCoindIso.{u, w} k Ω Q
    η ≫ i.hom = DiscreteAbelianAction.coindIota.{u, w}.app A := by
  intro A T η i
  have hη : η = (fieldGaloisSkyscraperAdjunction.{u, w} k Ω).unit.app A :=
    (fieldGaloisSkyscraperAdjunction_unit.{u, w} k Ω Q).symm
  have h := rightAdjointUnitComparison
    (fieldGaloisSkyscraperAdjunction.{u, w} k Ω)
    (DiscreteAbelianAction.forgetCoindAdjunction.{u, w} Gal(Ω/k)) A
    (DiscreteAbelianAction.coind.{u, w}.obj A) η
    (DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k) A).hom
    (DiscreteAbelianAction.coindIota.{u, w}.app A) hη
    (DiscreteAbelianAction.forgetCoindAdjunction_unit_untwist.{u, w} Gal(Ω/k) A)
  have hi := fieldGaloisPointCoindIsoHomModel.{u, w} k Ω Q
  exact (congrArg (fun f : T ⟶ DiscreteAbelianAction.coind.{u, w}.obj A => η ≫ f) hi).trans h

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original point-unit vector has the same constant value at every Galois element. -/
theorem fieldGaloisPointCoindIso_unit_apply
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (a : DiscreteAbelianAction.underlying ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
    (g : Gal(Ω/k)) :
    DiscreteAbelianAction.coindFunction.{u, w} ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
      (DiscreteAbelianAction.homToAdd
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
              (A := AddCommGrpCat.{max u w})).unit.app Q) ≫
            (fieldGaloisPointCoindIso.{u, w} k Ω Q).hom) a) g = a := by
  have h := fieldGaloisPointCoindIso_unit.{u, w} k Ω Q
  exact (congrArg (fun f => DiscreteAbelianAction.coindFunction.{u, w}
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
        (DiscreteAbelianAction.homToAdd f a) g) h).trans
    (DiscreteAbelianAction.coindIota_apply.{u, w}
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) a g)

set_option backward.isDefEq.respectTransparency.types false in
/-- Identity evaluation of the actual diagonal comparison is the same original point counit. -/
theorem fieldGaloisPointCoindIso_eval_one
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (z : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
            (A := AddCommGrpCat.{max u w})).obj
          (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
              (A := AddCommGrpCat.{max u w})).obj Q)))) :
    DiscreteAbelianAction.coindFunction.{u, w} ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
        (DiscreteAbelianAction.homToAdd (fieldGaloisPointCoindIso.{u, w} k Ω Q).hom z) 1 =
      (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
          (A := AddCommGrpCat.{max u w})).counit.app
        (((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
            (A := AddCommGrpCat.{max u w})).obj Q)).hom z := by
  let A := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q
  let M :=
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w})).obj Q
  let e := (fieldGaloisSkyscraperCoindIso.{u, w} k Ω).hom.app M
  have h₁ := DiscreteAbelianAction.coindUntwistIso_eval_one.{u, w} Gal(Ω/k) A
    (DiscreteAbelianAction.homToAdd e z)
  have h₂ := fieldGaloisSkyscraperCoindIso_counit_apply.{u, w} k Ω M z
  change DiscreteAbelianAction.coindFunction.{u, w} A
      (DiscreteAbelianAction.homToAdd (DiscreteAbelianAction.coindUntwistIso.{u, w} Gal(Ω/k) A).hom
        (DiscreteAbelianAction.homToAdd e z)) 1 = _
  exact h₁.trans h₂

end AlgebraicGeometry.Scheme.DerivedSections
