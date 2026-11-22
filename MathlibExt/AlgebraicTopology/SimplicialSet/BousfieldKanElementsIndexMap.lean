/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsRowsOf
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTarget
import MathlibExt.CategoryTheory.ElementsULiftCoefficients

/-!
# Full original coefficient-elements index maps

Every original index object, arrow and coefficient is retained by the
canonical elements coefficient lift, mapElements and precomp functors.
The existing independent nerve lift supplies the full original row map.
All original scalar operators commute before taking the diagonal.
-/

noncomputable section

universe u w vJ vK

open CategoryTheory Opposite

namespace SSet

variable {J : Type u} {K : Type (max u w)} [Category.{vJ} J] [Category.{max vJ vK} K]
variable {D : J ⥤ SSet.{max u vJ}} {E : K ⥤ SSet.{max u w vJ vK}}

/-- The same full original coefficient map in each original scalar degree. -/
def bkElementsIndexCoefficient (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) (q : SimplexCategoryᵒᵖ) :
    D.flip.obj q ⋙ CategoryTheory.uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E.flip.obj q where
  app j := (α.app j).app q
  naturality j k f := by
    have h : uliftFunctor.map (D.map f) ≫ α.app k = α.app j ≫ E.map (Φ.map f) := α.naturality f
    exact NatTrans.congr_app h q

/-- The full original native coefficient-elements index functor uses only the established full elements functors. -/
def bkElementsIndexFunctor (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) (q : SimplexCategoryᵒᵖ) :
    (D.flip.obj q).Elements ⥤ (E.flip.obj q).Elements :=
  Functor.Elements.uliftCoefficients (D.flip.obj q) ⋙
    (bkElementsIndexCoefficient Φ α q).mapElements ⋙ Functor.Elements.precomp Φ (E.flip.obj q)

/-- Every full original coefficient-elements index functor commutes with the same original scalar coefficient maps. -/
theorem bkElementsIndexFunctor_naturality (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    (D.flip.map θ).mapElements ⋙ bkElementsIndexFunctor Φ α r =
      bkElementsIndexFunctor Φ α q ⋙ (E.flip.map θ).mapElements := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro x
    change (E.flip.obj r).elementsMk (Φ.obj x.obj)
        ((α.app x.obj).app r (ULift.up ((D.obj x.obj).map θ x.val))) =
      (E.flip.obj r).elementsMk (Φ.obj x.obj)
        ((E.obj (Φ.obj x.obj)).map θ ((α.app x.obj).app q (ULift.up x.val)))
    let z : ((D ⋙ uliftFunctor.{max u w vJ vK,max u vJ}).obj x.obj).obj q :=
      SSet.uliftObjEquiv.{max u vJ,max u w vJ vK} (D.obj x.obj) q x.val
    have h := ConcreteCategory.congr_hom (C := Type (max u w vJ vK))
      ((α.app x.obj).naturality θ) z
    exact congrArg ((E.flip.obj r).elementsMk (Φ.obj x.obj)) h
  case h_map =>
    intro x y f
    apply Functor.Elements.hom_ext
    have hEq : ∀ {a b : (E.flip.obj r).Elements} (h : a = b),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro a b h
      cases h
      rfl
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom, hEq, hEq]
    change Φ.map f.hom = 𝟙 _ ≫ Φ.map f.hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- The same complete original index functor defines the full original coefficient-universe-lifted elements row map. -/
def bkElementsIndexRowsULift (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) :
    bkElementsRows D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ bkElementsRowsOf E where
  app q := nerveMapULiftToTarget.{max u vJ,max w vK,vJ,vK} (bkElementsIndexFunctor Φ α q)
  naturality q r θ := by
    apply SSet.hom_ext
    intro t
    apply ConcreteCategory.hom_ext
    intro F
    change (((D.flip.map θ).mapElements ⋙ bkElementsIndexFunctor Φ α r).mapComposableArrows t.unop.len).obj F.down =
      ((bkElementsIndexFunctor Φ α q ⋙ (E.flip.map θ).mapElements).mapComposableArrows t.unop.len).obj F.down
    exact congrArg (fun G => (G.mapComposableArrows t.unop.len).obj F.down)
      (bkElementsIndexFunctor_naturality Φ α θ)

end SSet
