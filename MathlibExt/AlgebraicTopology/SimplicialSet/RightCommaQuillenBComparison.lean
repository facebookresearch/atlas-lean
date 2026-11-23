/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopyRealization

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBasepointChange

/-!
# The right-comma comparison with a homotopy fiber

The defining arrow of an object of `CostructuredArrow F d` supplies a path
from the image of its source to the vertex selected by `d`.  Realizing this
row homotopy gives the canonical comparison from the realized right-comma
category to the compact-open homotopy fiber of `|nerveMap F|`.

For a morphism `g : d ⟶ d'`, the composable pair consisting of a comma
arrow and `g` gives a realized two-simplex.  Its whole, jointly continuous
family is used below to exhibit transition naturality as a bundled homotopy.
No weak-equivalence or Quillen-Theorem-B assertion is made here.
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial
open scoped Simplicial CategoryTheory.Prod unitInterval

universe u v w

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

private abbrev pathObjectProbe (B : TopCat.{u}) : TopCat.{u} :=
  TopCat.of C(TopCat.I.{u}, B)

private abbrev rightCommaProjectionFunctorProbe (F : C ⥤ D) (d : D) :
    CostructuredArrow F d ⥤ C :=
  CostructuredArrow.proj F d

private def rightCommaArrowNatTransProbe (F : C ⥤ D) (d : D) :
    rightCommaProjectionFunctorProbe F d ⋙ F ⟶
      (Functor.const (CostructuredArrow F d)).obj d where
  app X := X.hom
  naturality X Y h := by
    change F.map h.left ≫ Y.hom = X.hom ≫ 𝟙 d
    simpa only [Category.comp_id] using CostructuredArrow.w h

private theorem rightCommaArrowNatTransProbe_eq_public
    (F : C ⥤ D) (d : D) :
    rightCommaArrowNatTransProbe F d =
      SSet.rightCommaArrowNatTrans F d := by
  ext X
  rfl

private theorem rightCommaArrowNerveHomotopyProbe_eq_public
    (F : C ⥤ D) (d : D) :
    CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d) =
      SSet.rightCommaArrowNerveHomotopy F d := by
  rw [SSet.rightCommaArrowNerveHomotopy,
    rightCommaArrowNatTransProbe_eq_public]
  rfl

private def constantTransitionNatTrans (F : C ⥤ D) {d d' : D}
    (g : d ⟶ d') :
    (Functor.const (CostructuredArrow F d)).obj d ⟶
      (Functor.const (CostructuredArrow F d)).obj d' where
  app _ := g
  naturality _ _ f := by
    change 𝟙 d ≫ g = g ≫ 𝟙 d'
    simp

private def compositionNatChain (F : C ⥤ D) {d d' : D}
    (g : d ⟶ d') :
    ComposableArrows (CostructuredArrow F d ⥤ D) 2 :=
  ComposableArrows.mk₂ (rightCommaArrowNatTransProbe F d)
    (constantTransitionNatTrans F g)

private def compositionCylinderFunctor (F : C ⥤ D) {d d' : D}
    (g : d ⟶ d') :
    CostructuredArrow F d × Fin 3 ⥤ D :=
  CategoryTheory.Prod.swap (CostructuredArrow F d) (Fin 3) ⋙
    Functor.uncurry.obj (compositionNatChain F g)

private abbrev faceFunctor (j : Fin 3) : Fin 2 ⥤ Fin 3 :=
  (SimplexCategory.δ j).toOrderHom.toFunctor

private theorem compositionCylinderFunctor_face_two (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (Functor.id (CostructuredArrow F d)).prod (faceFunctor (2 : Fin 3)) ⋙
        compositionCylinderFunctor F g =
      CategoryTheory.NatTrans.nerveCylinderFunctor
        (rightCommaArrowNatTransProbe F d) := by
  apply Functor.hext
  · rintro ⟨X, i⟩
    fin_cases i <;> rfl
  · rintro ⟨X, i⟩ ⟨Y, j⟩ f
    rcases f with ⟨f, h⟩
    fin_cases i
    · fin_cases j
      · exact HEq.rfl
      · exact HEq.rfl
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom h
        omega
      · exact HEq.rfl

private theorem compositionCylinderFunctor_face_one (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (Functor.id (CostructuredArrow F d)).prod (faceFunctor (1 : Fin 3)) ⋙
        compositionCylinderFunctor F g =
      CategoryTheory.NatTrans.nerveCylinderFunctor
        (rightCommaArrowNatTransProbe F d ≫ constantTransitionNatTrans F g) := by
  apply Functor.hext
  · rintro ⟨X, i⟩
    fin_cases i <;> rfl
  · rintro ⟨X, i⟩ ⟨Y, j⟩ f
    rcases f with ⟨f, h⟩
    fin_cases i
    · fin_cases j
      · exact HEq.rfl
      · exact HEq.rfl
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom h
        omega
      · exact HEq.rfl

private def compositionNerveMap (F : C ⥤ D) {d d' : D}
    (g : d ⟶ d') :
    nerve (CostructuredArrow F d) ⊗ (Δ[2] : SSet.{max u v w}) ⟶ nerve D where
  app _ := ↾fun X =>
    ((compositionCylinderFunctor F g).mapComposableArrows _).obj
      (X.1.prod' (stdSimplex.asOrderHom X.2).toFunctor)

@[reassoc]
private theorem compositionNerveMap_face_two (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (nerve (CostructuredArrow F d) ◁
        stdSimplex.δ (2 : Fin 3)) ≫ compositionNerveMap F g =
      CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d) := by
  ext Δ X
  let T := (stdSimplex.asOrderHom X.2).toFunctor
  let Tface := (stdSimplex.asOrderHom
    ((stdSimplex.δ (2 : Fin 3)).app Δ X.2)).toFunctor
  have hInput :
      (((Functor.id (CostructuredArrow F d)).prod
        (faceFunctor (2 : Fin 3))).mapComposableArrows Δ.unop.len).obj
          (X.1.prod' T) = X.1.prod' Tface := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      exact HEq.rfl
  have hC := compositionCylinderFunctor_face_two F g
  have hApp := congrArg
    (fun K => (K.mapComposableArrows Δ.unop.len).obj (X.1.prod' T)) hC
  change ((compositionCylinderFunctor F g).mapComposableArrows Δ.unop.len).obj
      ((((Functor.id (CostructuredArrow F d)).prod
        (faceFunctor (2 : Fin 3))).mapComposableArrows Δ.unop.len).obj
          (X.1.prod' T)) = _ at hApp
  rw [hInput] at hApp
  change ((compositionCylinderFunctor F g).mapComposableArrows Δ.unop.len).obj
      (X.1.prod' Tface) =
    ((CategoryTheory.NatTrans.nerveCylinderFunctor
      (rightCommaArrowNatTransProbe F d)).mapComposableArrows Δ.unop.len).obj
        (X.1.prod' T)
  exact hApp

@[reassoc]
private theorem compositionNerveMap_face_zero (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (nerve (CostructuredArrow F d) ◁
        stdSimplex.δ (0 : Fin 3)) ≫ compositionNerveMap F g =
      CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (constantTransitionNatTrans F g) := by
  rfl

@[reassoc]
private theorem compositionNerveMap_face_one (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (nerve (CostructuredArrow F d) ◁
        stdSimplex.δ (1 : Fin 3)) ≫ compositionNerveMap F g =
      CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d ≫ constantTransitionNatTrans F g) := by
  ext Δ X
  let T := (stdSimplex.asOrderHom X.2).toFunctor
  let Tface := (stdSimplex.asOrderHom
    ((stdSimplex.δ (1 : Fin 3)).app Δ X.2)).toFunctor
  have hInput :
      (((Functor.id (CostructuredArrow F d)).prod
        (faceFunctor (1 : Fin 3))).mapComposableArrows Δ.unop.len).obj
          (X.1.prod' T) = X.1.prod' Tface := by
    apply Functor.hext
    · intro i
      rfl
    · intro i j f
      exact HEq.rfl
  have hC := compositionCylinderFunctor_face_one F g
  have hApp := congrArg
    (fun K => (K.mapComposableArrows Δ.unop.len).obj (X.1.prod' T)) hC
  change ((compositionCylinderFunctor F g).mapComposableArrows Δ.unop.len).obj
      ((((Functor.id (CostructuredArrow F d)).prod
        (faceFunctor (1 : Fin 3))).mapComposableArrows Δ.unop.len).obj
          (X.1.prod' T)) = _ at hApp
  rw [hInput] at hApp
  change ((compositionCylinderFunctor F g).mapComposableArrows Δ.unop.len).obj
      (X.1.prod' Tface) =
    ((CategoryTheory.NatTrans.nerveCylinderFunctor
      (rightCommaArrowNatTransProbe F d ≫
        constantTransitionNatTrans F g)).mapComposableArrows Δ.unop.len).obj
          (X.1.prod' T)
  exact hApp

private theorem rightCommaArrowNatTransProbe_map (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    Functor.whiskerLeft (CostructuredArrow.map g)
        (rightCommaArrowNatTransProbe F d') =
      rightCommaArrowNatTransProbe F d ≫ constantTransitionNatTrans F g := by
  apply NatTrans.ext
  funext X
  rfl

private theorem compositionNerveMap_face_one_reindex (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    (nerve (CostructuredArrow F d) ◁
        stdSimplex.δ (1 : Fin 3)) ≫ compositionNerveMap F g =
      (nerveMap (CostructuredArrow.map g) ▷ (Δ[1] : SSet.{max u v w})) ≫
        CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
          (rightCommaArrowNatTransProbe F d') := by
  rw [compositionNerveMap_face_one,
    CategoryTheory.NatTrans.nerveHomotopyMapCommonHom_precomp,
    rightCommaArrowNatTransProbe_map]

private noncomputable def univVertex₀ : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 3)

private noncomputable def univVertex₁ : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 3)

private noncomputable def univVertex₂ : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.{u}.symm (2 : Fin 3)

private noncomputable def univEdge₀₁ :
    (Δ[2] : SSet.{u}).Edge univVertex₀.{u} univVertex₁.{u} :=
  SSet.Edge.mk
    (SSet.stdSimplex.edge.{u} 2 (0 : Fin 3) (1 : Fin 3) (by decide))
    (by decide) (by decide)

private noncomputable def univEdge₁₂ :
    (Δ[2] : SSet.{u}).Edge univVertex₁.{u} univVertex₂.{u} :=
  SSet.Edge.mk
    (SSet.stdSimplex.edge.{u} 2 (1 : Fin 3) (2 : Fin 3) (by decide))
    (by decide) (by decide)

private noncomputable def univEdge₀₂ :
    (Δ[2] : SSet.{u}).Edge univVertex₀.{u} univVertex₂.{u} :=
  SSet.Edge.mk
    (SSet.stdSimplex.edge.{u} 2 (0 : Fin 3) (2 : Fin 3) (by decide))
    (by decide) (by decide)

private noncomputable def univCompStruct :
    SSet.Edge.CompStruct univEdge₀₁.{u} univEdge₁₂.{u}
      univEdge₀₂.{u} :=
  SSet.Edge.CompStruct.mk
    (SSet.yonedaEquiv ( 𝟙 (Δ[2] : SSet.{u})))
    (by decide) (by decide) (by decide)

private noncomputable def universalConcatToDirectHomotopy :
    Path.Homotopy
      ((TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{u})).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{u})))
      (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{u})) :=
  (SSet.realizedCompStructHomotopic univCompStruct.{u}).some.symm

private noncomputable def productBridgeIso (X K : SSet.{u}) :
    ((Limits.prod.functor.obj X).obj K) ≅ (X ⨯ K) :=
  Iso.refl _

@[reassoc]
private theorem productBridge_tensor_naturality
    (X : SSet.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    Limits.prod.map (𝟙 X) f ≫ (productBridgeIso X L).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app L =
      (productBridgeIso X K).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K ≫
          (X ◁ f) := by
  change (Limits.prod.functor.obj X).map f ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app L =
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K ≫
      (MonoidalCategory.tensorLeft X).map f
  exact (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.naturality f

set_option backward.isDefEq.respectTransparency false in
private theorem tensorLeftIsoProd_hom_natural_left
    {W X : SSet.{u}} (k : W ⟶ X) (T : SSet.{u}) :
    (k ▷ T) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T =
      (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
        Limits.prod.map k (𝟙 T) := by
  have hXfst :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T ≫
          Limits.prod.fst = CartesianMonoidalCategory.fst X T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X T)
      (Limits.limit.isLimit _) ⟨WalkingPair.left⟩
  have hXsnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T ≫
          Limits.prod.snd = CartesianMonoidalCategory.snd X T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X T)
      (Limits.limit.isLimit _) ⟨WalkingPair.right⟩
  have hWfst :
      (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
          Limits.prod.fst = CartesianMonoidalCategory.fst W T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct W T)
      (Limits.limit.isLimit _) ⟨WalkingPair.left⟩
  have hWsnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
          Limits.prod.snd = CartesianMonoidalCategory.snd W T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct W T)
      (Limits.limit.isLimit _) ⟨WalkingPair.right⟩
  apply Limits.prod.hom_ext
  · rw [Category.assoc, hXfst, Category.assoc, Limits.prod.map_fst]
    rw [← Category.assoc, hWfst]
    exact CartesianMonoidalCategory.whiskerRight_fst k T
  · rw [Category.assoc, hXsnd, Category.assoc, Limits.prod.map_snd]
    rw [← Category.assoc, hWsnd, Category.comp_id]
    exact CartesianMonoidalCategory.whiskerRight_snd k T

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem productBridge_tensor_naturality_left
    {W X : SSet.{u}} (k : W ⟶ X) (T : SSet.{u}) :
    Limits.prod.map k (𝟙 T) ≫ (productBridgeIso X T).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T =
      (productBridgeIso W T).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
          (k ▷ T) := by
  change Limits.prod.map k (𝟙 T) ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T =
    (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
      (k ▷ T)
  apply (cancel_mono
    ((CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T)).mp
  calc
    (Limits.prod.map k (𝟙 T) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T =
      Limits.prod.map k (𝟙 T) := by
        rw [Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
    _ = ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T) ≫
        Limits.prod.map k (𝟙 T) := by simp
    _ = (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
        ((CartesianMonoidalCategory.tensorLeftIsoProd W).hom.app T ≫
          Limits.prod.map k (𝟙 T)) := by rw [Category.assoc]
    _ = (CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
        ((k ▷ T) ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T) := by
      rw [tensorLeftIsoProd_hom_natural_left]
    _ = ((CartesianMonoidalCategory.tensorLeftIsoProd W).inv.app T ≫
          (k ▷ T)) ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T := by
      rw [Category.assoc]

@[reassoc]
private theorem productBridge_tensor_snd (X T : SSet.{u}) :
    (productBridgeIso X T).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T ≫
          CartesianMonoidalCategory.snd X T =
      Limits.prod.snd := by
  have hsnd :
      (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T ≫
          (productBridgeIso X T).hom ≫ Limits.prod.snd =
        CartesianMonoidalCategory.snd X T :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct X T)
      (Limits.limit.isLimit _) ⟨WalkingPair.right⟩
  calc
    (productBridgeIso X T).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T ≫
            CartesianMonoidalCategory.snd X T =
      (productBridgeIso X T).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app T ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app T ≫
            (productBridgeIso X T).hom ≫ Limits.prod.snd := by
              rw [hsnd]
    _ = Limits.prod.snd := by simp

private noncomputable def realizationProductIso (X : SSet.{u}) (n : ℕ) :
    SSet.toTop.obj (X ⨯ (Δ[n] : SSet.{u})) ≅
      SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[n] : SSet.{u}) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[n] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let hIso : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[n] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  exact @asIso _ _ _ _ (Limits.prodComparison SSet.toTop
    X (Δ[n] : SSet.{u})) hIso

@[simp] private theorem realizationProductIso_hom
    (X : SSet.{u}) (n : ℕ) :
    (realizationProductIso X n).hom =
      Limits.prodComparison SSet.toTop X (Δ[n] : SSet.{u}) :=
  rfl

private noncomputable def compositionEvaluation (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⨯
        SSet.toTop.obj (Δ[2] : SSet.{max u v w}) ⟶
      SSet.toTop.obj (nerve D) := by
  exact (realizationProductIso (nerve (CostructuredArrow F d)) 2).inv ≫
    SSet.toTop.map
      (productBridgeIso (nerve (CostructuredArrow F d))
        (Δ[2] : SSet.{max u v w})).inv ≫
    SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        (nerve (CostructuredArrow F d))).inv.app (Δ[2] : SSet.{max u v w})) ≫
    SSet.toTop.map (compositionNerveMap F g)

private noncomputable def orderedHomotopyEvaluation
    {X Y : SSet.{u}} (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) :
    SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[1] : SSet.{u}) ⟶
      SSet.toTop.obj Y := by
  exact (realizationProductIso X 1).inv ≫
    SSet.toTop.map (productBridgeIso X (Δ[1] : SSet.{u})).inv ≫
    SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
        (Δ[1] : SSet.{u})) ≫
    SSet.toTop.map h

private noncomputable def orderedPathMap
    {X Y : SSet.{u}} (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) :
    SSet.toTop.obj X ⟶ pathObjectProbe (SSet.toTop.obj Y) :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z => orderedHomotopyEvaluation h
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
            (z.1, SSet.stdSimplex.toTopObjIsoI.inv z.2))
      continuous_toFun :=
        (orderedHomotopyEvaluation h).hom.continuous.comp
          ((TopCat.prodIsoProd (SSet.toTop.obj X)
            (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv.hom.continuous.comp
              (continuous_fst.prodMk
                (SSet.stdSimplex.toTopObjIsoI.inv.hom.continuous.comp
                  continuous_snd))) }

private noncomputable def orderedHomotopyPath
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.toTop.obj X ⟶ pathObjectProbe (SSet.toTop.obj Y) :=
  orderedPathMap H.h

set_option backward.isDefEq.respectTransparency false in
private theorem realizeHomotopyMap_eq_ordered
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.realizeHomotopyMap X Y f g H =
      (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫
            orderedHomotopyEvaluation H.h := by
  unfold SSet.realizeHomotopyMap orderedHomotopyEvaluation
  rfl

private noncomputable def realizedHomotopyPathProbe
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.toTop.obj X ⟶ pathObjectProbe (SSet.toTop.obj Y) :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z => SSet.realizeHomotopy X Y f g H
        (TopCat.I.homeomorph z.2, z.1)
      continuous_toFun :=
        (SSet.realizeHomotopy X Y f g H).continuous.comp
          ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk
            continuous_fst) }

private theorem orderedHomotopyPath_eq_realizedHomotopyPathProbe
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    orderedHomotopyPath H = realizedHomotopyPathProbe H := by
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change orderedHomotopyEvaluation H.h
      ((TopCat.prodIsoProd
        (SSet.toTop.obj X) (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
          (z, SSet.stdSimplex.toTopObjIsoI.inv t)) =
    SSet.realizeHomotopy X Y f g H (TopCat.I.homeomorph t, z)
  change orderedHomotopyEvaluation H.h
      ((TopCat.prodIsoProd
        (SSet.toTop.obj X) (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
          (z, SSet.stdSimplex.toTopObjIsoI.inv t)) =
    SSet.realizeHomotopyMap X Y f g H
      ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv (t, z))
  have hbraid :
      (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom
          ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv (t, z)) =
        (TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv (z, t) := by
    apply Limits.Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · change (Limits.prod.fst :
          SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ SSet.toTop.obj X)
          ((Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom
            ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
              (t, z))) =
        (Limits.prod.fst :
          SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ SSet.toTop.obj X)
          ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv
            (z, t))
      calc
        _ = (Limits.prod.snd :
            TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X)
              ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
                (t, z)) := by
                  rw [← ConcreteCategory.comp_apply,
                    Limits.prod.braiding_hom, Limits.prod.lift_fst]
        _ = z := TopCat.prodIsoProd_inv_snd_apply
          (X := TopCat.I.{u}) (Y := SSet.toTop.obj X) (t, z)
        _ = _ := (TopCat.prodIsoProd_inv_fst_apply
          (X := SSet.toTop.obj X) (Y := TopCat.I.{u}) (z, t)).symm
    · change (Limits.prod.snd :
          SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ TopCat.I.{u})
          ((Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom
            ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
              (t, z))) =
        (Limits.prod.snd :
          SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ TopCat.I.{u})
          ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv
            (z, t))
      calc
        _ = (Limits.prod.fst :
            TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u})
              ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv
                (t, z)) := by
                  rw [← ConcreteCategory.comp_apply,
                    Limits.prod.braiding_hom, Limits.prod.lift_snd]
        _ = t := TopCat.prodIsoProd_inv_fst_apply
          (X := TopCat.I.{u}) (Y := SSet.toTop.obj X) (t, z)
        _ = _ := (TopCat.prodIsoProd_inv_snd_apply
          (X := SSet.toTop.obj X) (Y := TopCat.I.{u}) (z, t)).symm
  have hp := ConcreteCategory.congr_hom
    (realizeHomotopyMap_eq_ordered H)
    ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv (t, z))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hbraid] at hp
  have hprod :
      Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv
          ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv (z, t)) =
        (TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
            (z, SSet.stdSimplex.toTopObjIsoI.inv t) := by
    apply Limits.Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · change (Limits.prod.fst :
          SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[1] : SSet.{u}) ⟶
            SSet.toTop.obj X)
          (Limits.prod.map (𝟙 (SSet.toTop.obj X))
            SSet.stdSimplex.toTopObjIsoI.inv
            ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv
              (z, t))) = _
      calc
        _ = (𝟙 (SSet.toTop.obj X))
            ((Limits.prod.fst :
              SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ SSet.toTop.obj X)
              ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv
                (z, t))) := by
                  rw [← ConcreteCategory.comp_apply, Limits.prod.map_fst]
                  rfl
        _ = z := by rw [TopCat.prodIsoProd_inv_fst_apply]; rfl
        _ = _ := (TopCat.prodIsoProd_inv_fst_apply
          (X := SSet.toTop.obj X)
          (Y := SSet.toTop.obj (Δ[1] : SSet.{u}))
          (z, SSet.stdSimplex.toTopObjIsoI.inv t)).symm
    · change (Limits.prod.snd :
          SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[1] : SSet.{u}) ⟶
            SSet.toTop.obj (Δ[1] : SSet.{u}))
          (Limits.prod.map (𝟙 (SSet.toTop.obj X))
            SSet.stdSimplex.toTopObjIsoI.inv
            ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv
              (z, t))) = _
      calc
        _ = SSet.stdSimplex.toTopObjIsoI.inv
            ((Limits.prod.snd :
              SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ TopCat.I.{u})
              ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv
                (z, t))) := by
                  rw [← ConcreteCategory.comp_apply, Limits.prod.map_snd]
                  rfl
        _ = SSet.stdSimplex.toTopObjIsoI.inv t := by
          rw [TopCat.prodIsoProd_inv_snd_apply]
        _ = _ := (TopCat.prodIsoProd_inv_snd_apply
          (X := SSet.toTop.obj X)
          (Y := SSet.toTop.obj (Δ[1] : SSet.{u}))
          (z, SSet.stdSimplex.toTopObjIsoI.inv t)).symm
  rw [hprod] at hp
  exact hp.symm

@[reassoc]
private theorem realizedHomotopyPathProbe_evalZero
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    realizedHomotopyPathProbe H ≫
        TopCat.pathEvalZero (SSet.toTop.obj Y) =
      SSet.toTop.map f := by
  apply TopCat.ext
  intro x
  change SSet.realizeHomotopy X Y f g H
    (TopCat.I.homeomorph (0 : TopCat.I.{u}), x) = _
  rw [TopCat.I.homeomorph_zero]
  exact ContinuousMap.Homotopy.apply_zero
    (SSet.realizeHomotopy X Y f g H) x

@[reassoc]
private theorem realizedHomotopyPathProbe_evalOne
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    realizedHomotopyPathProbe H ≫
        TopCat.pathEvalOne (SSet.toTop.obj Y) =
      SSet.toTop.map g := by
  apply TopCat.ext
  intro x
  change SSet.realizeHomotopy X Y f g H
    (TopCat.I.homeomorph (1 : TopCat.I.{u}), x) = _
  rw [TopCat.I.homeomorph_one]
  exact ContinuousMap.Homotopy.apply_one
    (SSet.realizeHomotopy X Y f g H) x

universe hVertex

private def rightCommaVertex {D' : Type u} [Category.{hVertex} D'] (d : D') :
    (nerve D' : SSet.{max u hVertex}) _⦋0⦌ :=
  ComposableArrows.mk₀ d

private theorem nerveMap_const_eq_const (F : C ⥤ D) (d : D) :
    nerveMapCommonHom.{u, max v w, 0} ((Functor.const (CostructuredArrow F d)).obj d) =
      SSet.const (X := nerve (CostructuredArrow F d))
        (rightCommaVertex d) := by
  ext Δ X
  rfl

private noncomputable def rightCommaRealizedPathProbe
    (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      TopCat.pathObject (SSet.toTop.obj (nerve D)) :=
  realizedHomotopyPathProbe
    (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
      (rightCommaArrowNatTransProbe F d))

private def rightCommaTotalMapProbe (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      SSet.toTop.obj (nerve C) :=
  SSet.toTop.map (nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctorProbe F d))

private theorem rightCommaRealizedPathProbe_evalZero
    (F : C ⥤ D) (d : D) :
    rightCommaRealizedPathProbe F d ≫
        TopCat.pathEvalZero (SSet.toTop.obj (nerve D)) =
      rightCommaTotalMapProbe F d ≫ SSet.toTop.map (nerveMapCommonHom.{u, w, v} F) := by
  rw [rightCommaRealizedPathProbe,
    realizedHomotopyPathProbe_evalZero]
  unfold rightCommaTotalMapProbe
  calc
    SSet.toTop.map
        (nerveMapCommonHom.{u, max v w, 0} (rightCommaProjectionFunctorProbe F d ⋙ F)) =
      SSet.toTop.map
        (nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctorProbe F d) ≫
          nerveMapCommonHom.{u, w, v} F) :=
      congrArg SSet.toTop.map (by
        apply CategoryTheory.NatTrans.ext
        funext Δ
        apply ConcreteCategory.hom_ext
        intro X
        rfl)
    _ = SSet.toTop.map (nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctorProbe F d)) ≫
        SSet.toTop.map (nerveMapCommonHom.{u, w, v} F) :=
      Functor.map_comp _ _ _

private theorem rightCommaRealizedPathProbe_evalOne
    (F : C ⥤ D) (d : D) :
    rightCommaRealizedPathProbe F d ≫
        TopCat.pathEvalOne (SSet.toTop.obj (nerve D)) =
      TopCat.const (X := SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.realizedVertex (rightCommaVertex d)) := by
  rw [rightCommaRealizedPathProbe,
    realizedHomotopyPathProbe_evalOne, nerveMap_const_eq_const]
  have hfactor :
      SSet.toTop.map
          (SSet.const (X := nerve (CostructuredArrow F d))
            (rightCommaVertex d)) =
        SSet.toTop.map
            (SSet.stdSimplex.isTerminalObj₀.from
              (nerve (CostructuredArrow F d))) ≫
          SSet.toTop.map
            (SSet.const (X := (Δ[0] : SSet.{max u v w}))
              (rightCommaVertex d)) := by
    rw [← Functor.map_comp, SSet.comp_const]
  rw [hfactor, SSet.realizedVertex_eq_const]
  apply TopCat.ext
  intro x
  exact congrArg
    (SSet.toTop.map
      (SSet.const (X := (Δ[0] : SSet.{max u v w})) (rightCommaVertex d)))
    (Subsingleton.elim
      (SSet.toTop.map
        (SSet.stdSimplex.isTerminalObj₀.from
          (nerve (CostructuredArrow F d))) x)
      (default : SSet.toTop.obj (Δ[0] : SSet.{max u v w})))

private noncomputable def rightCommaHomotopyFiberComparisonProbe
    (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d)) :=
  pullback.lift
    (Limits.prod.lift (rightCommaTotalMapProbe F d)
      (TopCat.const (X := SSet.toTop.obj (nerve (CostructuredArrow F d)))
        PUnit.unit))
    (rightCommaRealizedPathProbe F d)
    (by
      apply Limits.prod.hom_ext
      · simpa [TopCat.pathEndpoints] using
          (rightCommaRealizedPathProbe_evalZero F d).symm
      · calc
          (Limits.prod.lift (rightCommaTotalMapProbe F d)
                (TopCat.const
                  (X := SSet.toTop.obj (nerve (CostructuredArrow F d)))
                  PUnit.unit) ≫
              Limits.prod.map (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
                (TopCat.const (X := TopCat.of PUnit)
                  (SSet.realizedVertex (rightCommaVertex d)))) ≫
              Limits.prod.snd =
              TopCat.const
                (X := SSet.toTop.obj (nerve (CostructuredArrow F d)))
                (SSet.realizedVertex (rightCommaVertex d)) := by
                rw [Category.assoc, Limits.prod.map_snd]
                rw [← Category.assoc, Limits.prod.lift_snd]
                apply TopCat.ext
                intro z
                change SSet.realizedVertex (rightCommaVertex d) =
                  SSet.realizedVertex (rightCommaVertex d)
                rfl
          _ = (rightCommaRealizedPathProbe F d ≫
              TopCat.pathEndpoints (SSet.toTop.obj (nerve D))) ≫
              Limits.prod.snd := by
                simpa [TopCat.pathEndpoints] using
                  (rightCommaRealizedPathProbe_evalOne F d).symm)

@[reassoc (attr := simp)]
private theorem rightCommaHomotopyFiberComparisonProbe_toTotal
    (F : C ⥤ D) (d : D) :
    rightCommaHomotopyFiberComparisonProbe F d ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (SSet.realizedVertex (rightCommaVertex d)) =
      rightCommaTotalMapProbe F d := by
  change rightCommaHomotopyFiberComparisonProbe F d ≫
      TopCat.homotopyPullbackLeft (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (TopCat.const (SSet.realizedVertex (rightCommaVertex d))) = _
  rw [rightCommaHomotopyFiberComparisonProbe,
    TopCat.homotopyPullbackLeft, ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
private theorem rightCommaHomotopyFiberComparisonProbe_path
    (F : C ⥤ D) (d : D) :
    rightCommaHomotopyFiberComparisonProbe F d ≫
        TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (SSet.realizedVertex (rightCommaVertex d)) =
      rightCommaRealizedPathProbe F d := by
  change rightCommaHomotopyFiberComparisonProbe F d ≫
      TopCat.homotopyPullbackPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (TopCat.const (SSet.realizedVertex (rightCommaVertex d))) = _
  rw [rightCommaHomotopyFiberComparisonProbe,
    TopCat.homotopyPullbackPath, pullback.lift_snd]

private noncomputable def rightCommaBasepointPathProbe
    {D' : Type u} [Category.{hVertex} D'] {d d' : D'} (g : d ⟶ d') :
    Path (SSet.realizedVertex (rightCommaVertex d))
      (SSet.realizedVertex (rightCommaVertex d')) :=
  TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk g))

private noncomputable def fiberRootPathProbe
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (z : TopCat.homotopyFiber f b) :
    Path (f (TopCat.homotopyFiberToTotal f b z)) b where
  toFun t := TopCat.homotopyFiberPath f b z (TopCat.I.homeomorph.symm t)
  continuous_toFun :=
    (TopCat.homotopyFiberPath f b z).continuous.comp
      TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalZero f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    exact h
  target' := by
    have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    have h := ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalOne f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    change TopCat.homotopyFiberPath f b z
      (TopCat.I.homeomorph.symm 1) = b
    rw [hOne]
    change TopCat.pathEvalOne B (TopCat.homotopyFiberPath f b z) = b
    change TopCat.pathEvalOne B (TopCat.homotopyFiberPath f b z) = b at h
    exact h

private theorem fiberRootPathProbe_continuous_family
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    Continuous ↿fun z : TopCat.homotopyFiber f b =>
      fiberRootPathProbe f b z := by
  exact continuous_eval.comp
    (((TopCat.homotopyFiberPath f b).hom.continuous.comp continuous_fst).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_snd))

private noncomputable def appendFiberPathProbe
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    TopCat.homotopyFiber f b ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        ((fiberRootPathProbe f b z.1).trans q) (TopCat.I.homeomorph z.2)
      continuous_toFun := by
        have htrans : Continuous
            ↿fun z : TopCat.homotopyFiber f b =>
              (fiberRootPathProbe f b z).trans q :=
          Path.trans_continuous_family _
            (fiberRootPathProbe_continuous_family f b) _
            (q.continuous.comp continuous_snd)
        exact htrans.comp
          (continuous_fst.prodMk
            (TopCat.I.homeomorph.continuous.comp continuous_snd)) }

@[reassoc]
private theorem appendFiberPathProbe_evalZero
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    appendFiberPathProbe f q ≫ TopCat.pathEvalZero B =
      TopCat.homotopyFiberToTotal f b ≫ f := by
  apply TopCat.ext
  intro z
  change ((fiberRootPathProbe f b z).trans q)
    (TopCat.I.homeomorph (0 : TopCat.I.{u})) =
      f (TopCat.homotopyFiberToTotal f b z)
  rw [TopCat.I.homeomorph_zero]
  exact ((fiberRootPathProbe f b z).trans q).source'

@[reassoc]
private theorem appendFiberPathProbe_evalOne
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    appendFiberPathProbe f q ≫ TopCat.pathEvalOne B =
      TopCat.const (X := TopCat.homotopyFiber f b) b' := by
  apply TopCat.ext
  intro z
  change ((fiberRootPathProbe f b z).trans q)
    (TopCat.I.homeomorph (1 : TopCat.I.{u})) = b'
  rw [TopCat.I.homeomorph_one]
  exact ((fiberRootPathProbe f b z).trans q).target'

private noncomputable def homotopyFiberBasepointChangeProbe
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    TopCat.homotopyFiber f b ⟶ TopCat.homotopyFiber f b' :=
  pullback.lift
    (Limits.prod.lift (TopCat.homotopyFiberToTotal f b)
      (TopCat.homotopyPullbackRight f
        (TopCat.const (X := TopCat.of PUnit) b)))
    (appendFiberPathProbe f q)
    (by
      apply Limits.prod.hom_ext
      · simpa [TopCat.pathEndpoints] using
          (appendFiberPathProbe_evalZero f q).symm
      · calc
          (Limits.prod.lift (TopCat.homotopyFiberToTotal f b)
                (TopCat.homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b')) ≫ Limits.prod.snd =
              TopCat.const b' := by
                rw [Category.assoc, Limits.prod.map_snd]
                rw [← Category.assoc, Limits.prod.lift_snd]
                apply TopCat.ext
                intro z
                exact congrArg (fun _ : PUnit => b')
                  (Subsingleton.elim
                    (TopCat.homotopyPullbackRight f
                      (TopCat.const (X := TopCat.of PUnit) b) z)
                    PUnit.unit)
          _ = (appendFiberPathProbe f q ≫ TopCat.pathEndpoints B) ≫
              Limits.prod.snd := by
                simpa [TopCat.pathEndpoints] using
                  (appendFiberPathProbe_evalOne f q).symm)

@[reassoc (attr := simp)]
private theorem homotopyFiberBasepointChangeProbe_toTotal
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiberBasepointChangeProbe f q ≫
        TopCat.homotopyFiberToTotal f b' =
      TopCat.homotopyFiberToTotal f b := by
  change homotopyFiberBasepointChangeProbe f q ≫
      TopCat.homotopyPullbackLeft f (TopCat.const b') =
    TopCat.homotopyPullbackLeft f (TopCat.const b)
  rw [homotopyFiberBasepointChangeProbe, TopCat.homotopyPullbackLeft,
    ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
private theorem homotopyFiberBasepointChangeProbe_path
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiberBasepointChangeProbe f q ≫
        TopCat.homotopyFiberPath f b' =
      appendFiberPathProbe f q := by
  change homotopyFiberBasepointChangeProbe f q ≫
      TopCat.homotopyPullbackPath f (TopCat.const b') = _
  rw [homotopyFiberBasepointChangeProbe,
    TopCat.homotopyPullbackPath, pullback.lift_snd]

private theorem orderedHomotopyEvaluation_precomp
    {W X Y : SSet.{u}} (k : W ⟶ X)
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) :
    Limits.prod.map (SSet.toTop.map k)
        (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) ≫
      orderedHomotopyEvaluation h =
    orderedHomotopyEvaluation ((k ▷ (Δ[1] : SSet.{u})) ≫ h) := by
  apply (cancel_epi (realizationProductIso W 1).hom).1
  rw [realizationProductIso_hom]
  rw [← SSet.toTop.map_id]
  rw [← Category.assoc, ← Limits.prodComparison_natural]
  unfold orderedHomotopyEvaluation
  rw [← realizationProductIso_hom X 1]
  rw [← realizationProductIso_hom W 1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp]
  rw [productBridge_tensor_naturality_left_assoc]

private theorem orderedHomotopyEvaluation_snd
    {X Y : SSet.{u}} (q : (Δ[1] : SSet.{u}) ⟶ Y) :
    orderedHomotopyEvaluation
        (CartesianMonoidalCategory.snd X (Δ[1] : SSet.{u}) ≫ q) =
      Limits.prod.snd ≫ SSet.toTop.map q := by
  apply (cancel_epi (realizationProductIso X 1).hom).1
  rw [realizationProductIso_hom]
  unfold orderedHomotopyEvaluation
  rw [← realizationProductIso_hom X 1]
  simp only [Iso.hom_inv_id_assoc]
  rw [realizationProductIso_hom, Limits.prodComparison_snd_assoc]
  simp only [← Functor.map_comp]
  apply congrArg SSet.toTop.map
  rw [productBridge_tensor_snd_assoc]

private noncomputable def compositionFamilyUncurried (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    C((unitInterval × SSet.toTop.obj (nerve (CostructuredArrow F d))) ×
        TopCat.I.{max u v w}, SSet.toTop.obj (nerve D)) where
  toFun z :=
    compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z.1.2, universalConcatToDirectHomotopy.{max u v w}
            (z.1.1, TopCat.I.homeomorph z.2)))
  continuous_toFun := by
    have hSurface : Continuous (fun z :
        (unitInterval × SSet.toTop.obj (nerve (CostructuredArrow F d))) ×
          TopCat.I.{max u v w} =>
        universalConcatToDirectHomotopy.{max u v w}
          (z.1.1, TopCat.I.homeomorph z.2)) :=
      universalConcatToDirectHomotopy.{max u v w}.continuous_toFun.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (TopCat.I.homeomorph.continuous.comp continuous_snd))
    exact (compositionEvaluation F g).hom.continuous.comp
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv.hom.continuous.comp
          ((continuous_snd.comp continuous_fst).prodMk hSurface))

private noncomputable def compositionPathMapAt (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') (s : unitInterval) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      pathObjectProbe (SSet.toTop.obj (nerve D)) :=
  TopCat.ofHom <| (ContinuousMap.curry (compositionFamilyUncurried F g)).comp
    { toFun := fun z => (s, z)
      continuous_toFun := continuous_const.prodMk continuous_id }

private noncomputable def compositionPathHomotopy (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    ContinuousMap.Homotopy
      (compositionPathMapAt F g 0).hom
      (compositionPathMapAt F g 1).hom where
  toFun := ContinuousMap.curry (compositionFamilyUncurried F g)
  continuous_toFun :=
    (ContinuousMap.curry (compositionFamilyUncurried F g)).continuous
  map_zero_left _ := rfl
  map_one_left _ := rfl

private theorem prodMap_prodIsoProd_inv_apply
    {X Y Z : TopCat.{u}} (g : Y ⟶ Z) (x : X) (y : Y) :
    Limits.prod.map (𝟙 X) g ((TopCat.prodIsoProd X Y).inv (x, y)) =
      (TopCat.prodIsoProd X Z).inv (x, g y) := by
  apply Limits.Concrete.limit_ext
  rintro ⟨⟨⟩⟩
  · change (Limits.prod.fst : X ⨯ Z ⟶ X)
        (Limits.prod.map (𝟙 X) g ((TopCat.prodIsoProd X Y).inv (x, y))) =
      (Limits.prod.fst : X ⨯ Z ⟶ X)
        ((TopCat.prodIsoProd X Z).inv (x, g y))
    calc
      _ = (𝟙 X) ((Limits.prod.fst : X ⨯ Y ⟶ X)
          ((TopCat.prodIsoProd X Y).inv (x, y))) := by
            rw [← ConcreteCategory.comp_apply, Limits.prod.map_fst]
            rfl
      _ = x := by rw [TopCat.prodIsoProd_inv_fst_apply]; rfl
      _ = _ := (TopCat.prodIsoProd_inv_fst_apply (X := X) (Y := Z)
        (x, g y)).symm
  · change (Limits.prod.snd : X ⨯ Z ⟶ Z)
        (Limits.prod.map (𝟙 X) g ((TopCat.prodIsoProd X Y).inv (x, y))) =
      (Limits.prod.snd : X ⨯ Z ⟶ Z)
        ((TopCat.prodIsoProd X Z).inv (x, g y))
    calc
      _ = g ((Limits.prod.snd : X ⨯ Y ⟶ Y)
          ((TopCat.prodIsoProd X Y).inv (x, y))) := by
            rw [← ConcreteCategory.comp_apply, Limits.prod.map_snd]
            rfl
      _ = g y := by rw [TopCat.prodIsoProd_inv_snd_apply]
      _ = _ := (TopCat.prodIsoProd_inv_snd_apply (X := X) (Y := Z)
        (x, g y)).symm

private theorem prodMap_prodIsoProd_inv_apply_left
    {W X Y : TopCat.{u}} (k : W ⟶ X) (w : W) (y : Y) :
    Limits.prod.map k (𝟙 Y) ((TopCat.prodIsoProd W Y).inv (w, y)) =
      (TopCat.prodIsoProd X Y).inv (k w, y) := by
  apply Limits.Concrete.limit_ext
  rintro ⟨⟨⟩⟩
  · change (Limits.prod.fst : X ⨯ Y ⟶ X)
        (Limits.prod.map k (𝟙 Y) ((TopCat.prodIsoProd W Y).inv (w, y))) =
      (Limits.prod.fst : X ⨯ Y ⟶ X)
        ((TopCat.prodIsoProd X Y).inv (k w, y))
    calc
      _ = k ((Limits.prod.fst : W ⨯ Y ⟶ W)
          ((TopCat.prodIsoProd W Y).inv (w, y))) := by
            rw [← ConcreteCategory.comp_apply, Limits.prod.map_fst]
            rfl
      _ = k w := by rw [TopCat.prodIsoProd_inv_fst_apply]
      _ = _ := (TopCat.prodIsoProd_inv_fst_apply (X := X) (Y := Y)
        (k w, y)).symm
  · change (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.map k (𝟙 Y) ((TopCat.prodIsoProd W Y).inv (w, y))) =
      (Limits.prod.snd : X ⨯ Y ⟶ Y)
        ((TopCat.prodIsoProd X Y).inv (k w, y))
    calc
      _ = (𝟙 Y) ((Limits.prod.snd : W ⨯ Y ⟶ Y)
          ((TopCat.prodIsoProd W Y).inv (w, y))) := by
            rw [← ConcreteCategory.comp_apply, Limits.prod.map_snd]
            rfl
      _ = y := by rw [TopCat.prodIsoProd_inv_snd_apply]; rfl
      _ = _ := (TopCat.prodIsoProd_inv_snd_apply (X := X) (Y := Y)
        (k w, y)).symm

private theorem orderedPathMap_precomp
    {W X Y : SSet.{u}} (k : W ⟶ X)
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) :
    SSet.toTop.map k ≫ orderedPathMap h =
      orderedPathMap ((k ▷ (Δ[1] : SSet.{u})) ≫ h) := by
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change orderedHomotopyEvaluation h
      ((TopCat.prodIsoProd
        (SSet.toTop.obj X) (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
          (SSet.toTop.map k z, SSet.stdSimplex.toTopObjIsoI.inv t)) =
    orderedHomotopyEvaluation ((k ▷ (Δ[1] : SSet.{u})) ≫ h)
      ((TopCat.prodIsoProd
        (SSet.toTop.obj W) (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
          (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  have hpre := ConcreteCategory.congr_hom
    (orderedHomotopyEvaluation_precomp k h)
    ((TopCat.prodIsoProd
      (SSet.toTop.obj W) (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
        (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  rw [ConcreteCategory.comp_apply,
    prodMap_prodIsoProd_inv_apply_left] at hpre
  exact hpre

private theorem directOrderedPath_reindex (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    orderedHomotopyPath
        (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
          (rightCommaArrowNatTransProbe F d ≫ constantTransitionNatTrans F g)) =
      SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        orderedHomotopyPath
          (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
            (rightCommaArrowNatTransProbe F d')) := by
  change orderedPathMap
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d ≫ constantTransitionNatTrans F g)) =
    SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
      orderedPathMap
        (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
          (rightCommaArrowNatTransProbe F d'))
  rw [orderedPathMap_precomp]
  apply congrArg orderedPathMap
  rw [CategoryTheory.NatTrans.nerveHomotopyMapCommonHom_precomp,
    rightCommaArrowNatTransProbe_map]

private theorem univEdge₀₂_yoneda :
    SSet.yonedaEquiv.symm univEdge₀₂.{u}.edge =
      SSet.stdSimplex.δ (1 : Fin 3) := by
  decide

private theorem univEdge₀₁_yoneda :
    SSet.yonedaEquiv.symm univEdge₀₁.{u}.edge =
      SSet.stdSimplex.δ (2 : Fin 3) := by
  decide

private theorem univEdge₁₂_yoneda :
    SSet.yonedaEquiv.symm univEdge₁₂.{u}.edge =
      SSet.stdSimplex.δ (0 : Fin 3) := by
  decide

private theorem universalConcatToDirectHomotopy_one_apply
    (t : TopCat.I.{u}) :
    universalConcatToDirectHomotopy.{u}
        (1, TopCat.I.homeomorph t) =
      SSet.toTop.map (SSet.stdSimplex.δ (1 : Fin 3))
        (SSet.stdSimplex.toTopObjIsoI.inv t) := by
  have hOne := universalConcatToDirectHomotopy.{u}.map_one_left
    (TopCat.I.homeomorph t)
  change universalConcatToDirectHomotopy.{u}
    (1, TopCat.I.homeomorph t) = _ at hOne
  rw [hOne]
  change (SSet.realizedEdgePath univEdge₀₂.{u}).hom
      (TopCat.I.homeomorph.symm (TopCat.I.homeomorph t)) = _
  rw [TopCat.I.homeomorph.symm_apply_apply]
  rw [SSet.realizedEdgePath_hom, univEdge₀₂_yoneda]
  rfl

private theorem compositionEvaluation_face_two (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    Limits.prod.map (𝟙 _)
        (SSet.toTop.map (stdSimplex.δ (2 : Fin 3))) ≫
      compositionEvaluation F g =
    orderedHomotopyEvaluation
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d)) := by
  let X := nerve (CostructuredArrow F d)
  apply (cancel_epi (realizationProductIso X 1).hom).1
  rw [realizationProductIso_hom]
  rw [← SSet.toTop.map_id]
  rw [← Category.assoc, ← Limits.prodComparison_natural]
  unfold compositionEvaluation orderedHomotopyEvaluation
  rw [← realizationProductIso_hom
    (nerve (CostructuredArrow F d)) 2]
  rw [← realizationProductIso_hom
    (nerve (CostructuredArrow F d)) 1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp]
  rw [productBridge_tensor_naturality_assoc]
  apply congrArg SSet.toTop.map
  calc
    (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ compositionNerveMap F g =
        (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          ((X ◁ stdSimplex.δ (2 : Fin 3)) ≫
            compositionNerveMap F g) := by rfl
    _ = (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
            (rightCommaArrowNatTransProbe F d) := by
      rw [compositionNerveMap_face_two]

private theorem compositionEvaluation_face_zero (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    Limits.prod.map (𝟙 _)
        (SSet.toTop.map (stdSimplex.δ (0 : Fin 3))) ≫
      compositionEvaluation F g =
    orderedHomotopyEvaluation
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (constantTransitionNatTrans F g)) := by
  let X := nerve (CostructuredArrow F d)
  apply (cancel_epi (realizationProductIso X 1).hom).1
  rw [realizationProductIso_hom]
  rw [← SSet.toTop.map_id]
  rw [← Category.assoc, ← Limits.prodComparison_natural]
  unfold compositionEvaluation orderedHomotopyEvaluation
  rw [← realizationProductIso_hom
    (nerve (CostructuredArrow F d)) 2]
  rw [← realizationProductIso_hom
    (nerve (CostructuredArrow F d)) 1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp]
  rw [productBridge_tensor_naturality_assoc]
  apply congrArg SSet.toTop.map
  calc
    (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ compositionNerveMap F g =
        (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          ((X ◁ stdSimplex.δ (0 : Fin 3)) ≫
            compositionNerveMap F g) := by rfl
    _ = (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
            (constantTransitionNatTrans F g) := by
      rw [compositionNerveMap_face_zero]

private theorem compositionEvaluation_face_one (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    Limits.prod.map (𝟙 _)
        (SSet.toTop.map (stdSimplex.δ (1 : Fin 3))) ≫
      compositionEvaluation F g =
    orderedHomotopyEvaluation
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d ≫ constantTransitionNatTrans F g)) := by
  let X := nerve (CostructuredArrow F d)
  apply (cancel_epi (realizationProductIso X 1).hom).1
  rw [realizationProductIso_hom]
  rw [← SSet.toTop.map_id]
  rw [← Category.assoc, ← Limits.prodComparison_natural]
  unfold compositionEvaluation orderedHomotopyEvaluation
  rw [← realizationProductIso_hom
    (nerve (CostructuredArrow F d)) 2]
  rw [← realizationProductIso_hom
    (nerve (CostructuredArrow F d)) 1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp]
  rw [productBridge_tensor_naturality_assoc]
  apply congrArg SSet.toTop.map
  calc
    (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ compositionNerveMap F g =
        (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          ((X ◁ stdSimplex.δ (1 : Fin 3)) ≫
            compositionNerveMap F g) := by rfl
    _ = (productBridgeIso X (Δ[1] : SSet.{max u v w})).inv ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app
            (Δ[1] : SSet.{max u v w}) ≫
          CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
            (rightCommaArrowNatTransProbe F d ≫
              constantTransitionNatTrans F g) := by
      rw [compositionNerveMap_face_one]

private theorem compositionPathMapAt_one (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    compositionPathMapAt F g 1 =
      orderedHomotopyPath
        (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
          (rightCommaArrowNatTransProbe F d ≫
            constantTransitionNatTrans F g)) := by
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, universalConcatToDirectHomotopy.{max u v w}
            (1, TopCat.I.homeomorph t))) =
    orderedHomotopyEvaluation
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d ≫
          constantTransitionNatTrans F g))
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
          (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  rw [universalConcatToDirectHomotopy_one_apply]
  have hface := ConcreteCategory.congr_hom
    (compositionEvaluation_face_one F g)
    ((TopCat.prodIsoProd
      (SSet.toTop.obj (nerve (CostructuredArrow F d)))
      (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
        (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  rw [ConcreteCategory.comp_apply,
    prodMap_prodIsoProd_inv_apply] at hface
  exact hface

private noncomputable def compositionEvaluationAt (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :
    C(SSet.toTop.obj (Δ[2] : SSet.{max u v w}), SSet.toTop.obj (nerve D)) where
  toFun w := compositionEvaluation F g
    ((TopCat.prodIsoProd
      (SSet.toTop.obj (nerve (CostructuredArrow F d)))
      (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv (z, w))
  continuous_toFun := (compositionEvaluation F g).hom.continuous.comp
    ((TopCat.prodIsoProd
      (SSet.toTop.obj (nerve (CostructuredArrow F d)))
      (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv.hom.continuous.comp
        (continuous_const.prodMk continuous_id))

private noncomputable def compositionFacePath₀₁ (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{max u v w})).map
    (compositionEvaluationAt F g z).continuous

private noncomputable def compositionFacePath₁₂ (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{max u v w})).map
    (compositionEvaluationAt F g z).continuous

private noncomputable def compositionFacePath₀₂ (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :=
  (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{max u v w})).map
    (compositionEvaluationAt F g z).continuous

private theorem compositionPathMapAt_zero_apply (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d)))
    (t : TopCat.I.{max u v w}) :
    compositionPathMapAt F g 0 z t =
      ((compositionFacePath₀₁ F g z).trans
        (compositionFacePath₁₂ F g z)) (TopCat.I.homeomorph t) := by
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, universalConcatToDirectHomotopy.{max u v w}
            (0, TopCat.I.homeomorph t))) = _
  have hZero := universalConcatToDirectHomotopy.{max u v w}.map_zero_left
    (TopCat.I.homeomorph t)
  change universalConcatToDirectHomotopy.{max u v w}
    (0, TopCat.I.homeomorph t) = _ at hZero
  change universalConcatToDirectHomotopy.{max u v w}
      (0, TopCat.I.homeomorph t) =
    ((TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{max u v w})).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{max u v w})))
        (TopCat.I.homeomorph t) at hZero
  rw [Path.trans_apply] at hZero
  rw [hZero]
  unfold compositionFacePath₀₁ compositionFacePath₁₂
  rw [Path.trans_apply]
  simp only [Path.map_coe, Function.comp_apply]
  split_ifs <;> rfl

private theorem compositionPathMapAt_one_apply (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d)))
    (t : TopCat.I.{max u v w}) :
    compositionPathMapAt F g 1 z t =
      compositionFacePath₀₂ F g z (TopCat.I.homeomorph t) := by
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, universalConcatToDirectHomotopy.{max u v w}
            (1, TopCat.I.homeomorph t))) = _
  have hOne := universalConcatToDirectHomotopy.{max u v w}.map_one_left
    (TopCat.I.homeomorph t)
  change universalConcatToDirectHomotopy.{max u v w}
    (1, TopCat.I.homeomorph t) = _ at hOne
  rw [hOne]
  rfl

private theorem compositionFacePath₀₁_apply (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d)))
    (t : TopCat.I.{max u v w}) :
    compositionFacePath₀₁ F g z (TopCat.I.homeomorph t) =
      orderedHomotopyPath
        (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
          (rightCommaArrowNatTransProbe F d)) z t := by
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, (TopCat.pathEquiv
            (SSet.realizedEdgePath univEdge₀₁.{max u v w}))
              (TopCat.I.homeomorph t))) = _
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, (SSet.realizedEdgePath univEdge₀₁.{max u v w}).hom t)) = _
  rw [SSet.realizedEdgePath_hom, univEdge₀₁_yoneda]
  have hface := ConcreteCategory.congr_hom
    (compositionEvaluation_face_two F g)
    ((TopCat.prodIsoProd
      (SSet.toTop.obj (nerve (CostructuredArrow F d)))
      (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
        (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  rw [ConcreteCategory.comp_apply,
    prodMap_prodIsoProd_inv_apply] at hface
  exact hface

private theorem compositionFacePath₁₂_apply (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d)))
    (t : TopCat.I.{max u v w}) :
    compositionFacePath₁₂ F g z (TopCat.I.homeomorph t) =
      orderedHomotopyPath
        (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
          (constantTransitionNatTrans F g)) z t := by
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, (TopCat.pathEquiv
            (SSet.realizedEdgePath univEdge₁₂.{max u v w}))
              (TopCat.I.homeomorph t))) = _
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, (SSet.realizedEdgePath univEdge₁₂.{max u v w}).hom t)) = _
  rw [SSet.realizedEdgePath_hom, univEdge₁₂_yoneda]
  have hface := ConcreteCategory.congr_hom
    (compositionEvaluation_face_zero F g)
    ((TopCat.prodIsoProd
      (SSet.toTop.obj (nerve (CostructuredArrow F d)))
      (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
        (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  rw [ConcreteCategory.comp_apply,
    prodMap_prodIsoProd_inv_apply] at hface
  exact hface

private theorem constantTransitionCylinder_eq (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    CategoryTheory.NatTrans.nerveCylinderFunctor
        (constantTransitionNatTrans F g) =
      CategoryTheory.Prod.snd (CostructuredArrow F d) (Fin 2) ⋙
        ComposableArrows.mk₁ g := by
  apply Functor.hext
  · rintro ⟨X, i⟩
    fin_cases i <;> rfl
  · rintro ⟨X, i⟩ ⟨Y, j⟩ h
    rcases h with ⟨f, h⟩
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [CategoryTheory.NatTrans.nerveCylinderFunctor,
          constantTransitionNatTrans, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [CategoryTheory.NatTrans.nerveCylinderFunctor,
          constantTransitionNatTrans, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom h
        omega
      · apply heq_of_eq
        simp [CategoryTheory.NatTrans.nerveCylinderFunctor,
          constantTransitionNatTrans, ComposableArrows.mk₁]

private theorem constantTransition_nerveHomotopyMap (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (constantTransitionNatTrans F g) =
      CartesianMonoidalCategory.snd
          (nerve (CostructuredArrow F d)) (Δ[1] : SSet.{max u v w}) ≫
        SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk g).edge := by
  ext Δ X
  let T := (SSet.stdSimplex.asOrderHom X.2).toFunctor
  have hC := constantTransitionCylinder_eq F g
  have hApp := congrArg
    (fun K => (K.mapComposableArrows Δ.unop.len).obj (X.1.prod' T)) hC
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor
      (constantTransitionNatTrans F g)).mapComposableArrows Δ.unop.len).obj
        (X.1.prod' T) = T ⋙ ComposableArrows.mk₁ g
  exact hApp

private theorem orderedHomotopyPath_constantTransition (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    orderedHomotopyPath
        (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
          (constantTransitionNatTrans F g)) =
      TopCat.const (X := SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk g)).hom.hom := by
  change orderedPathMap
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (constantTransitionNatTrans F g)) = _
  rw [constantTransition_nerveHomotopyMap]
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change orderedHomotopyEvaluation
      (CartesianMonoidalCategory.snd
          (nerve (CostructuredArrow F d)) (Δ[1] : SSet.{max u v w}) ≫
        SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk g).edge)
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
          (z, SSet.stdSimplex.toTopObjIsoI.inv t)) =
    (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk g)).hom t
  have hsnd := ConcreteCategory.congr_hom
    (orderedHomotopyEvaluation_snd
      (SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk g).edge))
    ((TopCat.prodIsoProd
      (SSet.toTop.obj (nerve (CostructuredArrow F d)))
      (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
        (z, SSet.stdSimplex.toTopObjIsoI.inv t))
  rw [ConcreteCategory.comp_apply,
    TopCat.prodIsoProd_inv_snd_apply] at hsnd
  change orderedHomotopyEvaluation
      (CartesianMonoidalCategory.snd
          (nerve (CostructuredArrow F d)) (Δ[1] : SSet.{max u v w}) ≫
        SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk g).edge)
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[1] : SSet.{max u v w}))).inv
          (z, SSet.stdSimplex.toTopObjIsoI.inv t)) =
    SSet.toTop.map
      (SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk g).edge)
        (SSet.stdSimplex.toTopObjIsoI.inv t)
  exact hsnd

private theorem comparisonPath_eq_compositionFace₀₁_apply
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d)))
    (s : unitInterval) :
    TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d))
        (rightCommaHomotopyFiberComparisonProbe F d z)
        (TopCat.I.homeomorph.symm s) =
      compositionFacePath₀₁ F g z s := by
  have hcomparison := ConcreteCategory.congr_hom
    (rightCommaHomotopyFiberComparisonProbe_path F d) z
  have hcomparisonPoint := congrArg
    (fun p : C(TopCat.I.{max u v w}, SSet.toTop.obj (nerve D)) =>
      p (TopCat.I.homeomorph.symm s)) hcomparison
  have hordered := ConcreteCategory.congr_hom
    (orderedHomotopyPath_eq_realizedHomotopyPathProbe
      (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTransProbe F d))) z
  have horderedPoint := congrArg
    (fun p : C(TopCat.I.{max u v w}, SSet.toTop.obj (nerve D)) =>
      p (TopCat.I.homeomorph.symm s)) hordered
  have hface := compositionFacePath₀₁_apply F g z
    (TopCat.I.homeomorph.symm s)
  rw [TopCat.I.homeomorph.apply_symm_apply] at hface
  exact hcomparisonPoint.trans (horderedPoint.symm.trans hface.symm)

private theorem basepointPath_eq_compositionFace₁₂_apply
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d')
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d)))
    (s : unitInterval) :
    rightCommaBasepointPathProbe g s = compositionFacePath₁₂ F g z s := by
  have hconstant := ConcreteCategory.congr_hom
    (orderedHomotopyPath_constantTransition F g) z
  have hconstantPoint := congrArg
    (fun p : C(TopCat.I.{max u v w}, SSet.toTop.obj (nerve D)) =>
      p (TopCat.I.homeomorph.symm s)) hconstant
  have hface := compositionFacePath₁₂_apply F g z
    (TopCat.I.homeomorph.symm s)
  rw [TopCat.I.homeomorph.apply_symm_apply] at hface
  change (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk g)).hom
      (TopCat.I.homeomorph.symm s) = compositionFacePath₁₂ F g z s
  exact hconstantPoint.symm.trans hface.symm

private theorem comparisonChange_path_eq_compositionPathMapAt_zero
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    ((rightCommaHomotopyFiberComparisonProbe F d ≫
        homotopyFiberBasepointChangeProbe (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (rightCommaBasepointPathProbe g)) ≫
      TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d'))) =
      compositionPathMapAt F g 0 := by
  rw [Category.assoc, homotopyFiberBasepointChangeProbe_path]
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change ((fiberRootPathProbe (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d))
        (rightCommaHomotopyFiberComparisonProbe F d z)).trans
      (rightCommaBasepointPathProbe g)) (TopCat.I.homeomorph t) =
    compositionPathMapAt F g 0 z t
  rw [compositionPathMapAt_zero_apply]
  simp only [Path.trans_apply]
  split_ifs with ht
  · exact comparisonPath_eq_compositionFace₀₁_apply F g z _
  · exact basepointPath_eq_compositionFace₁₂_apply F g z _

private theorem reindexedComparison_path_eq_compositionPathMapAt_one
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    ((SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparisonProbe F d') ≫
      TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d'))) =
      compositionPathMapAt F g 1 := by
  rw [Category.assoc, rightCommaHomotopyFiberComparisonProbe_path]
  rw [compositionPathMapAt_one]
  rw [directOrderedPath_reindex]
  rw [orderedHomotopyPath_eq_realizedHomotopyPathProbe]
  rw [rightCommaRealizedPathProbe]

private theorem rightCommaTotalMapProbe_naturality
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaTotalMapProbe F d' =
      rightCommaTotalMapProbe F d := by
  unfold rightCommaTotalMapProbe
  rw [← Functor.map_comp]
  apply congrArg SSet.toTop.map
  calc
    nerveMap (CostructuredArrow.map g) ≫
        nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctorProbe F d') =
      nerveMapCommonHom.{max u w, v, w}
        (CostructuredArrow.map g ⋙ rightCommaProjectionFunctorProbe F d') :=
      CategoryTheory.nerveMap_nerveMapCommonHom_comp.{max u w, v, w} _ _
    _ = nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctorProbe F d) := by rfl

private theorem compositionPathMapAt_evalZero_apply
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d')
    (s : unitInterval)
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :
    compositionPathMapAt F g s z (0 : TopCat.I.{max u v w}) =
      SSet.toTop.map (nerveMapCommonHom.{u, w, v} F) (rightCommaTotalMapProbe F d z) := by
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, universalConcatToDirectHomotopy.{max u v w}
            (s, TopCat.I.homeomorph (0 : TopCat.I.{max u v w})))) = _
  rw [TopCat.I.homeomorph_zero]
  rw [Path.Homotopy.source]
  calc
    compositionEvaluation F g
        ((TopCat.prodIsoProd
          (SSet.toTop.obj (nerve (CostructuredArrow F d)))
          (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
            (z, SSet.realizedVertex univVertex₀)) =
        compositionFacePath₀₁ F g z (0 : unitInterval) :=
      (compositionFacePath₀₁ F g z).source'.symm
    _ = compositionFacePath₀₁ F g z
        (TopCat.I.homeomorph (0 : TopCat.I.{max u v w})) := by
      rw [TopCat.I.homeomorph_zero]
    _ = orderedHomotopyPath
        (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
          (rightCommaArrowNatTransProbe F d)) z (0 : TopCat.I.{max u v w}) :=
      compositionFacePath₀₁_apply F g z (0 : TopCat.I.{max u v w})
    _ = rightCommaRealizedPathProbe F d z (0 : TopCat.I.{max u v w}) := by
      have h := ConcreteCategory.congr_hom
        (orderedHomotopyPath_eq_realizedHomotopyPathProbe
          (CategoryTheory.NatTrans.nerveHomotopyCommonHom.{u, max v w, 0}
            (rightCommaArrowNatTransProbe F d))) z
      exact congrArg (fun p : C(TopCat.I.{max u v w},
        SSet.toTop.obj (nerve D)) => p (0 : TopCat.I.{max u v w})) h
    _ = SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)
        (rightCommaTotalMapProbe F d z) := by
      have h := ConcreteCategory.congr_hom
        (rightCommaRealizedPathProbe_evalZero F d) z
      exact h

private theorem compositionPathMapAt_evalOne_apply
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d')
    (s : unitInterval)
    (z : SSet.toTop.obj (nerve (CostructuredArrow F d))) :
    compositionPathMapAt F g s z (1 : TopCat.I.{max u v w}) =
      SSet.realizedVertex (rightCommaVertex d') := by
  change compositionEvaluation F g
      ((TopCat.prodIsoProd
        (SSet.toTop.obj (nerve (CostructuredArrow F d)))
        (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
          (z, universalConcatToDirectHomotopy.{max u v w}
            (s, TopCat.I.homeomorph (1 : TopCat.I.{max u v w})))) = _
  rw [TopCat.I.homeomorph_one]
  rw [Path.Homotopy.target]
  calc
    compositionEvaluation F g
        ((TopCat.prodIsoProd
          (SSet.toTop.obj (nerve (CostructuredArrow F d)))
          (SSet.toTop.obj (Δ[2] : SSet.{max u v w}))).inv
            (z, SSet.realizedVertex univVertex₂)) =
        compositionFacePath₁₂ F g z (1 : unitInterval) :=
      (compositionFacePath₁₂ F g z).target'.symm
    _ = compositionFacePath₁₂ F g z
        (TopCat.I.homeomorph (1 : TopCat.I.{max u v w})) := by
      rw [TopCat.I.homeomorph_one]
    _ = rightCommaBasepointPathProbe g (1 : unitInterval) :=
      (basepointPath_eq_compositionFace₁₂_apply F g z
        (1 : unitInterval)).symm
    _ = SSet.realizedVertex (rightCommaVertex d') :=
      (rightCommaBasepointPathProbe g).target'

private abbrev transitionFamilyDomain (F : C ⥤ D) (d : D) : TopCat.{max u v w} :=
  TopCat.of (unitInterval ×
    SSet.toTop.obj (nerve (CostructuredArrow F d)))

private noncomputable def transitionFamilySlice (F : C ⥤ D) (d : D)
    (s : unitInterval) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      transitionFamilyDomain F d :=
  TopCat.ofHom
    { toFun := fun z => (s, z)
      continuous_toFun := continuous_const.prodMk continuous_id }

private noncomputable def transitionFamilyTotal (F : C ⥤ D) (d : D) :
    transitionFamilyDomain F d ⟶ SSet.toTop.obj (nerve C) :=
  TopCat.ofHom
    { toFun := fun z => rightCommaTotalMapProbe F d z.2
      continuous_toFun :=
        (rightCommaTotalMapProbe F d).hom.continuous.comp continuous_snd }

private noncomputable def transitionFamilyPath (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    transitionFamilyDomain F d ⟶
      TopCat.pathObject (SSet.toTop.obj (nerve D)) :=
  TopCat.ofHom
    { toFun := compositionPathHomotopy F g
      continuous_toFun := (compositionPathHomotopy F g).continuous }

private theorem transitionFamilyPath_evalZero
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    transitionFamilyPath F g ≫
        TopCat.pathEvalZero (SSet.toTop.obj (nerve D)) =
      transitionFamilyTotal F d ≫ SSet.toTop.map (nerveMapCommonHom.{u, w, v} F) := by
  apply TopCat.ext
  rintro ⟨s, z⟩
  exact compositionPathMapAt_evalZero_apply F g s z

private theorem transitionFamilyPath_evalOne
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    transitionFamilyPath F g ≫
        TopCat.pathEvalOne (SSet.toTop.obj (nerve D)) =
      TopCat.const (X := transitionFamilyDomain F d)
        (SSet.realizedVertex (rightCommaVertex d')) := by
  apply TopCat.ext
  rintro ⟨s, z⟩
  exact compositionPathMapAt_evalOne_apply F g s z

private noncomputable def transitionFiberFamilyMap (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    transitionFamilyDomain F d ⟶
      TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d')) :=
  pullback.lift
    (Limits.prod.lift (transitionFamilyTotal F d)
      (TopCat.const (X := transitionFamilyDomain F d) PUnit.unit))
    (transitionFamilyPath F g)
    (by
      apply Limits.prod.hom_ext
      · simpa [TopCat.pathEndpoints] using
          (transitionFamilyPath_evalZero F g).symm
      · calc
          (Limits.prod.lift (transitionFamilyTotal F d)
                (TopCat.const (X := transitionFamilyDomain F d) PUnit.unit) ≫
              Limits.prod.map (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
                (TopCat.const (X := TopCat.of PUnit)
                  (SSet.realizedVertex (rightCommaVertex d')))) ≫
              Limits.prod.snd =
              TopCat.const (X := transitionFamilyDomain F d)
                (SSet.realizedVertex (rightCommaVertex d')) := by
            rw [Category.assoc, Limits.prod.map_snd]
            rw [← Category.assoc, Limits.prod.lift_snd]
            apply TopCat.ext
            intro z
            rfl
          _ = (transitionFamilyPath F g ≫
              TopCat.pathEndpoints (SSet.toTop.obj (nerve D))) ≫
              Limits.prod.snd := by
            simpa [TopCat.pathEndpoints] using
              (transitionFamilyPath_evalOne F g).symm)

@[reassoc (attr := simp)]
private theorem transitionFiberFamilyMap_toTotal (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    transitionFiberFamilyMap F g ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (SSet.realizedVertex (rightCommaVertex d')) =
      transitionFamilyTotal F d := by
  change transitionFiberFamilyMap F g ≫
      TopCat.homotopyPullbackLeft (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (TopCat.const (SSet.realizedVertex (rightCommaVertex d'))) = _
  rw [transitionFiberFamilyMap, TopCat.homotopyPullbackLeft,
    ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
private theorem transitionFiberFamilyMap_path (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    transitionFiberFamilyMap F g ≫
        TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (SSet.realizedVertex (rightCommaVertex d')) =
      transitionFamilyPath F g := by
  change transitionFiberFamilyMap F g ≫
      TopCat.homotopyPullbackPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (TopCat.const (SSet.realizedVertex (rightCommaVertex d'))) = _
  rw [transitionFiberFamilyMap, TopCat.homotopyPullbackPath,
    pullback.lift_snd]

private theorem transitionFamilySlice_total (F : C ⥤ D) (d : D)
    (s : unitInterval) :
    transitionFamilySlice F d s ≫ transitionFamilyTotal F d =
      rightCommaTotalMapProbe F d := by
  apply TopCat.ext
  intro z
  rfl

private theorem transitionFamilySlice_path (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') (s : unitInterval) :
    transitionFamilySlice F d s ≫ transitionFamilyPath F g =
      compositionPathMapAt F g s := by
  apply TopCat.ext
  intro z
  rfl

private theorem transitionFiberFamilyMap_zero (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    transitionFamilySlice F d 0 ≫ transitionFiberFamilyMap F g =
      rightCommaHomotopyFiberComparisonProbe F d ≫
        homotopyFiberBasepointChangeProbe (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (rightCommaBasepointPathProbe g) := by
  apply TopCat.homotopyPullback_hom_ext
  · calc
      (transitionFamilySlice F d 0 ≫ transitionFiberFamilyMap F g) ≫
          TopCat.homotopyPullbackLeft (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) =
        transitionFamilySlice F d 0 ≫ transitionFamilyTotal F d := by
          rw [Category.assoc, transitionFiberFamilyMap_toTotal]
      _ = rightCommaTotalMapProbe F d :=
        transitionFamilySlice_total F d 0
      _ = (rightCommaHomotopyFiberComparisonProbe F d ≫
          homotopyFiberBasepointChangeProbe (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (rightCommaBasepointPathProbe g)) ≫
          TopCat.homotopyPullbackLeft (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) := by
          rw [Category.assoc, homotopyFiberBasepointChangeProbe_toTotal,
            rightCommaHomotopyFiberComparisonProbe_toTotal]
  · apply TopCat.ext
    intro z
    exact Subsingleton.elim _ _
  · calc
      (transitionFamilySlice F d 0 ≫ transitionFiberFamilyMap F g) ≫
          TopCat.homotopyPullbackPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) =
        transitionFamilySlice F d 0 ≫ transitionFamilyPath F g := by
          rw [Category.assoc, transitionFiberFamilyMap_path]
      _ = compositionPathMapAt F g 0 :=
        transitionFamilySlice_path F g 0
      _ = (rightCommaHomotopyFiberComparisonProbe F d ≫
          homotopyFiberBasepointChangeProbe (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (rightCommaBasepointPathProbe g)) ≫
          TopCat.homotopyPullbackPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) :=
        (comparisonChange_path_eq_compositionPathMapAt_zero F g).symm

private theorem transitionFiberFamilyMap_one (F : C ⥤ D)
    {d d' : D} (g : d ⟶ d') :
    transitionFamilySlice F d 1 ≫ transitionFiberFamilyMap F g =
      SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparisonProbe F d' := by
  apply TopCat.homotopyPullback_hom_ext
  · calc
      (transitionFamilySlice F d 1 ≫ transitionFiberFamilyMap F g) ≫
          TopCat.homotopyPullbackLeft (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) =
        transitionFamilySlice F d 1 ≫ transitionFamilyTotal F d := by
          rw [Category.assoc, transitionFiberFamilyMap_toTotal]
      _ = rightCommaTotalMapProbe F d :=
        transitionFamilySlice_total F d 1
      _ = SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
          rightCommaTotalMapProbe F d' :=
        (rightCommaTotalMapProbe_naturality F g).symm
      _ = (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
          rightCommaHomotopyFiberComparisonProbe F d') ≫
          TopCat.homotopyPullbackLeft (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) := by
          rw [Category.assoc,
            rightCommaHomotopyFiberComparisonProbe_toTotal]
  · apply TopCat.ext
    intro z
    exact Subsingleton.elim _ _
  · calc
      (transitionFamilySlice F d 1 ≫ transitionFiberFamilyMap F g) ≫
          TopCat.homotopyPullbackPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) =
        transitionFamilySlice F d 1 ≫ transitionFamilyPath F g := by
          rw [Category.assoc, transitionFiberFamilyMap_path]
      _ = compositionPathMapAt F g 1 :=
        transitionFamilySlice_path F g 1
      _ = (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
          rightCommaHomotopyFiberComparisonProbe F d') ≫
          TopCat.homotopyPullbackPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
            (TopCat.const
              (SSet.realizedVertex (rightCommaVertex d'))) :=
        (reindexedComparison_path_eq_compositionPathMapAt_one F g).symm

private noncomputable def transitionNaturalityHomotopyProbe
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    ContinuousMap.Homotopy
      (rightCommaHomotopyFiberComparisonProbe F d ≫
        homotopyFiberBasepointChangeProbe (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (rightCommaBasepointPathProbe g)).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparisonProbe F d').hom where
  toFun := (transitionFiberFamilyMap F g).hom
  continuous_toFun := (transitionFiberFamilyMap F g).hom.continuous
  map_zero_left z := by
    have h := ConcreteCategory.congr_hom
      (transitionFiberFamilyMap_zero F g) z
    exact h
  map_one_left z := by
    have h := ConcreteCategory.congr_hom
      (transitionFiberFamilyMap_one F g) z
    exact h

private theorem homotopyFiberBasepointChangeProbe_eq_public
    {X B : TopCat.{u}} (f : X ⟶ B) {b b' : B} (q : Path b b') :
    homotopyFiberBasepointChangeProbe f q =
      TopCat.homotopyFiberBasepointChange f q := by
  rfl

/-! ## Public comparison -/

/-- The canonical map from a realized right-comma category to the homotopy
fiber over the vertex selected by its target object. -/
noncomputable def rightCommaHomotopyFiberComparison
    (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (CostructuredArrow F d)) ⟶
      TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex
          (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌)) :=
  rightCommaHomotopyFiberComparisonProbe F d

/-- The total-space coordinate of the right-comma comparison is realization
of the comma projection. -/
@[reassoc (attr := simp)]
theorem rightCommaHomotopyFiberComparison_toTotal
    (F : C ⥤ D) (d : D) :
    rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (SSet.realizedVertex
            (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌)) =
      SSet.toTop.map (nerveMapCommonHom.{max u w, v, w} (CostructuredArrow.proj F d)) := by
  simpa [rightCommaHomotopyFiberComparison, rightCommaTotalMapProbe,
    rightCommaProjectionFunctorProbe, rightCommaVertex] using
      rightCommaHomotopyFiberComparisonProbe_toTotal F d

/-- The complete compact-open path carried by the right-comma comparison is
the realization of the comma-arrow row homotopy. -/
@[reassoc (attr := simp)]
theorem rightCommaHomotopyFiberComparison_path
    (F : C ⥤ D) (d : D) :
    rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (SSet.realizedVertex
            (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌)) =
      TopCat.ofHom (ContinuousMap.curry
        { toFun := fun z =>
            SSet.realizeHomotopy
                (nerve (CostructuredArrow F d)) (nerve D)
                (nerveMapCommonHom.{u, max v w, 0} (CostructuredArrow.proj F d ⋙ F))
                (nerveMapCommonHom.{u, max v w, 0} ((Functor.const (CostructuredArrow F d)).obj d))
                (SSet.rightCommaArrowNerveHomotopy F d)
                (TopCat.I.homeomorph z.2, z.1)
          continuous_toFun :=
            (SSet.realizeHomotopy
                (nerve (CostructuredArrow F d)) (nerve D)
                (nerveMapCommonHom.{u, max v w, 0} (CostructuredArrow.proj F d ⋙ F))
                (nerveMapCommonHom.{u, max v w, 0} ((Functor.const (CostructuredArrow F d)).obj d))
                (SSet.rightCommaArrowNerveHomotopy F d)).continuous.comp
              ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk
                continuous_fst) }) := by
  unfold rightCommaHomotopyFiberComparison
  change rightCommaHomotopyFiberComparisonProbe F d ≫
      TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (rightCommaVertex d)) = _
  rw [rightCommaHomotopyFiberComparisonProbe_path]
  unfold rightCommaRealizedPathProbe realizedHomotopyPathProbe
  rw [rightCommaArrowNerveHomotopyProbe_eq_public]

/-- A morphism of target objects makes the right-comma comparison natural up
to a jointly continuous homotopy.  The source first changes the selected
basepoint along the realized edge; the target first reindexes the comma
category.

The published underscore spelling is retained for the existing public
transition and full-path callers. This declaration alone is the legacy
exception to the data naming convention. -/
@[nolint defsWithUnderscore]
noncomputable def
    rightCommaHomotopyFiberComparison_transition_naturality_homotopy
    (F : C ⥤ D) {d d' : D} (g : d ⟶ d') :
    ContinuousMap.Homotopy
      (rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberBasepointChange
          (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (TopCat.pathEquiv
            (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk g)))).hom
      (SSet.toTop.map (nerveMap (CostructuredArrow.map g)) ≫
        rightCommaHomotopyFiberComparison F d').hom where
  toFun := (transitionNaturalityHomotopyProbe F g).toFun
  continuous_toFun :=
    (transitionNaturalityHomotopyProbe F g).continuous_toFun
  map_zero_left z := by
    rw [← homotopyFiberBasepointChangeProbe_eq_public]
    exact (transitionNaturalityHomotopyProbe F g).map_zero_left z
  map_one_left z :=
    (transitionNaturalityHomotopyProbe F g).map_one_left z

end SSet

end

public section NativeEqualityComponentPath

universe u v w

open CategoryTheory Opposite Simplicial
open scoped Simplicial

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- An equality structural arrow carries the literal constant path at every interval point. -/
theorem rightCommaHomotopyFiberComparison_vertex_path_const_of_hom_eqToHom
    (F : C ⥤ D) (d : D) (c : CostructuredArrow F d)
    (h : F.obj c.left = d) (hc : c.hom = eqToHom h)
    (t : TopCat.I.{max u v w}) :
    TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (ComposableArrows.mk₀ d :
          (nerve D : SSet.{max u v w}) _⦋0⦌))
        (rightCommaHomotopyFiberComparison.{u, v, w} F d
          (SSet.realizedVertex (ComposableArrows.mk₀ c :
            (nerve (CostructuredArrow F d) : SSet.{max u v w}) _⦋0⦌))) t =
      SSet.realizedVertex (ComposableArrows.mk₀ d :
        (nerve D : SSet.{max u v w}) _⦋0⦌) := by
  let alpha := rightCommaArrowNatTrans.{u, v, w} F d
  have halpha : alpha.app c = eqToHom h := by
    change (rightCommaArrowNatTrans.{u, v, w} F d).app c = eqToHom h
    rw [rightCommaArrowNatTrans_app]
    exact hc
  have hfixed := realizeHomotopy_nerveHomotopyCommonHom_const_vertex_apply.{
    u, max v w, 0} alpha c h halpha (TopCat.I.homeomorph t)
  have hpath := ConcreteCategory.congr_hom
    (rightCommaHomotopyFiberComparison_path.{u, v, w} F d)
    (SSet.realizedVertex (ComposableArrows.mk₀ c :
      (nerve (CostructuredArrow F d) : SSet.{max u v w}) _⦋0⦌))
  have ht := congrArg (fun gamma : TopCat.pathObject
      (SSet.toTop.obj (nerve D : SSet.{max u v w})) => gamma t) hpath
  change TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
      (SSet.realizedVertex (ComposableArrows.mk₀ d :
        (nerve D : SSet.{max u v w}) _⦋0⦌))
      (rightCommaHomotopyFiberComparison.{u, v, w} F d
        (SSet.realizedVertex (ComposableArrows.mk₀ c))) t =
    SSet.realizeHomotopy (nerve (CostructuredArrow F d)) (nerve D)
      (nerveMapCommonHom.{u, max v w, 0} (CostructuredArrow.proj F d ⋙ F))
      (nerveMapCommonHom.{u, max v w, 0}
        ((Functor.const (CostructuredArrow F d)).obj d))
      (rightCommaArrowNerveHomotopy.{u, v, w} F d)
      (TopCat.I.homeomorph t, SSet.realizedVertex (ComposableArrows.mk₀ c)) at ht
  exact ht.trans (hfixed.trans
    (congrArg (fun x : D => SSet.realizedVertex
      (X := (nerve D : SSet.{max u v w})) (ComposableArrows.mk₀ x)) h))

end SSet

end NativeEqualityComponentPath
