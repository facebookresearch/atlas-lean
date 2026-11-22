/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RowRestriction

/-!
# The box product and its two pullback-Hom functors

For simplicial sets `A` and `K`, `boxProduct` is the literal simplicial
space with bidegree `(m,n)` equal to `A_m × K_n`.  This module constructs
both divisions of that box product:

* `boxLeftDivisionFunctor` is the source left division `A \ X`;
* `rowPowerBifunctor` is the source right division `X / K`, and is
  definitionally compatible with the existing `rowPowerFunctor`.

The two parametrized adjunctions are joined into equivalences of original
commutative squares and lift structures.  The canonical pushout and pullback
objects, both pullback projections, and both filler equations remain visible.
This is the model independent two-variable calculus of Joyal--Tierney,
Proposition 2.1 and Appendix Proposition 7.6.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner

namespace SimplicialSpace

/-- The designated discrete-inner embedding of an outer simplicial set. -/
abbrev discreteInnerFunctor : SSet.{u} ⥤ SimplicialSpace.{u} :=
  SSet.simplicialSpaceDiscrete.{u} ⋙ ofSimplicialObject.{u}

/-- The literal box product `A ⊠ K`, with bidegree `A_m × K_n`. -/
abbrev boxProduct : SSet.{u} ⥤ SSet.{u} ⥤ SimplicialSpace.{u} :=
  discreteInnerFunctor.{u} ⋙ innerTensorBifunctor.{u}

/-- The box product retains the literal product carrier in every bidegree. -/
theorem boxProduct_obj_obj (A B : SSet.{u})
    (m n : SimplexCategoryᵒᵖ) :
    (((boxProduct.obj A).obj B).diagram.obj m).obj n =
      (A.obj m × B.obj n) := rfl

/-- A map in the outer factor acts only on the outer coordinate. -/
theorem boxProduct_map_left_app {A A' : SSet.{u}} (a : A ⟶ A')
    (B : SSet.{u}) (m n : SimplexCategoryᵒᵖ)
    (x : A.obj m × B.obj n) :
    ((((boxProduct.map a).app B).hom.app m).app n) x =
      (a.app m x.1, x.2) := rfl

/-- A map in the inner factor acts only on the inner coordinate. -/
theorem boxProduct_map_right_app (A : SSet.{u})
    {B B' : SSet.{u}} (b : B ⟶ B')
    (m n : SimplexCategoryᵒᵖ) (x : A.obj m × B.obj n) :
    ((((boxProduct.obj A).map b).hom.app m).app n) x =
      (x.1, b.app n x.2) := rfl

/-- The source-left division bifunctor `(A, X) ↦ A \ X`. -/
abbrev boxLeftDivisionFunctor : SSet.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  discreteInnerFunctor.{u}.op ⋙ innerHomFunctor.{u}

/-- The box product is parametrically left adjoint to source-left division. -/
noncomputable def boxProductLeftAdjunction₂ :
    boxProduct.{u} ⊣₂ boxLeftDivisionFunctor.{u} :=
  ParametrizedAdjunction.mk'
    (fun A => innerTensorHomAdjunction₂.{u}.adj (discreteInner A))
    (by
      intro A B a K X f
      exact innerTensorHomAdjunction₂.{u}.homEquiv_naturality_one
        (discreteInnerMap a) f)

/-- The canonical pullback square underlying the source-left pullback-Hom `⟨v \ f⟩`. -/
abbrev boxLeftPullbackHomSquare {A B : SSet.{u}} (v : A ⟶ B)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :=
  Functor.PullbackObjObj.ofHasPullback boxLeftDivisionFunctor.{u} v f

/-- The source-left pullback-Hom arrow `⟨v \ f⟩`. -/
abbrev boxLeftPullbackHom {A B : SSet.{u}} (v : A ⟶ B)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    ((boxLeftDivisionFunctor.obj (op B)).obj X) ⟶ (boxLeftPullbackHomSquare v f).pt :=
  (boxLeftPullbackHomSquare v f).π

/-- The first projection of the source-left pullback-Hom is restriction of the source. -/
@[reassoc] theorem boxLeftPullbackHom_fst {A B : SSet.{u}} (v : A ⟶ B)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    boxLeftPullbackHom v f ≫ (boxLeftPullbackHomSquare v f).fst =
      (boxLeftDivisionFunctor.map v.op).app X :=
  (boxLeftPullbackHomSquare v f).π_fst

/-- The second projection of the source-left pullback-Hom is the map on the `B`-division. -/
@[reassoc] theorem boxLeftPullbackHom_snd {A B : SSet.{u}} (v : A ⟶ B)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    boxLeftPullbackHom v f ≫ (boxLeftPullbackHomSquare v f).snd =
      (boxLeftDivisionFunctor.obj (op B)).map f :=
  (boxLeftPullbackHomSquare v f).π_snd

end SimplicialSpace

namespace SimplicialSpace

/-- Transposition exchanges the box factors, using the product symmetry in every bidegree. -/
noncomputable def boxTransposeIso (A B : SSet.{u}) :
    HorizontalModel.transposeSpaceEquivalence.{u}.functor.obj
      ((boxProduct.obj A).obj B) ≅
      (boxProduct.obj B).obj A := by
  apply InducedCategory.isoMk
  refine NatIso.ofComponents (fun m => ?_) ?_
  · exact
      { hom :=
          { app := fun n => ↾fun x : A.obj n × B.obj m => (x.2, x.1)
            naturality := by
              intro n n' a
              ext x
              rfl }
        inv :=
          { app := fun n => ↾fun x : B.obj m × A.obj n => (x.2, x.1)
            naturality := by
              intro n n' a
              ext x
              rfl }
        hom_inv_id := by
          ext n x
          rfl
        inv_hom_id := by
          ext n x
          rfl }
  · intro m m' a
    ext n x
    rfl

end SimplicialSpace

namespace SimplicialSpace

/-- The box-factor transposition is natural in the first factor. -/
noncomputable def boxTransposeNatIso (B : SSet.{u}) :
    boxProduct.{u}.flip.obj B ⋙
        HorizontalModel.transposeSpaceEquivalence.{u}.functor ≅
      boxProduct.{u}.obj B :=
  NatIso.ofComponents (fun A => boxTransposeIso A B) (by
    intro A A' a
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    apply NatTrans.ext
    funext n
    ext x
    rfl)

end SimplicialSpace

namespace SimplicialSpace

/-- The source-right division bifunctor `(K, X) ↦ X / K`. -/
abbrev rowPowerBifunctor :
    SSet.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  boxLeftDivisionFunctor.{u} ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u}
      SimplicialSpace.{u} SSet.{u}).obj
        HorizontalModel.transposeSpaceEquivalence.{u}.functor

/-- The bifunctorial right division is definitionally the existing row-power functor. -/
theorem rowPowerBifunctor_obj (B : SSet.{u}) :
    rowPowerBifunctor.{u}.obj (op B) = rowPowerFunctor.{u} B := rfl

/-- Contravariance of the bifunctorial right division is the existing row restriction. -/
theorem rowPowerBifunctor_map_app {B B' : SSet.{u}} (b : B ⟶ B')
    (X : SimplicialSpace.{u}) :
    (rowPowerBifunctor.{u}.map b.op).app X = rowRestriction b X := rfl

/-- The Hom equivalence exhibiting `X / B` as the right division of the box product. -/
noncomputable def boxRightHomEquiv (A B : SSet.{u})
    (X : SimplicialSpace.{u}) :
    ((boxProduct.obj A).obj B ⟶ X) ≃
      (A ⟶ (rowPowerBifunctor.obj (op B)).obj X) :=
  HorizontalModel.transposeSpaceEquivalence.{u}.fullyFaithfulFunctor.homEquiv |>.trans
    ((boxTransposeIso A B).homCongr (Iso.refl _)) |>.trans
      (innerTensorHomEquiv A (discreteInner B)
        (HorizontalModel.transposeSpaceEquivalence.functor.obj X))

end SimplicialSpace

namespace SimplicialSpace

/-- The right-division Hom equivalence transposes the map, swaps the box factors, and curries. -/
theorem boxRightHomEquiv_apply (A B : SSet.{u})
    (X : SimplicialSpace.{u}) (f : (boxProduct.obj A).obj B ⟶ X) :
    boxRightHomEquiv A B X f =
      innerTensorHomEquiv A (discreteInner B)
        (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
        ((boxTransposeIso A B).inv ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map f) := by
  rfl

/-- Naturality of inverse box transposition in the outer factor. -/
@[reassoc]
theorem boxTransposeIso_inv_naturality_outer {A A' B : SSet.{u}}
    (a : A ⟶ A') :
    (boxProduct.obj B).map a ≫ (boxTransposeIso A' B).inv =
      (boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map
          ((boxProduct.flip.obj B).map a) := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext m
  apply NatTrans.ext
  funext n
  ext x
  rfl

/-- Naturality of inverse box transposition in the inner factor. -/
@[reassoc]
theorem boxTransposeIso_inv_naturality_inner {A B B' : SSet.{u}}
    (b : B ⟶ B') :
    (boxProduct.map b).app A ≫ (boxTransposeIso A B').inv =
      (boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map
          ((boxProduct.obj A).map b) := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext m
  apply NatTrans.ext
  funext n
  ext x
  rfl

/-- Naturality of the right-division Hom equivalence in the outer source. -/
@[reassoc]
theorem boxRightHomEquiv_naturality_outer {A A' B : SSet.{u}}
    (a : A ⟶ A') (X : SimplicialSpace.{u})
    (f : (boxProduct.obj A').obj B ⟶ X) :
    boxRightHomEquiv A B X
        ((boxProduct.flip.obj B).map a ≫ f) =
      a ≫ boxRightHomEquiv A' B X f := by
  change innerTensorHomEquiv A (discreteInner B)
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
      ((boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map
          ((boxProduct.flip.obj B).map a ≫ f)) =
    a ≫ innerTensorHomEquiv A' (discreteInner B)
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
      ((boxTransposeIso A' B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map f)
  rw [Functor.map_comp]
  have hpre :
      (boxTransposeIso A B).inv ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map
            ((boxProduct.flip.obj B).map a) ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map f =
        (boxProduct.obj B).map a ≫ (boxTransposeIso A' B).inv ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map f := by
    rw [← Category.assoc, ← boxTransposeIso_inv_naturality_outer a,
      Category.assoc]
  rw [hpre]
  exact innerTensorHomEquiv_scalar a (discreteInner B)
    (HorizontalModel.transposeSpaceEquivalence.functor.obj X) _

set_option maxHeartbeats 800000 in
/-- Naturality of the right-division Hom equivalence in the target space. -/
@[reassoc]
theorem boxRightHomEquiv_naturality_target (A B : SSet.{u})
    {X Y : SimplicialSpace.{u}} (f : (boxProduct.obj A).obj B ⟶ X)
    (g : X ⟶ Y) :
    boxRightHomEquiv A B Y (f ≫ g) =
      boxRightHomEquiv A B X f ≫ (rowPowerFunctor B).map g := by
  change innerTensorHomEquiv A (discreteInner B)
      (HorizontalModel.transposeSpaceEquivalence.functor.obj Y)
      ((boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map (f ≫ g)) =
    innerTensorHomEquiv A (discreteInner B)
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
      ((boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map f) ≫
      (innerHomFunctor.obj (op (discreteInner B))).map
        (HorizontalModel.transposeSpaceEquivalence.functor.map g)
  rw [Functor.map_comp]
  simpa only [← Category.assoc] using
    innerTensorHomEquiv_target A (discreteInner B)
      (HorizontalModel.transposeSpaceEquivalence.functor.map g)
      ((boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map f)

/-- Naturality of the right-division Hom equivalence in the inner parameter. -/
@[reassoc]
theorem boxRightHomEquiv_naturality_inner {A B B' : SSet.{u}}
    (b : B ⟶ B') (X : SimplicialSpace.{u})
    (f : (boxProduct.obj A).obj B' ⟶ X) :
    boxRightHomEquiv A B X ((boxProduct.obj A).map b ≫ f) =
      boxRightHomEquiv A B' X f ≫
        (rowPowerBifunctor.map b.op).app X := by
  change innerTensorHomEquiv A (discreteInner B)
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
      ((boxTransposeIso A B).inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map
          ((boxProduct.obj A).map b ≫ f)) =
    innerTensorHomEquiv A (discreteInner B')
      (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
      ((boxTransposeIso A B').inv ≫
        HorizontalModel.transposeSpaceEquivalence.functor.map f) ≫
      (innerHomFunctor.map (discreteInnerMap b).op).app
        (HorizontalModel.transposeSpaceEquivalence.functor.obj X)
  rw [Functor.map_comp]
  have hpre :
      (boxTransposeIso A B).inv ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map
            ((boxProduct.obj A).map b) ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map f =
        (boxProduct.map b).app A ≫ (boxTransposeIso A B').inv ≫
          HorizontalModel.transposeSpaceEquivalence.functor.map f := by
    rw [← Category.assoc, ← boxTransposeIso_inv_naturality_inner b,
      Category.assoc]
  rw [hpre]
  exact innerTensorHomEquiv_source (discreteInnerMap b) A
    (HorizontalModel.transposeSpaceEquivalence.functor.obj X) _

private def boxRightHomCore (B : SSet.{u}) :
    Adjunction.CoreHomEquiv (boxProduct.{u}.flip.obj B)
      (rowPowerBifunctor.{u}.obj (op B)) where
  homEquiv := fun A X => boxRightHomEquiv A B X
  homEquiv_naturality_left_symm := by
    intro A A' X a g
    apply (boxRightHomEquiv A B X).injective
    rw [Equiv.apply_symm_apply, boxRightHomEquiv_naturality_outer,
      Equiv.apply_symm_apply]
  homEquiv_naturality_right := by
    intro A X Y f g
    exact boxRightHomEquiv_naturality_target A B f g

/-- For fixed inner factor, the box product is left adjoint to right division. -/
noncomputable def boxProductRightAdjunction (B : SSet.{u}) :
    boxProduct.{u}.flip.obj B ⊣ rowPowerBifunctor.{u}.obj (op B) :=
  Adjunction.mkOfHomEquiv (boxRightHomCore B)

/-- The fixed-factor adjunction uses the canonical right-division Hom equivalence. -/
@[simp]
theorem boxProductRightAdjunction_homEquiv (A B : SSet.{u})
    (X : SimplicialSpace.{u}) :
    (boxProductRightAdjunction B).homEquiv A X =
      boxRightHomEquiv A B X := by
  simp [boxProductRightAdjunction, boxRightHomCore]
  rfl

/-- The parametrized adjunction between the flipped box product and right division. -/
noncomputable def boxProductRightAdjunction₂ :
    boxProduct.{u}.flip ⊣₂ rowPowerBifunctor.{u} :=
  ParametrizedAdjunction.mk' boxProductRightAdjunction
    (by
      intro B B' b A X f
      simp only [boxProductRightAdjunction,
        Adjunction.mkOfHomEquiv_homEquiv]
      exact boxRightHomEquiv_naturality_inner b X f)

end SimplicialSpace

namespace SimplicialSpace

private abbrev rowPullbackHomSquareForBox {K L : SSet.{u}} (v : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :=
  Functor.PullbackObjObj.ofHasPullback rowPowerBifunctor.{u} v f

/-- The canonical pullback-Hom of `rowPowerBifunctor` is the existing row pullback-Hom. -/
theorem rowPullbackHom_eq_bifunctorPullback {K L : SSet.{u}}
    (v : K ⟶ L) {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    (Functor.PullbackObjObj.ofHasPullback
      rowPowerBifunctor.{u} v f).π = rowPullbackHom v f := rfl


end SimplicialSpace

namespace SimplicialSpace

/-- The canonical pushout-product square of two simplicial-set maps under the literal box
product. -/
noncomputable abbrev boxPushoutProductSquare
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L) :=
  Functor.PushoutObjObj.ofHasPushout boxProduct.{u} v u

/-- Commutative squares against caller-supplied right and left pullback-Hom
packets are naturally equivalent through one supplied box pushout. -/
noncomputable def boxPullbackHomArrowEquivOf
    {A B K L : SSet.{u}} {v : A ⟶ B} {u : K ⟶ L}
    {X Y : SimplicialSpace.{u}} {f : X ⟶ Y}
    (pp : boxProduct.{u}.PushoutObjObj v u)
    (rowSq : rowPowerBifunctor.{u}.PullbackObjObj u f)
    (leftSq : boxLeftDivisionFunctor.{u}.PullbackObjObj v f) :
    (Arrow.mk v ⟶ Arrow.mk rowSq.π) ≃
      (Arrow.mk u ⟶ Arrow.mk leftSq.π) :=
  ((boxProductRightAdjunction₂.{u}.arrowHomEquiv
      pp.flip rowSq).symm).trans
    (boxProductLeftAdjunction₂.{u}.arrowHomEquiv pp leftSq)

/-- Commutative squares against the two canonical pullback-Homs are naturally equivalent. -/
noncomputable def boxPullbackHomArrowEquiv
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    (Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) ≃
      (Arrow.mk u ⟶ Arrow.mk (boxLeftPullbackHom v f)) :=
  boxPullbackHomArrowEquivOf (boxPushoutProductSquare v u)
    (rowPullbackHomSquareForBox u f) (boxLeftPullbackHomSquare v f)

/-- Two-variable lifting for caller-supplied box, right pullback, and left
pullback packets. -/
theorem box_hasLiftingProperty_iff_of
    {A B K L : SSet.{u}} {v : A ⟶ B} {u : K ⟶ L}
    {X Y : SimplicialSpace.{u}} {f : X ⟶ Y}
    (pp : boxProduct.{u}.PushoutObjObj v u)
    (rowSq : rowPowerBifunctor.{u}.PullbackObjObj u f)
    (leftSq : boxLeftDivisionFunctor.{u}.PullbackObjObj v f) :
    HasLiftingProperty v rowSq.π ↔ HasLiftingProperty u leftSq.π :=
  (boxProductRightAdjunction₂.{u}.hasLiftingProperty_iff
    pp.flip rowSq).symm.trans
      (boxProductLeftAdjunction₂.{u}.hasLiftingProperty_iff pp leftSq)

/-- Two-variable lifting for the literal box product, retaining both canonical
pullback-Hom arrows. -/
theorem box_hasLiftingProperty_iff
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    HasLiftingProperty v (rowPullbackHom u f) ↔
      HasLiftingProperty u (boxLeftPullbackHom v f) :=
  box_hasLiftingProperty_iff_of (boxPushoutProductSquare v u)
    (rowPullbackHomSquareForBox u f) (boxLeftPullbackHomSquare v f)

end SimplicialSpace

namespace SimplicialSpace

private def liftStructEquivOfEq {C : Type*} [Category* C]
    {f g : Arrow C} {sq sq' : f ⟶ g} (h : sq = sq') :
    Arrow.LiftStruct sq ≃ Arrow.LiftStruct sq' := by
  subst h
  exact Equiv.refl _

/-- Fillers for corresponding squares against caller-supplied right and left
pullback-Hom packets are equivalent. -/
noncomputable def boxPullbackHomLiftStructEquivOf
    {A B K L : SSet.{u}} {v : A ⟶ B} {u : K ⟶ L}
    {X Y : SimplicialSpace.{u}} {f : X ⟶ Y}
    (pp : boxProduct.{u}.PushoutObjObj v u)
    (rowSq : rowPowerBifunctor.{u}.PullbackObjObj u f)
    (leftSq : boxLeftDivisionFunctor.{u}.PullbackObjObj v f)
    (sq : Arrow.mk v ⟶ Arrow.mk rowSq.π) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (boxPullbackHomArrowEquivOf pp rowSq leftSq sq) := by
  let eR := boxProductRightAdjunction₂.{u}.arrowHomEquiv pp.flip rowSq
  let common := eR.symm sq
  let hR : eR common = sq := eR.apply_symm_apply sq
  let fromCommon : Arrow.LiftStruct common ≃ Arrow.LiftStruct sq :=
    (boxProductRightAdjunction₂.{u}.liftStructEquiv pp.flip rowSq common).trans
      (liftStructEquivOfEq hR)
  exact fromCommon.symm.trans
    (boxProductLeftAdjunction₂.{u}.liftStructEquiv pp leftSq common)

/-- Fillers for corresponding canonical right and left box pullback-Hom squares
are equivalent. -/
noncomputable def boxPullbackHomLiftStructEquiv
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (boxPullbackHomArrowEquiv v u f sq) :=
  boxPullbackHomLiftStructEquivOf (boxPushoutProductSquare v u)
    (rowPullbackHomSquareForBox u f) (boxLeftPullbackHomSquare v f) sq

end SimplicialSpace

namespace SimplicialSpace

/-- The common pushout-product square corresponding to a square against a
caller-supplied right pullback-Hom packet. -/
noncomputable def boxPullbackHomCommonSquareOf
    {A B K L : SSet.{u}} {v : A ⟶ B} {u : K ⟶ L}
    {X Y : SimplicialSpace.{u}} {f : X ⟶ Y}
    (pp : boxProduct.{u}.PushoutObjObj v u)
    (rowSq : rowPowerBifunctor.{u}.PullbackObjObj u f)
    (sq : Arrow.mk v ⟶ Arrow.mk rowSq.π) :
    Arrow.mk pp.ι ⟶ Arrow.mk f :=
  (boxProductRightAdjunction₂.{u}.arrowHomEquiv pp.flip rowSq).symm sq

/-- The common pushout-product square corresponding to a right pullback-Hom square. -/
noncomputable def boxPullbackHomCommonSquare
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    Arrow.mk (boxPushoutProductSquare v u).ι ⟶ Arrow.mk f :=
  boxPullbackHomCommonSquareOf (boxPushoutProductSquare v u)
    (rowPullbackHomSquareForBox u f) sq

/-- The left side of the corresponding left pullback-Hom square is the first curried pushout leg. -/
theorem boxPullbackHomArrowEquiv_apply_left
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    (boxPullbackHomArrowEquiv v u f sq).left =
      boxProductLeftAdjunction₂.{u}.homEquiv
        ((boxPushoutProductSquare v u).inl ≫
          (boxPullbackHomCommonSquare v u f sq).left) := by
  rfl

/-- The right side of the corresponding square retains the first pullback projection. -/
@[reassoc]
theorem boxPullbackHomArrowEquiv_apply_right_fst
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    (boxPullbackHomArrowEquiv v u f sq).right ≫
        (boxLeftPullbackHomSquare v f).fst =
      boxProductLeftAdjunction₂.{u}.homEquiv
        ((boxPushoutProductSquare v u).inr ≫
          (boxPullbackHomCommonSquare v u f sq).left) := by
  exact ParametrizedAdjunction.arrowHomEquiv_apply_right_fst
    boxProductLeftAdjunction₂ (boxPushoutProductSquare v u)
      (boxLeftPullbackHomSquare v f)
      (boxPullbackHomCommonSquare v u f sq)

/-- The right side of the corresponding square retains the second pullback projection. -/
@[reassoc]
theorem boxPullbackHomArrowEquiv_apply_right_snd
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    (boxPullbackHomArrowEquiv v u f sq).right ≫
        (boxLeftPullbackHomSquare v f).snd =
      boxProductLeftAdjunction₂.{u}.homEquiv
        (boxPullbackHomCommonSquare v u f sq).right := by
  exact ParametrizedAdjunction.arrowHomEquiv_apply_right_snd
    boxProductLeftAdjunction₂ (boxPushoutProductSquare v u)
      (boxLeftPullbackHomSquare v f)
      (boxPullbackHomCommonSquare v u f sq)

/-- The transported filler satisfies the original left triangle equation. -/
@[simp]
theorem boxPullbackHomLiftStructEquiv_fac_left
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f))
    (l : Arrow.LiftStruct sq) :
    u ≫ (boxPullbackHomLiftStructEquiv v u f sq l).l =
      (boxPullbackHomArrowEquiv v u f sq).left :=
  (boxPullbackHomLiftStructEquiv v u f sq l).fac_left

/-- The transported filler satisfies the original right triangle equation. -/
theorem boxPullbackHomLiftStructEquiv_fac_right
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f))
    (l : Arrow.LiftStruct sq) :
    (boxPullbackHomLiftStructEquiv v u f sq l).l ≫
        boxLeftPullbackHom v f =
      (boxPullbackHomArrowEquiv v u f sq).right :=
  (boxPullbackHomLiftStructEquiv v u f sq l).fac_right

end SimplicialSpace

namespace SimplicialSpace

/-- The common square on the second pushout leg is the uncurried upper map. -/
@[reassoc]
theorem boxPushoutProduct_inr_commonSquare
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    (boxPushoutProductSquare v u).inr ≫
        (boxPullbackHomCommonSquare v u f sq).left =
      boxProductRightAdjunction₂.{u}.homEquiv.symm sq.left := by
  exact ParametrizedAdjunction.inl_arrowHomEquiv_symm_apply_left
    boxProductRightAdjunction₂ (boxPushoutProductSquare v u).flip
      (rowPullbackHomSquareForBox u f) sq

/-- The common square on the first pushout leg is the uncurried first pullback projection. -/
@[reassoc]
theorem boxPushoutProduct_inl_commonSquare
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    (boxPushoutProductSquare v u).inl ≫
        (boxPullbackHomCommonSquare v u f sq).left =
      boxProductRightAdjunction₂.{u}.homEquiv.symm
        (sq.right ≫ (rowPullbackHomSquareForBox u f).fst) := by
  exact ParametrizedAdjunction.inr_arrowHomEquiv_symm_apply_left
    boxProductRightAdjunction₂ (boxPushoutProductSquare v u).flip
      (rowPullbackHomSquareForBox u f) sq

/-- The target side of the common square is the uncurried second pullback projection. -/
@[simp]
theorem boxPullbackHomCommonSquare_right
    {A B K L : SSet.{u}} (v : A ⟶ B) (u : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (sq : Arrow.mk v ⟶ Arrow.mk (rowPullbackHom u f)) :
    (boxPullbackHomCommonSquare v u f sq).right =
      boxProductRightAdjunction₂.{u}.homEquiv.symm
        (sq.right ≫ (rowPullbackHomSquareForBox u f).snd) := by
  exact ParametrizedAdjunction.arrowHomEquiv_symm_apply_right
    boxProductRightAdjunction₂ (boxPushoutProductSquare v u).flip
      (rowPullbackHomSquareForBox u f) sq

end SimplicialSpace
