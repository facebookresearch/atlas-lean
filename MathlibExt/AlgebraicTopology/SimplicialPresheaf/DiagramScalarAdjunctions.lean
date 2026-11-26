/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarTensorEndLifting
import MathlibExt.CategoryTheory.Products.LocallySmall
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Original product-site scalar adjunctions

The actual free/cofree diagrams, original Hom labels and full scalar mapping
ends retain every original transpose and naturality; no model/locality/weak outcome is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u vD wD vJ wJ

open CategoryTheory CategoryTheory.Limits Opposite SimplicialPresheaf

namespace SimplicialPresheaf.LocalizationDiagram

variable {D : Type wD} [Category.{vD} D]
  {J : Type wJ} [Category.{vJ} J]

/-- Literal currying of the ordered original product/opposite site. -/
@[reducible]
def curry : SimplicialPresheaf.{u} (D × J) ≌
    (Dᵒᵖ ⥤ SimplicialPresheaf.{u} J) :=
  (prodOpEquiv D (D := J)).congrLeft.trans CategoryTheory.Functor.currying.symm

/-- The original component value, retaining D then J and then inner simplex. -/
theorem curry_obj (X : SimplicialPresheaf.{u} (D × J)) (d : D) (j : J) :
    (((curry (D := D) (J := J)).functor.obj X).obj (op d)).obj (op j) =
      X.obj (op (d, j)) := rfl

/-- Evaluation at the prescribed original D object on the literal flat site. -/
@[reducible]
def evaluation (d : D) : SimplicialPresheaf.{u} (D × J) ⥤ SimplicialPresheaf.{u} J :=
  (curry (D := D) (J := J)).functor ⋙
    (CategoryTheory.evaluation Dᵒᵖ (SimplicialPresheaf.{u} J)).obj (op d)

variable [LocallySmall.{u} D]

/-- Original Hom labels have their actual coproduct shapes in the presheaf coefficient. -/
local instance homCoproducts :
    ∀ a b : Dᵒᵖ, HasCoproductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
  fun a b => hasCoproductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)

/-- Original Hom labels have their actual product shapes in the presheaf coefficient. -/
local instance homProducts :
    ∀ a b : Dᵒᵖ, HasProductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
  fun a b => hasProductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)

/-- The actual free diagram, with all original Hom labels kept in the coproduct. -/
@[reducible]
def free (d : D) : SimplicialPresheaf.{u} J ⥤ SimplicialPresheaf.{u} (D × J) := by
  letI : ∀ a b : Dᵒᵖ,
      HasCoproductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
    fun a b => hasCoproductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)
  exact evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d) ⋙
    (curry (D := D) (J := J)).inverse

/-- The actual cofree diagram uses products over original d→e operators. -/
@[reducible]
def cofree (d : D) : SimplicialPresheaf.{u} J ⥤ SimplicialPresheaf.{u} (D × J) := by
  letI : ∀ a b : Dᵒᵖ,
      HasProductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
    fun a b => hasProductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)
  exact evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op d) ⋙
    (curry (D := D) (J := J)).inverse

/-- Both ordinary Hom directions are the native free/evaluation adjunction. -/
def freeAdjunction (d : D) :
    free (J := J) d ⊣ evaluation (J := J) d := by
  letI : ∀ a b : Dᵒᵖ,
      HasCoproductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
    fun a b => hasCoproductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)
  exact (evaluationAdjunctionRight (SimplicialPresheaf.{u} J) (op d)).comp
    (curry (D := D) (J := J)).symm.toAdjunction

/-- Both ordinary Hom directions are the native evaluation/cofree adjunction. -/
def cofreeAdjunction (d : D) :
    evaluation (J := J) d ⊣ cofree (J := J) d := by
  letI : ∀ a b : Dᵒᵖ,
      HasProductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
    fun a b => hasProductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)
  exact (curry (D := D) (J := J)).toAdjunction.comp
    (evaluationAdjunctionLeft (SimplicialPresheaf.{u} J) (op d))

/-- Original scalar tensor and product-site evaluation commute at every component. -/
def evaluationTensorIso (d : D) (A : SimplicialPresheaf.{u} (D × J)) :
    scalarTensor.obj A ⋙ evaluation (J := J) d ≅
      scalarTensor.obj ((evaluation (J := J) d).obj A) :=
  NatIso.ofComponents (fun K => Iso.refl _) (by
    intro K L k
    ext j n z
    rfl)

variable [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J]

/-- The original two Hom-smallness bounds give the same product-site bound. -/
instance locallySmallProduct : LocallySmall.{u} (D × J) :=
  CategoryTheory.Prod.locallySmall D J

/-- Evaluation commutes with the actual scalar cotensor, in the original order. -/
def evaluationCotensorIso (d : D) (K : SSet.{u}) :
    (scalarCotensor (D := D × J)).obj (op K) ⋙ evaluation (J := J) d ≅
      evaluation (J := J) d ⋙ (scalarCotensor (D := J)).obj (op K) :=
  NatIso.ofComponents (fun A => Iso.refl _) (by intro A B a; ext j n q; rfl)

omit [LocallySmall.{u} D] [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Both source and scalar maps retain the strict original evaluation/tensor square. -/
theorem evaluationTensorIso_laws (d : D)
    {A B : SimplicialPresheaf.{u} (D × J)} (a : A ⟶ B)
    {K L : SSet.{u}} (k : K ⟶ L) :
    (evaluation (J := J) d).map ((scalarTensor.map a).app K) ≫
        (evaluationTensorIso (J := J) d B).hom.app K =
      (evaluationTensorIso (J := J) d A).hom.app K ≫
        (scalarTensor.map ((evaluation (J := J) d).map a)).app K ∧
    (evaluation (J := J) d).map ((scalarTensor.obj A).map k) ≫
        (evaluationTensorIso (J := J) d A).hom.app L =
      (evaluationTensorIso (J := J) d A).hom.app K ≫
        (scalarTensor.obj ((evaluation (J := J) d).obj A)).map k := by
  constructor <;> ext j n q <;> rfl
/-- The original Hom-indexed coproduct comparison preserves tensoring in the coefficient presheaf
category. -/
def tensorCoproductIso (d : D) (e : Dᵒᵖ)
    (A : SimplicialPresheaf.{u} J) (K : SSet.{u}) :
    (∐ fun _ : op d ⟶ e => (scalarTensor.obj A).obj K) ≅
      (scalarTensorFixed (D := J) K).obj (∐ fun _ : op d ⟶ e => A) := by
  let : HasCoproductsOfShape (op d ⟶ e) (SimplicialPresheaf.{u} J) :=
    hasCoproductsOfShape_of_small (SimplicialPresheaf.{u} J) (op d ⟶ e)
  let : (scalarTensorFixed (D := J) K).IsLeftAdjoint :=
    ⟨_, ⟨scalarTensorCotensorAdjunction (D := J) K⟩⟩
  exact (PreservesCoproduct.iso (scalarTensorFixed (D := J) K)
    (fun _ : op d ⟶ e => A)).symm
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Each original coproduct injection is carried to the tensor of that same injection. -/
theorem tensorCoproductIso_hom_ι (d : D) (e : Dᵒᵖ)
    (A : SimplicialPresheaf.{u} J) (K : SSet.{u}) (h : op d ⟶ e) :
    Sigma.ι (fun _ : op d ⟶ e => (scalarTensor.obj A).obj K) h ≫
        (tensorCoproductIso (J := J) d e A K).hom =
      (scalarTensorFixed (D := J) K).map (Sigma.ι (fun _ : op d ⟶ e => A) h) := by
  simp only [tensorCoproductIso, Iso.symm_hom, PreservesCoproduct.inv_hom]
  change Sigma.ι (fun _ : op d ⟶ e => (scalarTensorFixed (D := J) K).obj A) h ≫
      sigmaComparison (scalarTensorFixed (D := J) K) (fun _ : op d ⟶ e => A) = _
  exact ι_comp_sigmaComparison _ _ h
/-- The original free coefficient diagram commutes with fixed-scalar tensoring at every object. -/
@[reducible]
def freeTensorNestedIso (d : D) (A : SimplicialPresheaf.{u} J)
    (K : SSet.{u}) :
    (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj
        ((scalarTensor.obj A).obj K) ≅
      (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A ⋙
        scalarTensorFixed (D := J) K := by
  let : ∀ a b : Dᵒᵖ, HasCoproductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
    fun a b => hasCoproductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)
  refine NatIso.ofComponents (fun e => tensorCoproductIso (J := J) d e A K) ?_
  intro e e' f
  apply Sigma.hom_ext
  intro h
  change Sigma.ι (fun _ : op d ⟶ e => (scalarTensor.obj A).obj K) h ≫
      Sigma.desc (fun g : op d ⟶ e =>
        Sigma.ι (fun _ : op d ⟶ e' => (scalarTensor.obj A).obj K) (g ≫ f)) ≫
          (tensorCoproductIso (J := J) d e' A K).hom =
    Sigma.ι (fun _ : op d ⟶ e => (scalarTensor.obj A).obj K) h ≫
      (tensorCoproductIso (J := J) d e A K).hom ≫
        (scalarTensorFixed (D := J) K).map
          (Sigma.desc (fun g : op d ⟶ e => Sigma.ι (fun _ : op d ⟶ e' => A) (g ≫ f)))
  rw [← Category.assoc, colimit.ι_desc, Cofan.mk_ι_app, tensorCoproductIso_hom_ι]
  rw [← Category.assoc, tensorCoproductIso_hom_ι]
  have hcomp : Sigma.ι (fun _ : op d ⟶ e => A) h ≫
      Sigma.desc (fun g : op d ⟶ e => Sigma.ι (fun _ : op d ⟶ e' => A) (g ≫ f)) =
        Sigma.ι (fun _ : op d ⟶ e' => A) (h ≫ f) := by
    simp only [colimit.ι_desc, Cofan.mk_ι_app]
  exact (congrArg ((scalarTensorFixed (D := J) K).map) hcomp).symm.trans
    ((scalarTensorFixed (D := J) K).map_comp _ _)
/-- The actual inverse currying equivalence preserves fixed-scalar tensoring and its original
diagram operators. -/
@[reducible]
def uncurryTensorIso (K : SSet.{u}) (X : Dᵒᵖ ⥤ SimplicialPresheaf.{u} J) :
    (curry (D := D) (J := J)).inverse.obj (X ⋙ scalarTensorFixed (D := J) K) ≅
      (scalarTensorFixed (D := D × J) K).obj
        ((curry (D := D) (J := J)).inverse.obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro e e' f; ext n q; rfl)

private def uncurryTensorNatural (K : SSet.{u}) :
    (CategoryTheory.Functor.whiskeringRight Dᵒᵖ (SimplicialPresheaf.{u} J)
      (SimplicialPresheaf.{u} J)).obj (scalarTensorFixed (D := J) K) ⋙
        (curry (D := D) (J := J)).inverse ≅
    (curry (D := D) (J := J)).inverse ⋙ scalarTensorFixed (D := D × J) K :=
  NatIso.ofComponents (fun X => uncurryTensorIso (D := D) (J := J) K X)
    (by intro X Y a; ext e n q; rfl)

private def fixedScalarMap {K L : SSet.{u}} (k : K ⟶ L) :
    scalarTensorFixed (D := J) K ⟶ scalarTensorFixed (D := J) L where
  app A := (scalarTensor.obj A).map k
  naturality _ _ a := (scalarTensor.map a).naturality k |>.symm

omit [LocallySmall.{u} D] [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem uncurryScalarMap {K L : SSet.{u}} (k : K ⟶ L)
    (X : Dᵒᵖ ⥤ SimplicialPresheaf.{u} J) :
    (curry (D := D) (J := J)).inverse.map
        (CategoryTheory.Functor.whiskerLeft X (fixedScalarMap (J := J) k)) ≫
        (uncurryTensorIso (D := D) (J := J) L X).hom =
      (uncurryTensorIso (D := D) (J := J) K X).hom ≫
        (scalarTensor.obj ((curry (D := D) (J := J)).inverse.obj X)).map k := by
  ext e n q
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem nestedTensor_source (d : D)
    {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B) (K : SSet.{u}) :
    (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).map
        ((scalarTensor.map a).app K) ≫ (freeTensorNestedIso (J := J) d B K).hom =
      (freeTensorNestedIso (J := J) d A K).hom ≫
        CategoryTheory.Functor.whiskerRight
            ((evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).map a)
          (scalarTensorFixed (D := J) K) := by
  apply NatTrans.ext
  funext e
  apply Sigma.hom_ext
  intro h
  change Sigma.ι _ h ≫ Sigma.desc (fun h : op d ⟶ e => (scalarTensor.map a).app K ≫
      Sigma.ι (fun _ : op d ⟶ e => (scalarTensor.obj B).obj K) h) ≫
        (tensorCoproductIso (J := J) d e B K).hom =
    Sigma.ι _ h ≫ (tensorCoproductIso (J := J) d e A K).hom ≫
      (scalarTensorFixed (D := J) K).map
        (Sigma.desc (fun h : op d ⟶ e => a ≫ Sigma.ι (fun _ : op d ⟶ e => B) h))
  rw [← Category.assoc, colimit.ι_desc, Cofan.mk_ι_app, Category.assoc,
    tensorCoproductIso_hom_ι]
  rw [← Category.assoc, tensorCoproductIso_hom_ι, ← CategoryTheory.Functor.map_comp,
    colimit.ι_desc, Cofan.mk_ι_app, CategoryTheory.Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem nestedTensor_scalar (d : D) (A : SimplicialPresheaf.{u} J)
    {K L : SSet.{u}} (k : K ⟶ L) :
    (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).map
        ((scalarTensor.obj A).map k) ≫ (freeTensorNestedIso (J := J) d A L).hom =
      (freeTensorNestedIso (J := J) d A K).hom ≫
        CategoryTheory.Functor.whiskerLeft
            ((evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A)
          (fixedScalarMap (J := J) k) := by
  apply NatTrans.ext
  funext e
  apply Sigma.hom_ext
  intro h
  change Sigma.ι _ h ≫ Sigma.desc (fun h : op d ⟶ e => (scalarTensor.obj A).map k ≫
      Sigma.ι (fun _ : op d ⟶ e => (scalarTensor.obj A).obj L) h) ≫
        (tensorCoproductIso (J := J) d e A L).hom =
    Sigma.ι _ h ≫ (tensorCoproductIso (J := J) d e A K).hom ≫
      (scalarTensor.obj (∐ fun _ : op d ⟶ e => A)).map k
  rw [← Category.assoc, colimit.ι_desc, Cofan.mk_ι_app, Category.assoc,
    tensorCoproductIso_hom_ι]
  rw [← Category.assoc, tensorCoproductIso_hom_ι]
  exact (scalarTensor.map (Sigma.ι (fun _ : op d ⟶ e => A) h)).naturality k
/-- The original flat free presheaf carries the actual coefficient tensor to its flat tensor. -/
@[reducible]
def freeTensorComponentIso (d : D) (A : SimplicialPresheaf.{u} J)
    (K : SSet.{u}) :
    (free (J := J) d).obj ((scalarTensor.obj A).obj K) ≅
      (scalarTensor.obj ((free (J := J) d).obj A)).obj K := by
  let : ∀ a b : Dᵒᵖ, HasCoproductsOfShape (a ⟶ b) (SimplicialPresheaf.{u} J) :=
    fun a b => hasCoproductsOfShape_of_small (SimplicialPresheaf.{u} J) (a ⟶ b)
  exact (curry (D := D) (J := J)).inverse.mapIso (freeTensorNestedIso (J := J) d A K) ≪≫
    uncurryTensorIso (D := D) (J := J) K
      ((evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A)

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Original coefficient maps commute with the actual Hom-coproduct tensor comparison. -/
theorem freeTensorComponent_source (d : D)
    {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B) (K : SSet.{u}) :
    (free (J := J) d).map ((scalarTensor.map a).app K) ≫
        (freeTensorComponentIso (J := J) d B K).hom =
      (freeTensorComponentIso (J := J) d A K).hom ≫
        (scalarTensor.map ((free (J := J) d).map a)).app K := by
  let C := (curry (D := D) (J := J)).inverse
  let F := evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)
  let αA := (freeTensorNestedIso (J := J) d A K).hom
  let αB := (freeTensorNestedIso (J := J) d B K).hom
  let γA := (uncurryTensorIso (D := D) (J := J) K (F.obj A)).hom
  let γB := (uncurryTensorIso (D := D) (J := J) K (F.obj B)).hom
  let aK := (scalarTensor.map a).app K
  let aF := CategoryTheory.Functor.whiskerRight (F.map a) (scalarTensorFixed (D := J) K)
  let aFlat := (scalarTensorFixed (D := D × J) K).map (C.map (F.map a))
  have hN := nestedTensor_source (J := J) d a K
  change F.map aK ≫ αB = αA ≫ aF at hN
  have hU := (uncurryTensorNatural (D := D) (J := J) K).hom.naturality (F.map a)
  change C.map aF ≫ γB = γA ≫ aFlat at hU
  -- Normalize BOTH target boundaries before a rewrite can leave an
  -- implicitly ill-typed scalarTensorFixed / scalarTensor.obj mixture.
  change C.map (F.map aK) ≫ (C.map αB ≫ γB) =
    (C.map αA ≫ γA) ≫ aFlat
  calc
    _ = C.map (F.map aK ≫ αB) ≫ γB := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = C.map (αA ≫ aF) ≫ γB := by rw [hN]
    _ = C.map αA ≫ (C.map aF ≫ γB) := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = C.map αA ≫ (γA ≫ aFlat) := congrArg (C.map αA ≫ ·) hU
    _ = (C.map αA ≫ γA) ≫ aFlat := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Every original scalar map commutes with the same flat free tensor comparison. -/
theorem freeTensorComponent_scalar (d : D) (A : SimplicialPresheaf.{u} J)
    {K L : SSet.{u}} (k : K ⟶ L) :
    (free (J := J) d).map ((scalarTensor.obj A).map k) ≫
        (freeTensorComponentIso (J := J) d A L).hom =
      (freeTensorComponentIso (J := J) d A K).hom ≫
        (scalarTensor.obj ((free (J := J) d).obj A)).map k := by
  let C := (curry (D := D) (J := J)).inverse
  let F := evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)
  let αK := (freeTensorNestedIso (J := J) d A K).hom
  let αL := (freeTensorNestedIso (J := J) d A L).hom
  let γK := (uncurryTensorIso (D := D) (J := J) K (F.obj A)).hom
  let γL := (uncurryTensorIso (D := D) (J := J) L (F.obj A)).hom
  let aK := (scalarTensor.obj A).map k
  let aF := CategoryTheory.Functor.whiskerLeft (F.obj A) (fixedScalarMap (J := J) k)
  let aFlat := (scalarTensor.obj (C.obj (F.obj A))).map k
  have hN := nestedTensor_scalar (J := J) d A k
  change F.map aK ≫ αL = αK ≫ aF at hN
  have hU := uncurryScalarMap (D := D) (J := J) k (F.obj A)
  change C.map aF ≫ γL = γK ≫ aFlat at hU
  -- Make the free object's literal inverse-currying object appear on BOTH sides.
  change C.map (F.map aK) ≫ (C.map αL ≫ γL) =
    (C.map αK ≫ γK) ≫ aFlat
  calc
    _ = C.map (F.map aK ≫ αL) ≫ γL := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = C.map (αK ≫ aF) ≫ γL := by rw [hN]
    _ = C.map αK ≫ (C.map aF ≫ γL) := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = C.map αK ≫ (γK ≫ aFlat) := congrArg (C.map αK ≫ ·) hU
    _ = (C.map αK ≫ γK) ≫ aFlat := (Category.assoc _ _ _).symm

/-- The entire actual free/scalar tensor comparison, natural in the scalar object. -/
@[reducible]
def freeTensorIso (d : D) (A : SimplicialPresheaf.{u} J) :
    scalarTensor.obj A ⋙ free (J := J) d ≅
      scalarTensor.obj ((free (J := J) d).obj A) :=
  NatIso.ofComponents (fun K => freeTensorComponentIso (J := J) d A K)
    (by intro K L k; exact freeTensorComponent_scalar (J := J) d A k)

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Both original coefficient directions retain the same scalar tensor isomorphism. -/
theorem freeTensorIso_source (d : D)
    {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B) (K : SSet.{u}) :
    (free (J := J) d).map ((scalarTensor.map a).app K) ≫
        (freeTensorIso (J := J) d B).hom.app K =
      (freeTensorIso (J := J) d A).hom.app K ≫
        (scalarTensor.map ((free (J := J) d).map a)).app K :=
  freeTensorComponent_source (J := J) d a K

private theorem rightUniq_transpose
    {C₀ C₁ : Type*} [Category* C₀] [Category* C₁]
    {F : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀}
    (a₀ : F ⊣ R) (a₁ : F ⊣ R') {K : C₀} {Z : C₁} (g : K ⟶ R.obj Z) :
    g ≫ (a₀.rightAdjointUniq a₁).hom.app Z =
      a₁.homEquiv K Z ((a₀.homEquiv K Z).symm g) := by
  apply (a₁.homEquiv K Z).symm.injective
  simp only [_root_.Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    CategoryTheory.Functor.map_comp, Category.assoc, Adjunction.rightAdjointUniq_hom_app_counit]

/-- The whole target-natural free mapping-end comparison of the original coefficient presheaf. -/
@[reducible]
def freeHomNatIso (d : D) (A : SimplicialPresheaf.{u} J) :
    innerHomFunctor.obj (op ((free (J := J) d).obj A)) ≅
      evaluation (J := J) d ⋙ innerHomFunctor.obj (op A) := by
  let a₀ := scalarTensorHomAdjunction ((free (J := J) d).obj A)
  let a₁ := (scalarTensorHomAdjunction A).comp (freeAdjunction (J := J) d)
  exact a₀.rightAdjointUniq (a₁.ofNatIsoLeft (freeTensorIso (J := J) d A))

/-- The actual scalar free mapping-end isomorphism at the original target. -/
abbrev freeHomIso (d : D) (A : SimplicialPresheaf.{u} J)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    innerHom ((free (J := J) d).obj A) Z ≅
      innerHom A ((evaluation (J := J) d).obj Z) :=
  (freeHomNatIso (J := J) d A).app Z

/-- The whole target-natural cofree mapping-end comparison on the original flat source. -/
@[reducible]
def cofreeHomNatIso (d : D) (A : SimplicialPresheaf.{u} (D × J)) :
    cofree (J := J) d ⋙ innerHomFunctor.obj (op A) ≅
      innerHomFunctor.obj (op ((evaluation (J := J) d).obj A)) := by
  let a₀ := (scalarTensorHomAdjunction A).comp (cofreeAdjunction (J := J) d)
  let a₁ := scalarTensorHomAdjunction ((evaluation (J := J) d).obj A)
  exact a₀.rightAdjointUniq (a₁.ofNatIsoLeft (evaluationTensorIso (J := J) d A).symm)

/-- The actual scalar cofree mapping-end isomorphism at the original coefficient target. -/
abbrev cofreeHomIso (d : D) (A : SimplicialPresheaf.{u} (D × J))
    (Z : SimplicialPresheaf.{u} J) :
    innerHom A ((cofree (J := J) d).obj Z) ≅
      innerHom ((evaluation (J := J) d).obj A) Z :=
  (cofreeHomNatIso (J := J) d A).app Z

set_option backward.isDefEq.respectTransparency false in
/-- Free forward transposition keeps the original tensor/free/ordinary adjunction maps. -/
theorem freeHomIso_hom_characteristic (d : D) (A : SimplicialPresheaf.{u} J)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} (D × J))
    (g : K ⟶ innerHom ((free (J := J) d).obj A) Z) :
    g ≫ (freeHomIso (J := J) d A Z).hom =
      scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)
        ((freeAdjunction (J := J) d).homEquiv _ Z
          ((freeTensorIso (J := J) d A).hom.app K ≫
            (scalarTensorHomEquiv ((free (J := J) d).obj A) K Z).symm g)) := by
  have h := rightUniq_transpose
    (scalarTensorHomAdjunction ((free (J := J) d).obj A))
    (((scalarTensorHomAdjunction A).comp (freeAdjunction (J := J) d)).ofNatIsoLeft
      (freeTensorIso (J := J) d A)) g
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv,
    scalarTensorHomAdjunction_homEquiv, scalarTensorHomAdjunction_homEquiv] at h
  change g ≫ (freeHomIso (J := J) d A Z).hom =
    scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)
      ((freeAdjunction (J := J) d).homEquiv _ Z
        ((freeTensorIso (J := J) d A).hom.app K ≫
          (scalarTensorHomEquiv ((free (J := J) d).obj A) K Z).symm g)) at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Cofree forward transposition keeps the evaluation tensor inverse and original Hom map. -/
theorem cofreeHomIso_hom_characteristic (d : D)
    (A : SimplicialPresheaf.{u} (D × J)) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} J)
    (g : K ⟶ innerHom A ((cofree (J := J) d).obj Z)) :
    g ≫ (cofreeHomIso (J := J) d A Z).hom =
      scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z
        ((evaluationTensorIso (J := J) d A).inv.app K ≫
          ((cofreeAdjunction (J := J) d).homEquiv _ Z).symm
            ((scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)).symm g)) := by
  have h := rightUniq_transpose
    ((scalarTensorHomAdjunction A).comp (cofreeAdjunction (J := J) d))
    ((scalarTensorHomAdjunction ((evaluation (J := J) d).obj A)).ofNatIsoLeft
      (evaluationTensorIso (J := J) d A).symm) g
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv,
    scalarTensorHomAdjunction_homEquiv, scalarTensorHomAdjunction_homEquiv] at h
  simp only [_root_.Equiv.symm_trans_apply,
    CategoryTheory.Iso.symm_hom] at h
  change g ≫ (cofreeHomIso (J := J) d A Z).hom =
    scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z
      ((evaluationTensorIso (J := J) d A).inv.app K ≫
        ((cofreeAdjunction (J := J) d).homEquiv _ Z).symm
          ((scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)).symm g)) at h
  exact h

/-- The actual forward free characteristic after undoing the scalar transposition. -/
theorem freeHomIso_untranspose (d : D) (A : SimplicialPresheaf.{u} J)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} (D × J))
    (g : K ⟶ innerHom ((free (J := J) d).obj A) Z) :
    (scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)).symm
        (g ≫ (freeHomIso (J := J) d A Z).hom) =
      (freeAdjunction (J := J) d).homEquiv _ Z
        ((freeTensorIso (J := J) d A).hom.app K ≫
          (scalarTensorHomEquiv ((free (J := J) d).obj A) K Z).symm g) := by
  rw [freeHomIso_hom_characteristic, _root_.Equiv.symm_apply_apply]

/-- The actual forward cofree characteristic after undoing the scalar transposition. -/
theorem cofreeHomIso_untranspose (d : D) (A : SimplicialPresheaf.{u} (D × J))
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} J)
    (g : K ⟶ innerHom A ((cofree (J := J) d).obj Z)) :
    (scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z).symm
        (g ≫ (cofreeHomIso (J := J) d A Z).hom) =
      (evaluationTensorIso (J := J) d A).inv.app K ≫
        ((cofreeAdjunction (J := J) d).homEquiv _ Z).symm
          ((scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)).symm g) := by
  rw [cofreeHomIso_hom_characteristic, _root_.Equiv.symm_apply_apply]

/-- Free inverse transposition keeps both the native scalar and ordinary inverse Hom maps. -/
theorem freeHomIso_inv_characteristic (d : D) (A : SimplicialPresheaf.{u} J)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} (D × J))
    (g : K ⟶ innerHom A ((evaluation (J := J) d).obj Z)) :
    (scalarTensorHomEquiv ((free (J := J) d).obj A) K Z).symm
        (g ≫ (freeHomIso (J := J) d A Z).inv) =
      (freeTensorIso (J := J) d A).inv.app K ≫
        ((freeAdjunction (J := J) d).homEquiv _ Z).symm
          ((scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)).symm g) := by
  have h := freeHomIso_untranspose (J := J) d A K Z
    (g ≫ (freeHomIso (J := J) d A Z).inv)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have h' := congrArg (fun q => ((freeAdjunction (J := J) d).homEquiv _ Z).symm q) h
  simp only [_root_.Equiv.symm_apply_apply] at h'
  exact (Iso.eq_inv_comp _).mpr h'.symm

set_option backward.isDefEq.respectTransparency false in
/-- Cofree inverse transposition keeps the native evaluation tensor forward comparison. -/
theorem cofreeHomIso_inv_characteristic (d : D) (A : SimplicialPresheaf.{u} (D × J))
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} J)
    (g : K ⟶ innerHom ((evaluation (J := J) d).obj A) Z) :
    (scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)).symm
        (g ≫ (cofreeHomIso (J := J) d A Z).inv) =
      (cofreeAdjunction (J := J) d).homEquiv _ Z
        ((evaluationTensorIso (J := J) d A).hom.app K ≫
          (scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z).symm g) := by
  let T₀ := scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)
  let T₁ := scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z
  let H := (cofreeAdjunction (J := J) d).homEquiv ((scalarTensor.obj A).obj K) Z
  let e := evaluationTensorIso (J := J) d A
  let q := T₀.symm (g ≫ (cofreeHomIso (J := J) d A Z).inv)
  have h := cofreeHomIso_untranspose (J := J) d A K Z
    (g ≫ (cofreeHomIso (J := J) d A Z).inv)
  simp only [CategoryTheory.Category.assoc, CategoryTheory.Iso.inv_hom_id,
    CategoryTheory.Category.comp_id] at h
  change T₁.symm g = e.inv.app K ≫ H.symm q at h
  apply H.symm.injective
  change H.symm q = H.symm (H (e.hom.app K ≫ T₁.symm g))
  rw [_root_.Equiv.symm_apply_apply]
  calc
    _ = e.hom.app K ≫ (e.inv.app K ≫ H.symm q) := by
      rw [← CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id_app,
        CategoryTheory.Category.id_comp]
    _ = e.hom.app K ≫ T₁.symm g := congrArg (e.hom.app K ≫ ·) h.symm

/-- The free end comparison is source-natural on every original coefficient arrow. -/
theorem freeHomIso_source (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    innerHomPre ((free (J := J) d).map a) Z ≫ (freeHomIso (J := J) d A Z).hom =
      (freeHomIso (J := J) d B Z).hom ≫ innerHomPre a ((evaluation (J := J) d).obj Z) := by
  let K := innerHom ((free (J := J) d).obj B) Z
  apply (scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)).symm.injective
  have hB := freeHomIso_untranspose (J := J) d B K Z (𝟙 _)
  simp only [Category.id_comp] at hB
  have hE := scalarTensorHomEquiv_source_symm ((free (J := J) d).map a) K Z (𝟙 _)
  simp only [Category.id_comp] at hE
  rw [freeHomIso_untranspose, scalarTensorHomEquiv_source_symm, hB, hE,
    ← Category.assoc, ← freeTensorIso_source, Category.assoc,
    (freeAdjunction (J := J) d).homEquiv_naturality_left]

/-- The cofree end comparison is source-natural on every original flat presheaf arrow. -/
theorem cofreeHomIso_source (d : D) {A B : SimplicialPresheaf.{u} (D × J)} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} J) :
    innerHomPre a ((cofree (J := J) d).obj Z) ≫ (cofreeHomIso (J := J) d A Z).hom =
      (cofreeHomIso (J := J) d B Z).hom ≫ innerHomPre ((evaluation (J := J) d).map a) Z := by
  let K := innerHom B ((cofree (J := J) d).obj Z)
  apply (scalarTensorHomEquiv ((evaluation (J := J) d).obj A) K Z).symm.injective
  have hB := cofreeHomIso_untranspose (J := J) d B K Z (𝟙 _)
  simp only [Category.id_comp] at hB
  have hE := scalarTensorHomEquiv_source_symm a K ((cofree (J := J) d).obj Z) (𝟙 _)
  simp only [Category.id_comp] at hE
  have hInv : (evaluationTensorIso (J := J) d A).inv.app K ≫
      (evaluation (J := J) d).map ((scalarTensor.map a).app K) =
      (scalarTensor.map ((evaluation (J := J) d).map a)).app K ≫
        (evaluationTensorIso (J := J) d B).inv.app K := by
    ext j n q
    rfl
  rw [cofreeHomIso_untranspose, scalarTensorHomEquiv_source_symm, hE,
    (cofreeAdjunction (J := J) d).homEquiv_naturality_left_symm,
    ← Category.assoc, hInv, Category.assoc, ← hB]

/-- Both inverse source naturalities follow for the same original end comparison maps. -/
theorem freeHomIso_source_inv (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    innerHomPre a ((evaluation (J := J) d).obj Z) ≫ (freeHomIso (J := J) d A Z).inv =
      (freeHomIso (J := J) d B Z).inv ≫ innerHomPre ((free (J := J) d).map a) Z := by
  apply (cancel_mono (freeHomIso (J := J) d A Z).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    freeHomIso_source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The cofree inverse source square keeps both actual original precomposition arrows. -/
theorem cofreeHomIso_source_inv (d : D)
    {A B : SimplicialPresheaf.{u} (D × J)} (a : A ⟶ B) (Z : SimplicialPresheaf.{u} J) :
    innerHomPre ((evaluation (J := J) d).map a) Z ≫ (cofreeHomIso (J := J) d A Z).inv =
      (cofreeHomIso (J := J) d B Z).inv ≫ innerHomPre a ((cofree (J := J) d).obj Z) := by
  apply (cancel_mono (cofreeHomIso (J := J) d A Z).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    cofreeHomIso_source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Both original target naturalities are the actual natural isomorphism components. -/
theorem freeHomIso_target (d : D) (A : SimplicialPresheaf.{u} J)
    {Z Z' : SimplicialPresheaf.{u} (D × J)} (z : Z ⟶ Z') :
    innerHomPost ((free (J := J) d).obj A) z ≫ (freeHomIso (J := J) d A Z').hom =
      (freeHomIso (J := J) d A Z).hom ≫
        innerHomPost A ((evaluation (J := J) d).map z) ∧
    innerHomPost A ((evaluation (J := J) d).map z) ≫ (freeHomIso (J := J) d A Z').inv =
      (freeHomIso (J := J) d A Z).inv ≫ innerHomPost ((free (J := J) d).obj A) z :=
  ⟨(freeHomNatIso (J := J) d A).hom.naturality z,
    (freeHomNatIso (J := J) d A).inv.naturality z⟩

/-- Both original cofree target naturalities retain the same native cofree action. -/
theorem cofreeHomIso_target (d : D) (A : SimplicialPresheaf.{u} (D × J))
    {Z Z' : SimplicialPresheaf.{u} J} (z : Z ⟶ Z') :
    innerHomPost A ((cofree (J := J) d).map z) ≫ (cofreeHomIso (J := J) d A Z').hom =
      (cofreeHomIso (J := J) d A Z).hom ≫
        innerHomPost ((evaluation (J := J) d).obj A) z ∧
    innerHomPost ((evaluation (J := J) d).obj A) z ≫ (cofreeHomIso (J := J) d A Z').inv =
      (cofreeHomIso (J := J) d A Z).inv ≫ innerHomPost A ((cofree (J := J) d).map z) :=
  ⟨(cofreeHomNatIso (J := J) d A).hom.naturality z,
    (cofreeHomNatIso (J := J) d A).inv.naturality z⟩

/-- The WHOLE free precomposition Arrow uses the original target/source endpoint order. -/
def freePrecompArrowIso (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    Arrow.mk (innerHomPre ((free (J := J) d).map a) Z) ≅
      Arrow.mk (innerHomPre a ((evaluation (J := J) d).obj Z)) :=
  Arrow.isoMk (freeHomIso (J := J) d B Z) (freeHomIso (J := J) d A Z)
    (freeHomIso_source (J := J) d a Z).symm

/-- The WHOLE cofree precomposition Arrow retains the original flat source arrow. -/
def cofreePrecompArrowIso (d : D) {A B : SimplicialPresheaf.{u} (D × J)} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} J) :
    Arrow.mk (innerHomPre a ((cofree (J := J) d).obj Z)) ≅
      Arrow.mk (innerHomPre ((evaluation (J := J) d).map a) Z) :=
  Arrow.isoMk (cofreeHomIso (J := J) d B Z) (cofreeHomIso (J := J) d A Z)
    (cofreeHomIso_source (J := J) d a Z).symm

/-- All four actual forward/inverse free Arrow fields are the original end isomorphisms. -/
theorem freePrecompArrowIso_laws (d : D) {A B : SimplicialPresheaf.{u} J} (a : A ⟶ B)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    (freePrecompArrowIso (J := J) d a Z).hom.left = (freeHomIso (J := J) d B Z).hom ∧
    (freePrecompArrowIso (J := J) d a Z).hom.right = (freeHomIso (J := J) d A Z).hom ∧
    (freePrecompArrowIso (J := J) d a Z).inv.left = (freeHomIso (J := J) d B Z).inv ∧
    (freePrecompArrowIso (J := J) d a Z).inv.right = (freeHomIso (J := J) d A Z).inv :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The actual coefficient object of the original free diagram is its original Hom coproduct. -/
@[reducible]
def freeObjectIso (d e : D) (A : SimplicialPresheaf.{u} J) :
    (evaluation (J := J) e).obj ((free (J := J) d).obj A) ≅
      ∐ fun _ : op d ⟶ op e => A :=
  ((curry (D := D) (J := J)).counitIso.app
    ((evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A)).app (op e)

/-- The actual coefficient object of the original cofree diagram is its original Hom product. -/
@[reducible]
def cofreeObjectIso (d e : D) (Z : SimplicialPresheaf.{u} J) :
    (evaluation (J := J) e).obj ((cofree (J := J) d).obj Z) ≅
      ∏ᶜ fun _ : op e ⟶ op d => Z :=
  ((curry (D := D) (J := J)).counitIso.app
    ((evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op d)).obj Z)).app (op e)

/-- Every original arrow e→d supplies its actual free summand, without resizing the Hom label. -/
@[reducible]
def freeInclusion (d e : D) (h : e ⟶ d) (A : SimplicialPresheaf.{u} J) :
    A ⟶ (evaluation (J := J) e).obj ((free (J := J) d).obj A) :=
  Sigma.ι (fun _ : op d ⟶ op e => A) h.op ≫ (freeObjectIso (J := J) d e A).inv

/-- Every original arrow d→e supplies the actual cofree projection with the correct orientation. -/
@[reducible]
def cofreeProjection (d e : D) (h : d ⟶ e) (Z : SimplicialPresheaf.{u} J) :
    (evaluation (J := J) e).obj ((cofree (J := J) d).obj Z) ⟶ Z :=
  (cofreeObjectIso (J := J) d e Z).hom ≫ Pi.π (fun _ : op e ⟶ op d => Z) h.op

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- A free summand normalization needs only its original e→d label. -/
theorem freeInclusion_hom (d e : D) (h : e ⟶ d) (A : SimplicialPresheaf.{u} J) :
    freeInclusion (J := J) d e h A ≫ (freeObjectIso (J := J) d e A).hom =
      Sigma.ι (fun _ : op d ⟶ op e => A) h.op := by
  simp only [freeInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- A cofree factor normalization needs only its original d→e label. -/
theorem cofreeProjection_inv (d e : D) (h : d ⟶ e) (Z : SimplicialPresheaf.{u} J) :
    (cofreeObjectIso (J := J) d e Z).inv ≫ cofreeProjection (J := J) d e h Z =
      Pi.π (fun _ : op e ⟶ op d => Z) h.op := by
  simp only [cofreeProjection, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The original restriction in the D parameter retains its native component map. -/
@[reducible]
def evaluationRestriction {d e : D} (t : d ⟶ e) :
    evaluation (J := J) e ⟶ evaluation (J := J) d where
  app X := ((curry (D := D) (J := J)).functor.obj X).map t.op
  naturality X Y f := by
    exact (((curry (D := D) (J := J)).functor.map f).naturality t.op).symm

/-- Original parameter maps reindex free summands by the same unshrunk Hom composition. -/
@[reducible]
def freeIndexMap {d e : D} (t : d ⟶ e) (A : SimplicialPresheaf.{u} J) :
    (free (J := J) d).obj A ⟶ (free (J := J) e).obj A :=
  (curry (D := D) (J := J)).inverse.map
    { app q := Sigma.desc (fun h : op d ⟶ q =>
        Sigma.ι (fun _ : op e ⟶ q => A) (t.op ≫ h))
      naturality q q' f := by
        apply Sigma.hom_ext
        intro h
        simp [evaluationLeftAdjoint, Category.assoc] }

/-- Original parameter maps reindex cofree projections by actual Hom precomposition. -/
@[reducible]
def cofreeIndexMap {d e : D} (t : d ⟶ e) (Z : SimplicialPresheaf.{u} J) :
    (cofree (J := J) d).obj Z ⟶ (cofree (J := J) e).obj Z :=
  (curry (D := D) (J := J)).inverse.map
    { app q := Pi.lift (fun h : q ⟶ op e => Pi.π (fun _ : q ⟶ op d => Z) (h ≫ t.op))
      naturality q q' f := by
        apply Pi.hom_ext
        intro h
        simp [evaluationRightAdjoint, Category.assoc] }

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem freeUnit (d : D) (A : SimplicialPresheaf.{u} J) :
    (freeAdjunction (J := J) d).unit.app A =
      freeInclusion (J := J) d d (𝟙 d) A := by
  change ((evaluationAdjunctionRight (SimplicialPresheaf.{u} J) (op d)).comp
    (curry (D := D) (J := J)).symm.toAdjunction).unit.app A = _
  rw [Adjunction.comp_unit_app]
  rfl

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem cofreeCounit (d : D) (Z : SimplicialPresheaf.{u} J) :
    (cofreeAdjunction (J := J) d).counit.app Z =
      cofreeProjection (J := J) d d (𝟙 d) Z := by
  change ((curry (D := D) (J := J)).toAdjunction.comp
    (evaluationAdjunctionLeft (SimplicialPresheaf.{u} J) (op d))).counit.app Z = _
  rw [Adjunction.comp_counit_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem freeInclusion_operator (d e f : D) (s : e ⟶ f) (h : f ⟶ d)
    (A : SimplicialPresheaf.{u} J) :
    freeInclusion (J := J) d f h A ≫
        ((curry (D := D) (J := J)).functor.obj ((free (J := J) d).obj A)).map s.op =
      freeInclusion (J := J) d e (s ≫ h) A := by
  let N := (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A
  let E := (curry (D := D) (J := J)).counitIso.app N
  let U := ((curry (D := D) (J := J)).inverse ⋙
    (curry (D := D) (J := J)).functor).obj N
  have hn : N.map s.op ≫ E.inv.app (op e) =
      E.inv.app (op f) ≫ U.map s.op := E.inv.naturality s.op
  have hp : Sigma.ι (fun _ : op d ⟶ op f => A) h.op ≫ N.map s.op =
      Sigma.ι (fun _ : op d ⟶ op e => A) (s ≫ h).op := by
    change Sigma.ι (fun _ : op d ⟶ op f => A) h.op ≫
      Sigma.desc (fun g : op d ⟶ op f =>
        Sigma.ι (fun _ : op d ⟶ op e => A) (g ≫ s.op)) = _
    simp only [colimit.ι_desc, Cofan.mk_ι_app, op_comp]
  change Sigma.ι (fun _ : op d ⟶ op f => A) h.op ≫
      E.inv.app (op f) ≫ U.map s.op =
    Sigma.ι (fun _ : op d ⟶ op e => A) (s ≫ h).op ≫ E.inv.app (op e)
  calc
    _ = Sigma.ι (fun _ : op d ⟶ op f => A) h.op ≫
        N.map s.op ≫ E.inv.app (op e) :=
      congrArg (fun k => Sigma.ι (fun _ : op d ⟶ op f => A) h.op ≫ k) hn.symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ E.inv.app (op e)) hp

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem cofreeProjection_operator (d e : D) (h : d ⟶ e)
    (Z : SimplicialPresheaf.{u} J) :
    cofreeProjection (J := J) d e h Z =
      ((curry (D := D) (J := J)).functor.obj ((cofree (J := J) d).obj Z)).map h.op ≫
        cofreeProjection (J := J) d d (𝟙 d) Z := by
  let N := (evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op d)).obj Z
  let E := (curry (D := D) (J := J)).counitIso.app N
  let U := ((curry (D := D) (J := J)).inverse ⋙
    (curry (D := D) (J := J)).functor).obj N
  have hn : U.map h.op ≫ E.hom.app (op d) =
      E.hom.app (op e) ≫ N.map h.op := E.hom.naturality h.op
  have hp : N.map h.op ≫
      Pi.π (fun _ : op d ⟶ op d => Z) (𝟙 _) =
        Pi.π (fun _ : op e ⟶ op d => Z) h.op := by
    change Pi.lift (fun g : op d ⟶ op d =>
      Pi.π (fun _ : op e ⟶ op d => Z) (h.op ≫ g)) ≫
        Pi.π (fun _ : op d ⟶ op d => Z) (𝟙 _) = _
    simp only [limit.lift_π, Fan.mk_π_app, Category.comp_id]
  change E.hom.app (op e) ≫
      Pi.π (fun _ : op e ⟶ op d => Z) h.op =
    U.map h.op ≫ E.hom.app (op d) ≫
      Pi.π (fun _ : op d ⟶ op d => Z) (𝟙 _)
  calc
    _ = E.hom.app (op e) ≫ N.map h.op ≫
        Pi.π (fun _ : op d ⟶ op d => Z) (𝟙 _) :=
      (congrArg (fun k => E.hom.app (op e) ≫ k) hp).symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ Pi.π (fun _ : op d ⟶ op d => Z) (𝟙 _)) hn.symm

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Free forward transposition is the actual identity-labelled summand followed by evaluation. -/
theorem freeAdjunction_hom_characteristic (d : D) (A : SimplicialPresheaf.{u} J)
    (X : SimplicialPresheaf.{u} (D × J)) (f : (free (J := J) d).obj A ⟶ X) :
    (freeAdjunction (J := J) d).homEquiv A X f =
      freeInclusion (J := J) d d (𝟙 d) A ≫ (evaluation (J := J) d).map f := by
  rw [Adjunction.homEquiv_unit, freeUnit]

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Free inverse transposition retains every original e→d summand with no reverse-label premise. -/
theorem freeAdjunction_inv_characteristic (d e : D) (h : e ⟶ d)
    (A : SimplicialPresheaf.{u} J) (X : SimplicialPresheaf.{u} (D × J))
    (g : A ⟶ (evaluation (J := J) d).obj X) :
    freeInclusion (J := J) d e h A ≫
        (evaluation (J := J) e).map (((freeAdjunction (J := J) d).homEquiv A X).symm g) =
      g ≫ ((curry (D := D) (J := J)).functor.obj X).map h.op := by
  let p := ((freeAdjunction (J := J) d).homEquiv A X).symm g
  have hn :
      ((curry (D := D) (J := J)).functor.obj ((free (J := J) d).obj A)).map h.op ≫
          (evaluation (J := J) e).map p =
        (evaluation (J := J) d).map p ≫
          ((curry (D := D) (J := J)).functor.obj X).map h.op :=
    ((curry (D := D) (J := J)).functor.map p).naturality h.op
  have hI := freeInclusion_operator (J := J) d e d h (𝟙 d) A
  simp only [Category.comp_id] at hI
  rw [← hI, Category.assoc, hn, ← Category.assoc,
    ← freeAdjunction_hom_characteristic, _root_.Equiv.apply_symm_apply]

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- The cofree ordinary inverse Hom map is actual evaluation followed by the identity projection. -/
theorem cofreeAdjunction_inv_characteristic (d : D) (X : SimplicialPresheaf.{u} (D × J))
    (Z : SimplicialPresheaf.{u} J) (p : X ⟶ (cofree (J := J) d).obj Z) :
    ((cofreeAdjunction (J := J) d).homEquiv X Z).symm p =
      (evaluation (J := J) d).map p ≫ cofreeProjection (J := J) d d (𝟙 d) Z := by
  rw [Adjunction.homEquiv_counit, cofreeCounit]

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Cofree forward transposition retains every original d→e projection with no reverse arrow. -/
theorem cofreeAdjunction_hom_characteristic (d e : D) (h : d ⟶ e)
    (X : SimplicialPresheaf.{u} (D × J)) (Z : SimplicialPresheaf.{u} J)
    (q : (evaluation (J := J) d).obj X ⟶ Z) :
    (evaluation (J := J) e).map ((cofreeAdjunction (J := J) d).homEquiv X Z q) ≫
        cofreeProjection (J := J) d e h Z =
      ((curry (D := D) (J := J)).functor.obj X).map h.op ≫ q := by
  let p := (cofreeAdjunction (J := J) d).homEquiv X Z q
  have hn :
      ((curry (D := D) (J := J)).functor.obj X).map h.op ≫
          (evaluation (J := J) d).map p =
        (evaluation (J := J) e).map p ≫
          ((curry (D := D) (J := J)).functor.obj ((cofree (J := J) d).obj Z)).map h.op :=
    ((curry (D := D) (J := J)).functor.map p).naturality h.op
  rw [cofreeProjection_operator, ← Category.assoc, ← hn, Category.assoc,
    ← cofreeAdjunction_inv_characteristic, _root_.Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- The actual ordinary units and counits are the identity-labelled free and cofree maps. -/
theorem ordinaryAdjunction_unit_counit (d : D) (A Z : SimplicialPresheaf.{u} J)
    (X : SimplicialPresheaf.{u} (D × J)) :
    (freeAdjunction (J := J) d).unit.app A = freeInclusion (J := J) d d (𝟙 d) A ∧
    (cofreeAdjunction (J := J) d).counit.app Z = cofreeProjection (J := J) d d (𝟙 d) Z ∧
    (freeAdjunction (J := J) d).homEquiv _ X ((freeAdjunction (J := J) d).counit.app X) = 𝟙 _ ∧
    ((cofreeAdjunction (J := J) d).homEquiv X _).symm
        ((cofreeAdjunction (J := J) d).unit.app X) = 𝟙 _ := by
  refine ⟨freeUnit d A, cofreeCounit d Z, ?_, ?_⟩
  · have h : ((freeAdjunction (J := J) d).homEquiv _ X).symm (𝟙 _) =
        (freeAdjunction (J := J) d).counit.app X := by
      rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← h, _root_.Equiv.apply_symm_apply]
  · have h : (cofreeAdjunction (J := J) d).homEquiv X _ (𝟙 _) =
        (cofreeAdjunction (J := J) d).unit.app X := by
      rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
      exact CategoryTheory.Category.comp_id _
    rw [← h, _root_.Equiv.symm_apply_apply]

private def assistParameterFreeMap {d e : D} (t : d ⟶ e)
    (A : SimplicialPresheaf.{u} J) :
    (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A ⟶
      (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op e)).obj A where
  app q := Sigma.desc (fun h : op d ⟶ q =>
    Sigma.ι (fun _ : op e ⟶ q => A) (t.op ≫ h))
  naturality q q' f := by
    apply Sigma.hom_ext
    intro h
    simp [evaluationLeftAdjoint, Category.assoc]

private def assistParameterCofreeMap {d e : D} (t : d ⟶ e)
    (Z : SimplicialPresheaf.{u} J) :
    (evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op d)).obj Z ⟶
      (evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op e)).obj Z where
  app q := Pi.lift (fun h : q ⟶ op e =>
    Pi.π (fun _ : q ⟶ op d => Z) (h ≫ t.op))
  naturality q q' f := by
    apply Pi.hom_ext
    intro h
    simp [evaluationRightAdjoint, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem assist_freeIndex_inclusion {d e q : D}
    (t : d ⟶ e) (h : q ⟶ d) (A : SimplicialPresheaf.{u} J) :
    freeInclusion (J := J) d q h A ≫
        (evaluation (J := J) q).map (freeIndexMap (J := J) t A) =
      freeInclusion (J := J) e q (h ≫ t) A := by
  let Nd := (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A
  let Ne := (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op e)).obj A
  let R := (curry (D := D) (J := J)).inverse ⋙ (curry (D := D) (J := J)).functor
  let Ed : R.obj Nd ≅ Nd := (curry (D := D) (J := J)).counitIso.app Nd
  let Ee : R.obj Ne ≅ Ne := (curry (D := D) (J := J)).counitIso.app Ne
  let N : Nd ⟶ Ne := assistParameterFreeMap (J := J) t A
  have hn : N.app (op q) ≫ Ee.inv.app (op q) =
      Ed.inv.app (op q) ≫ (R.map N).app (op q) :=
    congrArg (fun z => z.app (op q))
      ((curry (D := D) (J := J)).counitIso.inv.naturality N)
  have hi : Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫ N.app (op q) =
      Sigma.ι (fun _ : op e ⟶ op q => A) (h ≫ t).op := by
    change Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫
      Sigma.desc (fun j : op d ⟶ op q =>
        Sigma.ι (fun _ : op e ⟶ op q => A) (t.op ≫ j)) = _
    simpa only [op_comp] using (Sigma.ι_comp_desc
      (fun j : op d ⟶ op q => Sigma.ι (fun _ : op e ⟶ op q => A) (t.op ≫ j)) h.op)
  change (Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫ Ed.inv.app (op q)) ≫
    (R.map N).app (op q) =
      Sigma.ι (fun _ : op e ⟶ op q => A) (h ≫ t).op ≫ Ee.inv.app (op q)
  calc
    _ = Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫
        (Ed.inv.app (op q) ≫ (R.map N).app (op q)) := CategoryTheory.Category.assoc _ _ _
    _ = Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫
        (N.app (op q) ≫ Ee.inv.app (op q)) :=
      congrArg (Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫ ·) hn.symm
    _ = (Sigma.ι (fun _ : op d ⟶ op q => A) h.op ≫ N.app (op q)) ≫
        Ee.inv.app (op q) := (CategoryTheory.Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ Ee.inv.app (op q)) hi

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem assist_cofreeIndex_projection {d e q : D}
    (t : d ⟶ e) (h : e ⟶ q) (Z : SimplicialPresheaf.{u} J) :
    (evaluation (J := J) q).map (cofreeIndexMap (J := J) t Z) ≫
        cofreeProjection (J := J) e q h Z =
      cofreeProjection (J := J) d q (t ≫ h) Z := by
  let Nd := (evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op d)).obj Z
  let Ne := (evaluationRightAdjoint (SimplicialPresheaf.{u} J) (op e)).obj Z
  let R := (curry (D := D) (J := J)).inverse ⋙ (curry (D := D) (J := J)).functor
  let Ed : R.obj Nd ≅ Nd := (curry (D := D) (J := J)).counitIso.app Nd
  let Ee : R.obj Ne ≅ Ne := (curry (D := D) (J := J)).counitIso.app Ne
  let N : Nd ⟶ Ne := assistParameterCofreeMap (J := J) t Z
  have hn : (R.map N).app (op q) ≫ Ee.hom.app (op q) =
      Ed.hom.app (op q) ≫ N.app (op q) :=
    congrArg (fun z => z.app (op q))
      ((curry (D := D) (J := J)).counitIso.hom.naturality N)
  have hi : N.app (op q) ≫ Pi.π (fun _ : op q ⟶ op e => Z) h.op =
      Pi.π (fun _ : op q ⟶ op d => Z) (t ≫ h).op := by
    change Pi.lift (fun j : op q ⟶ op e =>
      Pi.π (fun _ : op q ⟶ op d => Z) (j ≫ t.op)) ≫
        Pi.π (fun _ : op q ⟶ op e => Z) h.op = _
    simpa only [op_comp] using (Pi.lift_comp_π
      (fun j : op q ⟶ op e => Pi.π (fun _ : op q ⟶ op d => Z) (j ≫ t.op)) h.op)
  change (R.map N).app (op q) ≫
      (Ee.hom.app (op q) ≫ Pi.π (fun _ : op q ⟶ op e => Z) h.op) =
    Ed.hom.app (op q) ≫ Pi.π (fun _ : op q ⟶ op d => Z) (t ≫ h).op
  calc
    _ = ((R.map N).app (op q) ≫ Ee.hom.app (op q)) ≫
        Pi.π (fun _ : op q ⟶ op e => Z) h.op := (CategoryTheory.Category.assoc _ _ _).symm
    _ = (Ed.hom.app (op q) ≫ N.app (op q)) ≫
        Pi.π (fun _ : op q ⟶ op e => Z) h.op :=
      congrArg (· ≫ Pi.π (fun _ : op q ⟶ op e => Z) h.op) hn
    _ = Ed.hom.app (op q) ≫
        (N.app (op q) ≫ Pi.π (fun _ : op q ⟶ op e => Z) h.op) := CategoryTheory.Category.assoc _ _ _
    _ = _ := congrArg (Ed.hom.app (op q) ≫ ·) hi

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
private theorem assist_nestedTensor_index {d e : D} (t : d ⟶ e)
    (A : SimplicialPresheaf.{u} J) (K : SSet.{u}) :
    assistParameterFreeMap (J := J) t ((scalarTensor.obj A).obj K) ≫
        (freeTensorNestedIso (J := J) e A K).hom =
      (freeTensorNestedIso (J := J) d A K).hom ≫
        ((CategoryTheory.Functor.whiskeringRight Dᵒᵖ (SimplicialPresheaf.{u} J)
          (SimplicialPresheaf.{u} J)).obj (scalarTensorFixed (D := J) K)).map
            (assistParameterFreeMap (J := J) t A) := by
  apply NatTrans.ext
  funext q
  apply Sigma.hom_ext
  intro h
  let T := scalarTensorFixed (D := J) K
  let NK : (∐ fun _ : op d ⟶ q => (scalarTensor.obj A).obj K) ⟶
      (∐ fun _ : op e ⟶ q => (scalarTensor.obj A).obj K) :=
    (assistParameterFreeMap (J := J) t ((scalarTensor.obj A).obj K)).app q
  let NA : (∐ fun _ : op d ⟶ q => A) ⟶ (∐ fun _ : op e ⟶ q => A) :=
    (assistParameterFreeMap (J := J) t A).app q
  let αd := (tensorCoproductIso (J := J) d q A K).hom
  let αe := (tensorCoproductIso (J := J) e q A K).hom
  have hK : Sigma.ι (fun _ : op d ⟶ q => (scalarTensor.obj A).obj K) h ≫ NK =
      Sigma.ι (fun _ : op e ⟶ q => (scalarTensor.obj A).obj K) (t.op ≫ h) := by
    change Sigma.ι (fun _ : op d ⟶ q => (scalarTensor.obj A).obj K) h ≫
      Sigma.desc (fun j : op d ⟶ q => Sigma.ι
        (fun _ : op e ⟶ q => (scalarTensor.obj A).obj K) (t.op ≫ j)) = _
    exact Sigma.ι_comp_desc _ _
  have hA : Sigma.ι (fun _ : op d ⟶ q => A) h ≫ NA =
      Sigma.ι (fun _ : op e ⟶ q => A) (t.op ≫ h) := by
    change Sigma.ι (fun _ : op d ⟶ q => A) h ≫
      Sigma.desc (fun j : op d ⟶ q => Sigma.ι (fun _ : op e ⟶ q => A) (t.op ≫ j)) = _
    exact Sigma.ι_comp_desc _ _
  change Sigma.ι (fun _ : op d ⟶ q => (scalarTensor.obj A).obj K) h ≫ (NK ≫ αe) =
    (Sigma.ι (fun _ : op d ⟶ q => (scalarTensor.obj A).obj K) h ≫ αd) ≫ T.map NA
  have hd : Sigma.ι (fun _ : op d ⟶ q => (scalarTensor.obj A).obj K) h ≫ αd =
      T.map (Sigma.ι (fun _ : op d ⟶ q => A) h) :=
    tensorCoproductIso_hom_ι (J := J) d q A K h
  have he : Sigma.ι (fun _ : op e ⟶ q => (scalarTensor.obj A).obj K) (t.op ≫ h) ≫ αe =
      T.map (Sigma.ι (fun _ : op e ⟶ q => A) (t.op ≫ h)) :=
    tensorCoproductIso_hom_ι (J := J) e q A K (t.op ≫ h)
  rw [← CategoryTheory.Category.assoc, hK, he, hd]
  exact (congrArg T.map hA.symm).trans (T.map_comp _ _)

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- Both source-parameter actions satisfy the original ordinary free/cofree transpose equations. -/
theorem ordinaryAdjunction_index {d e : D} (t : d ⟶ e)
    (A Z : SimplicialPresheaf.{u} J) (X : SimplicialPresheaf.{u} (D × J))
    (f : (free (J := J) e).obj A ⟶ X) (g : X ⟶ (cofree (J := J) d).obj Z) :
    (freeAdjunction (J := J) d).homEquiv A X (freeIndexMap (J := J) t A ≫ f) =
        (freeAdjunction (J := J) e).homEquiv A X f ≫
          (evaluationRestriction (J := J) t).app X ∧
    ((cofreeAdjunction (J := J) e).homEquiv X Z).symm (g ≫ cofreeIndexMap (J := J) t Z) =
        (evaluationRestriction (J := J) t).app X ≫
          ((cofreeAdjunction (J := J) d).homEquiv X Z).symm g := by
  constructor
  · rw [freeAdjunction_hom_characteristic,
      (evaluation (J := J) d).map_comp, ← Category.assoc,
      assist_freeIndex_inclusion]
    simpa only [Category.id_comp, _root_.Equiv.symm_apply_apply, evaluationRestriction] using
      freeAdjunction_inv_characteristic (J := J) e d t A X
        ((freeAdjunction (J := J) e).homEquiv A X f)
  · rw [cofreeAdjunction_inv_characteristic,
      (evaluation (J := J) e).map_comp, Category.assoc,
      assist_cofreeIndex_projection]
    simpa only [Category.comp_id, _root_.Equiv.apply_symm_apply, evaluationRestriction] using
      cofreeAdjunction_hom_characteristic (J := J) d e t X Z
        (((cofreeAdjunction (J := J) d).homEquiv X Z).symm g)

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- The original free-index transpose equation needs no unrelated map or outcome. -/
theorem freeAdjunction_index {d e : D} (t : d ⟶ e)
    (A : SimplicialPresheaf.{u} J) (X : SimplicialPresheaf.{u} (D × J))
    (f : (free (J := J) e).obj A ⟶ X) :
    (freeAdjunction (J := J) d).homEquiv A X (freeIndexMap (J := J) t A ≫ f) =
      (freeAdjunction (J := J) e).homEquiv A X f ≫
        (evaluationRestriction (J := J) t).app X :=
  (ordinaryAdjunction_index (J := J) t A ((evaluation (J := J) d).obj X) X f
    ((cofreeAdjunction (J := J) d).unit.app X)).1

omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- The original cofree-index transpose equation retains its actual inverse Hom direction. -/
theorem cofreeAdjunction_index {d e : D} (t : d ⟶ e)
    (X : SimplicialPresheaf.{u} (D × J)) (Z : SimplicialPresheaf.{u} J)
    (g : X ⟶ (cofree (J := J) d).obj Z) :
    ((cofreeAdjunction (J := J) e).homEquiv X Z).symm (g ≫ cofreeIndexMap (J := J) t Z) =
      (evaluationRestriction (J := J) t).app X ≫
        ((cofreeAdjunction (J := J) d).homEquiv X Z).symm g :=
  (ordinaryAdjunction_index (J := J) t ((evaluation (J := J) e).obj X) Z X
    ((freeAdjunction (J := J) e).counit.app X) g).2

set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} D] [Small.{u} J] [LocallySmall.{u} J] in
/-- The actual free tensor comparison retains every original parameter-index map. -/
theorem freeTensorIso_index {d e : D} (t : d ⟶ e)
    (A : SimplicialPresheaf.{u} J) (K : SSet.{u}) :
    freeIndexMap (J := J) t ((scalarTensor.obj A).obj K) ≫
        (freeTensorIso (J := J) e A).hom.app K =
      (freeTensorIso (J := J) d A).hom.app K ≫
        (scalarTensor.map (freeIndexMap (J := J) t A)).app K := by
  let C := (curry (D := D) (J := J)).inverse
  let Nd := (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op d)).obj A
  let Ne := (evaluationLeftAdjoint (SimplicialPresheaf.{u} J) (op e)).obj A
  let NK := assistParameterFreeMap (J := J) t ((scalarTensor.obj A).obj K)
  let NA := assistParameterFreeMap (J := J) t A
  let NT := ((Functor.whiskeringRight Dᵒᵖ (SimplicialPresheaf.{u} J)
    (SimplicialPresheaf.{u} J)).obj (scalarTensorFixed (D := J) K)).map NA
  let αd := (freeTensorNestedIso (J := J) d A K).hom
  let αe := (freeTensorNestedIso (J := J) e A K).hom
  let γd := (uncurryTensorIso (D := D) (J := J) K Nd).hom
  let γe := (uncurryTensorIso (D := D) (J := J) K Ne).hom
  let M := (scalarTensorFixed (D := D × J) K).map (C.map NA)
  have hN := assist_nestedTensor_index (J := J) t A K
  change NK ≫ αe = αd ≫ NT at hN
  have hU := (uncurryTensorNatural (D := D) (J := J) K).hom.naturality NA
  change C.map NT ≫ γe = γd ≫ M at hU
  change C.map NK ≫ (C.map αe ≫ γe) = (C.map αd ≫ γd) ≫ M
  calc
    _ = C.map (NK ≫ αe) ≫ γe := by rw [Functor.map_comp, CategoryTheory.Category.assoc]
    _ = C.map (αd ≫ NT) ≫ γe := by rw [hN]
    _ = C.map αd ≫ (C.map NT ≫ γe) := by rw [Functor.map_comp, CategoryTheory.Category.assoc]
    _ = C.map αd ≫ (γd ≫ M) := congrArg (C.map αd ≫ ·) hU
    _ = (C.map αd ≫ γd) ≫ M := (CategoryTheory.Category.assoc _ _ _).symm

/-- Free source-index naturality is the original evaluation restriction on the same target. -/
theorem freeHomIso_index {d e : D} (t : d ⟶ e) (A : SimplicialPresheaf.{u} J)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    innerHomPre (freeIndexMap (J := J) t A) Z ≫ (freeHomIso (J := J) d A Z).hom =
      (freeHomIso (J := J) e A Z).hom ≫
        innerHomPost A ((evaluationRestriction (J := J) t).app Z) := by
  let K := innerHom ((free (J := J) e).obj A) Z
  apply (scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)).symm.injective
  have hE := scalarTensorHomEquiv_source_symm (freeIndexMap (J := J) t A) K Z (𝟙 _)
  simp only [Category.id_comp] at hE
  have h0 := freeHomIso_untranspose (J := J) e A K Z (𝟙 _)
  simp only [Category.id_comp] at h0
  have hR := (scalarTensorHomAdjunction A).homEquiv_naturality_right_symm
    (freeHomIso (J := J) e A Z).hom ((evaluationRestriction (J := J) t).app Z)
  rw [scalarTensorHomAdjunction_homEquiv] at hR
  change (scalarTensorHomEquiv A K ((evaluation (J := J) d).obj Z)).symm
    ((freeHomIso (J := J) e A Z).hom ≫ innerHomPost A ((evaluationRestriction (J := J) t).app Z)) =
      (scalarTensorHomEquiv A K ((evaluation (J := J) e).obj Z)).symm
        (freeHomIso (J := J) e A Z).hom ≫ (evaluationRestriction (J := J) t).app Z at hR
  rw [freeHomIso_untranspose, hE, hR, h0, ← Category.assoc,
    ← freeTensorIso_index, Category.assoc]
  exact freeAdjunction_index (J := J) t ((scalarTensor.obj A).obj K) Z _

set_option backward.isDefEq.respectTransparency false in
/-- Cofree source-index naturality retains the original opposite-site restriction. -/
theorem cofreeHomIso_index {d e : D} (t : d ⟶ e)
    (A : SimplicialPresheaf.{u} (D × J)) (Z : SimplicialPresheaf.{u} J) :
    innerHomPost A (cofreeIndexMap (J := J) t Z) ≫ (cofreeHomIso (J := J) e A Z).hom =
      (cofreeHomIso (J := J) d A Z).hom ≫
        innerHomPre ((evaluationRestriction (J := J) t).app A) Z := by
  let K := innerHom A ((cofree (J := J) d).obj Z)
  apply (scalarTensorHomEquiv ((evaluation (J := J) e).obj A) K Z).symm.injective
  have h0 := cofreeHomIso_untranspose (J := J) d A K Z (𝟙 _)
  simp only [Category.id_comp] at h0
  have hE := (scalarTensorHomAdjunction A).homEquiv_naturality_right_symm
    (𝟙 (innerHom A ((cofree (J := J) d).obj Z))) (cofreeIndexMap (J := J) t Z)
  rw [scalarTensorHomAdjunction_homEquiv] at hE
  simp only [Category.id_comp] at hE
  change (scalarTensorHomEquiv A K ((cofree (J := J) e).obj Z)).symm
    (innerHomPost A (cofreeIndexMap (J := J) t Z)) =
      (scalarTensorHomEquiv A K ((cofree (J := J) d).obj Z)).symm (𝟙 _) ≫
        cofreeIndexMap (J := J) t Z at hE
  have ht : (evaluationTensorIso (J := J) e A).inv.app K ≫
      (evaluationRestriction (J := J) t).app ((scalarTensor.obj A).obj K) =
      (scalarTensor.map ((evaluationRestriction (J := J) t).app A)).app K ≫
        (evaluationTensorIso (J := J) d A).inv.app K := by
    ext j n q
    rfl
  rw [cofreeHomIso_untranspose, scalarTensorHomEquiv_source_symm, h0, hE,
    cofreeAdjunction_index,
    ← Category.assoc, ht, Category.assoc]

/-- Both inverse index directions follow from the same original free/cofree source squares. -/
theorem freeHomIso_index_inv {d e : D} (t : d ⟶ e) (A : SimplicialPresheaf.{u} J)
    (Z : SimplicialPresheaf.{u} (D × J)) :
    innerHomPost A ((evaluationRestriction (J := J) t).app Z) ≫
        (freeHomIso (J := J) d A Z).inv =
      (freeHomIso (J := J) e A Z).inv ≫ innerHomPre (freeIndexMap (J := J) t A) Z := by
  apply (cancel_mono (freeHomIso (J := J) d A Z).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    freeHomIso_index, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The inverse cofree index direction retains original evaluation and cofree maps. -/
theorem cofreeHomIso_index_inv {d e : D} (t : d ⟶ e)
    (A : SimplicialPresheaf.{u} (D × J)) (Z : SimplicialPresheaf.{u} J) :
    innerHomPre ((evaluationRestriction (J := J) t).app A) Z ≫
        (cofreeHomIso (J := J) e A Z).inv =
      (cofreeHomIso (J := J) d A Z).inv ≫ innerHomPost A (cofreeIndexMap (J := J) t Z) := by
  apply (cancel_mono (cofreeHomIso (J := J) e A Z).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    cofreeHomIso_index, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Every original inner-simplex operator commutes in both directions of the free comparison. -/
theorem freeHomIso_operator (d : D) (A : SimplicialPresheaf.{u} J)
    (Z : SimplicialPresheaf.{u} (D × J))
    {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) :
    (innerHom ((free (J := J) d).obj A) Z).map a ≫
        (freeHomIso (J := J) d A Z).hom.app m =
      (freeHomIso (J := J) d A Z).hom.app n ≫
        (innerHom A ((evaluation (J := J) d).obj Z)).map a ∧
    (innerHom A ((evaluation (J := J) d).obj Z)).map a ≫
        (freeHomIso (J := J) d A Z).inv.app m =
      (freeHomIso (J := J) d A Z).inv.app n ≫
        (innerHom ((free (J := J) d).obj A) Z).map a :=
  ⟨(freeHomIso (J := J) d A Z).hom.naturality a,
    (freeHomIso (J := J) d A Z).inv.naturality a⟩

/-- Every original inner-simplex operator commutes in both directions of the cofree comparison. -/
theorem cofreeHomIso_operator (d : D) (A : SimplicialPresheaf.{u} (D × J))
    (Z : SimplicialPresheaf.{u} J) {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) :
    (innerHom A ((cofree (J := J) d).obj Z)).map a ≫
        (cofreeHomIso (J := J) d A Z).hom.app m =
      (cofreeHomIso (J := J) d A Z).hom.app n ≫
        (innerHom ((evaluation (J := J) d).obj A) Z).map a ∧
    (innerHom ((evaluation (J := J) d).obj A) Z).map a ≫
        (cofreeHomIso (J := J) d A Z).inv.app m =
      (cofreeHomIso (J := J) d A Z).inv.app n ≫
        (innerHom A ((cofree (J := J) d).obj Z)).map a :=
  ⟨(cofreeHomIso (J := J) d A Z).hom.naturality a,
    (cofreeHomIso (J := J) d A Z).inv.naturality a⟩

/-- Both original scalar mapping-end isomorphisms retain their full inverse roundtrips. -/
theorem mappingEndIso_roundtrips (d : D) (A Z : SimplicialPresheaf.{u} J)
    (X : SimplicialPresheaf.{u} (D × J)) :
    (freeHomIso (J := J) d A X).hom ≫ (freeHomIso (J := J) d A X).inv = 𝟙 _ ∧
    (freeHomIso (J := J) d A X).inv ≫ (freeHomIso (J := J) d A X).hom = 𝟙 _ ∧
    (cofreeHomIso (J := J) d X Z).hom ≫ (cofreeHomIso (J := J) d X Z).inv = 𝟙 _ ∧
    (cofreeHomIso (J := J) d X Z).inv ≫ (cofreeHomIso (J := J) d X Z).hom = 𝟙 _ :=
  ⟨Iso.hom_inv_id _, Iso.inv_hom_id _, Iso.hom_inv_id _, Iso.inv_hom_id _⟩


/-- All four actual forward/inverse cofree Arrow fields retain the original source endpoints. -/
theorem cofreePrecompArrowIso_laws (d : D)
    {A B : SimplicialPresheaf.{u} (D × J)} (a : A ⟶ B) (Z : SimplicialPresheaf.{u} J) :
    (cofreePrecompArrowIso (J := J) d a Z).hom.left = (cofreeHomIso (J := J) d B Z).hom ∧
    (cofreePrecompArrowIso (J := J) d a Z).hom.right = (cofreeHomIso (J := J) d A Z).hom ∧
    (cofreePrecompArrowIso (J := J) d a Z).inv.left = (cofreeHomIso (J := J) d B Z).inv ∧
    (cofreePrecompArrowIso (J := J) d a Z).inv.right = (cofreeHomIso (J := J) d A Z).inv :=
  ⟨rfl, rfl, rfl, rfl⟩



end SimplicialPresheaf.LocalizationDiagram
