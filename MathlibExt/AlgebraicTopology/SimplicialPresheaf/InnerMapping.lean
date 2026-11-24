/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
# Fixed-universe simplicial presheaf ends

All mapping objects are actual ends in the fixed scalar universe. The original site and its
natural transformations are retained even when their declared object or Hom universes are
larger. Scalar adjunctions and the genuine presheaf exponential use these original ends.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed MonoidalCategory Opposite
open scoped MonoidalClosed Simplicial

namespace SimplicialPresheaf

section Ends

variable {J : Type w} [Category.{v} J] [Small.{u} J] [LocallySmall.{u} J]

/-- The original small-label end exists through native products and an equalizer. -/
abbrev hasEnd (F : Jᵒᵖ ⥤ J ⥤ SSet.{u}) : HasEnd F := by
  let : HasProductsOfShape J SSet.{u} :=
    hasProductsOfShape_of_small (C := SSet.{u}) (β := J)
  let : HasProductsOfShape (Arrow J) SSet.{u} :=
    hasProductsOfShape_of_small (C := SSet.{u}) (β := Arrow J)
  let I := multicospanIndexEnd F
  let : HasProduct I.left := by
    dsimp [I, multicospanIndexEnd, multicospanShapeEnd]
    infer_instance
  let : HasProduct I.right := by
    dsimp [I, multicospanIndexEnd, multicospanShapeEnd]
    infer_instance
  exact ⟨⟨⟨I.multiforkEquivPiFork.inverse.obj (limit.cone (parallelPair I.fstPiMap I.sndPiMap)),
    IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩⟩⟩

/-- The original under-category ends also exist in the fixed scalar universe. -/
abbrev hasFunctorEnrichedHom (A Z : J ⥤ SSet.{u}) :
    Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} A Z := by
  intro j
  let : Small.{u} (Under j) := by
    change Small.{u} (StructuredArrow j (𝟭 J))
    infer_instance
  let : LocallySmall.{u} (Under j) := locallySmall_of_faithful (Under.forget j)
  exact hasEnd (Enriched.FunctorCategory.diagram SSet.{u}
    (Under.forget j ⋙ A) (Under.forget j ⋙ Z))

end Ends

attribute [local instance] hasEnd hasFunctorEnrichedHom

variable {D : Type w} [Category.{v} D] [smallD : Small.{u} D] [localD : LocallySmall.{u} D]

/-- The original presheaf category is enriched in SSet of the fixed value universe. -/
@[instance_reducible]
def scalarEnrichment : EnrichedOrdinaryCategory SSet.{u} (SimplicialPresheaf.{u} D) :=
  Enriched.FunctorCategory.enrichedOrdinaryCategory
    (V := SSet.{u}) (J := Dᵒᵖ) (C := SSet.{u})

attribute [local instance] scalarEnrichment

/-- The actual scalar end of the original presheaf internal-Hom diagram. -/
abbrev innerHom (A Z : SimplicialPresheaf.{u} D) : SSet.{u} :=
  Enriched.FunctorCategory.enrichedHom SSet.{u} A Z

/-- The mapping bifunctor on original presheaves and natural transformations. -/
def innerHomFunctor : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  eHomFunctor SSet.{u} (SimplicialPresheaf.{u} D)

/-- The actual end projection at an original site object. -/
abbrev innerHomπ (A Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    innerHom A Z ⟶ (ihom (A.obj d)).obj (Z.obj d) :=
  Enriched.FunctorCategory.enrichedHomπ SSet.{u} A Z d

/-- The end equation retains each original site arrow and both original presheaf maps. -/
@[reassoc]
theorem innerHom_condition (A Z : SimplicialPresheaf.{u} D) {i j : Dᵒᵖ} (g : i ⟶ j) :
    innerHomπ A Z i ≫ (ihom (A.obj i)).map (Z.map g) =
      innerHomπ A Z j ≫ (pre (A.map g)).app (Z.obj j) := by
  simpa only [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] using
    Enriched.FunctorCategory.enrichedHom_condition SSet.{u} A Z g

/-- Source precomposition acts on the actual original scalar end. -/
def innerHomPre {A A' : SimplicialPresheaf.{u} D} (f : A' ⟶ A)
    (Z : SimplicialPresheaf.{u} D) : innerHom A Z ⟶ innerHom A' Z :=
  eHomWhiskerRight SSet.{u} f Z

/-- Target postcomposition acts on the actual original scalar end. -/
def innerHomPost (A : SimplicialPresheaf.{u} D) {Z Z' : SimplicialPresheaf.{u} D}
    (g : Z ⟶ Z') : innerHom A Z ⟶ innerHom A Z' :=
  eHomWhiskerLeft SSet.{u} A g

/-- The original under-end presheaf Hom bifunctor used by the native closed structure. -/
def underHomFunctor : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤
    SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D := by
  letI : EnrichedOrdinaryCategory (SimplicialPresheaf.{u} D) (SimplicialPresheaf.{u} D) :=
    Enriched.FunctorCategory.functorEnrichedOrdinaryCategory
      (V := SSet.{u}) (J := Dᵒᵖ) (C := SSet.{u})
  exact eHomFunctor (SimplicialPresheaf.{u} D) (SimplicialPresheaf.{u} D)

/-- The native Cartesian adjunction with the actual under-end right adjoint. -/
def underHomAdjunction (A : SimplicialPresheaf.{u} D) :
    tensorLeft A ⊣ underHomFunctor.obj (op A) :=
  MonoidalClosed.FunctorCategory.adj A

/-- End projections detect equality of original scalar maps. -/
@[ext]
theorem innerHom_ext {A Z : SimplicialPresheaf.{u} D} {K : SSet.{u}}
    {f g : K ⟶ innerHom A Z}
    (h : ∀ d : Dᵒᵖ, f ≫ innerHomπ A Z d = g ≫ innerHomπ A Z d) : f = g :=
  end_.hom_ext h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Source precomposition is the original component precomposition at every end projection. -/
@[reassoc (attr := simp)]
theorem innerHomPre_π {A A' : SimplicialPresheaf.{u} D} (f : A' ⟶ A)
    (Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    innerHomPre f Z ≫ innerHomπ A' Z d =
      innerHomπ A Z d ≫ (pre (f.app d)).app (Z.obj d) := by
  change (λ_ (innerHom A Z)).inv ≫
    (Enriched.FunctorCategory.homEquiv SSet.{u} f ▷ innerHom A Z) ≫
      Enriched.FunctorCategory.enrichedComp SSet.{u} A' A Z ≫ innerHomπ A' Z d = _
  simp only [innerHomπ, Enriched.FunctorCategory.enrichedHomπ,
    Enriched.FunctorCategory.enrichedComp_π, tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, Enriched.FunctorCategory.homEquiv_apply_π,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  change innerHomπ A Z d ≫ eHomWhiskerRight SSet.{u} (f.app d) (Z.obj d) = _
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Target postcomposition is the original component postcomposition at every end projection. -/
@[reassoc (attr := simp)]
theorem innerHomPost_π (A : SimplicialPresheaf.{u} D) {Z Z' : SimplicialPresheaf.{u} D}
    (g : Z ⟶ Z') (d : Dᵒᵖ) :
    innerHomPost A g ≫ innerHomπ A Z' d =
      innerHomπ A Z d ≫ (ihom (A.obj d)).map (g.app d) := by
  change (ρ_ (innerHom A Z)).inv ≫
    innerHom A Z ◁ (Enriched.FunctorCategory.homEquiv SSet.{u} g) ≫
      Enriched.FunctorCategory.enrichedComp SSet.{u} A Z Z' ≫ innerHomπ A Z' d = _
  simp only [innerHomπ, Enriched.FunctorCategory.enrichedHomπ,
    Enriched.FunctorCategory.enrichedComp_π, tensorHom_def', Category.assoc]
  rw [← whiskerLeft_comp_assoc, Enriched.FunctorCategory.homEquiv_apply_π,
    whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  change innerHomπ A Z d ≫ eHomWhiskerLeft SSet.{u} (A.obj d) (g.app d) = _
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]

/-- Precomposition preserves the original identity. -/
@[simp]
theorem innerHomPre_id (A Z : SimplicialPresheaf.{u} D) :
    innerHomPre (𝟙 A) Z = 𝟙 (innerHom A Z) := eHomWhiskerRight_id _ _ _

/-- Precomposition preserves the original composition with its contravariant order. -/
@[reassoc]
theorem innerHomPre_comp {A A' A'' : SimplicialPresheaf.{u} D}
    (f : A' ⟶ A) (g : A'' ⟶ A') (Z : SimplicialPresheaf.{u} D) :
    innerHomPre f Z ≫ innerHomPre g Z = innerHomPre (g ≫ f) Z :=
  (eHomWhiskerRight_comp _ _ _ _).symm

/-- Postcomposition preserves the original identity. -/
@[simp]
theorem innerHomPost_id (A Z : SimplicialPresheaf.{u} D) :
    innerHomPost A (𝟙 Z) = 𝟙 (innerHom A Z) := eHomWhiskerLeft_id _ _ _

/-- Postcomposition preserves the original composition. -/
@[reassoc]
theorem innerHomPost_comp (A : SimplicialPresheaf.{u} D)
    {Z Z' Z'' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') (h : Z' ⟶ Z'') :
    innerHomPost A g ≫ innerHomPost A h = innerHomPost A (g ≫ h) :=
  (eHomWhiskerLeft_comp _ _ _ _).symm

/-- The original source and target mapping actions commute. -/
@[reassoc]
theorem innerHom_exchange {A A' Z Z' : SimplicialPresheaf.{u} D}
    (f : A' ⟶ A) (g : Z ⟶ Z') :
    innerHomPre f Z ≫ innerHomPost A' g = innerHomPost A g ≫ innerHomPre f Z' :=
  (eHom_whisker_exchange SSet.{u} f g).symm

/-- Original natural transformations identify with the actual end's zero simplices. -/
def innerHomHomEquiv (A Z : SimplicialPresheaf.{u} D) :
    (A ⟶ Z) ≃ (innerHom A Z).obj (op ⦋0⦌) :=
  (Enriched.FunctorCategory.homEquiv (V := SSet.{u}) (F₁ := A) (F₂ := Z)).trans
    (SSet.unitHomEquiv (innerHom A Z))

/-- Ordinary-map zero simplices preserve every source precomposition. -/
@[simp]
theorem innerHomHomEquiv_precomp {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (g : B ⟶ Z) :
    (innerHomPre f Z).app (op ⦋0⦌) (innerHomHomEquiv B Z g) =
      innerHomHomEquiv A Z (f ≫ g) := by
  have h : eHomEquiv SSet.{u} g ≫ eHomWhiskerRight SSet.{u} f Z =
      eHomEquiv SSet.{u} (f ≫ g) := by
    dsimp [eHomWhiskerRight]
    rw [leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc, ← eHomEquiv_comp]
  change SSet.unitHomEquiv _ (eHomEquiv SSet.{u} g ≫ eHomWhiskerRight SSet.{u} f Z) =
    SSet.unitHomEquiv _ (eHomEquiv SSet.{u} (f ≫ g))
  rw [h]

/-- Ordinary-map zero simplices preserve every target postcomposition. -/
@[simp]
theorem innerHomHomEquiv_postcomp (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') (f : A ⟶ Z) :
    (innerHomPost A g).app (op ⦋0⦌) (innerHomHomEquiv A Z f) =
      innerHomHomEquiv A Z' (f ≫ g) := by
  have hu : (ρ_ (𝟙_ SSet.{u})).inv = (λ_ (𝟙_ SSet.{u})).inv :=
    (Iso.inv_eq_inv _ _).mpr unitors_equal.symm
  have h : eHomEquiv SSet.{u} f ≫ eHomWhiskerLeft SSet.{u} A g =
      eHomEquiv SSet.{u} (f ≫ g) := by
    dsimp [eHomWhiskerLeft]
    rw [rightUnitor_inv_naturality_assoc, ← tensorHom_def_assoc, hu, ← eHomEquiv_comp]
  change SSet.unitHomEquiv _ (eHomEquiv SSet.{u} f ≫ eHomWhiskerLeft SSet.{u} A g) =
    SSet.unitHomEquiv _ (eHomEquiv SSet.{u} (f ≫ g))
  rw [h]

/-- Ordinary original-site limits exist in the fixed coefficient universe. -/
instance hasLimitsOfSite : HasLimitsOfShape Dᵒᵖ SSet.{u} :=
  hasLimitsOfShape_of_essentiallySmall (J := Dᵒᵖ) (C := SSet.{u})

/-- The actual under-end limit has the original scalar mapping end as cone point. -/
def innerHomLimitIso (A Z : SimplicialPresheaf.{u} D) :
    limit ((underHomFunctor.obj (op A)).obj Z) ≅ innerHom A Z :=
  limit.isoLimitCone ⟨_, Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet.{u} A Z⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem innerHomLimitIso_hom_precomp (A Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    (innerHomLimitIso A Z).hom ≫
        Enriched.FunctorCategory.precompEnrichedHom SSet.{u} A Z (Under.forget d) =
      limit.π ((underHomFunctor.obj (op A)).obj Z) d := by
  exact limit.isoLimitCone_hom_π
    ⟨_, Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet.{u} A Z⟩ d

/-- Tensor followed by the original under-end and ordinary limit, using native adjunctions. -/
def scalarTensorLimitAdjunction (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj A ⊣ underHomFunctor.obj (op A) ⋙ lim :=
  (constLimAdj (J := Dᵒᵖ) (C := SSet.{u})).comp (underHomAdjunction A)

/-- The original scalar tensor-Hom equivalence through the actual under-end limit. -/
def scalarTensorHomEquiv (A : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (Z : SimplicialPresheaf.{u} D) :
    (((scalarTensor.obj A).obj K) ⟶ Z) ≃ (K ⟶ innerHom A Z) :=
  ((scalarTensorLimitAdjunction A).homEquiv K Z).trans
    (Iso.homCongr (Iso.refl K) (innerHomLimitIso A Z))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transposition is the original component curry at each actual end projection. -/
@[reassoc (attr := simp)]
theorem scalarTensorHomEquiv_π (A : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (Z : SimplicialPresheaf.{u} D) (f : ((scalarTensor.obj A).obj K) ⟶ Z) (d : Dᵒᵖ) :
    scalarTensorHomEquiv A K Z f ≫ innerHomπ A Z d = curry (f.app d) := by
  have hp :
      Enriched.FunctorCategory.precompEnrichedHom SSet.{u} A Z (Under.forget d) ≫
        Enriched.FunctorCategory.enrichedHomπ SSet.{u}
          (Under.forget d ⋙ A) (Under.forget d ⋙ Z) (Under.mk (𝟙 d)) =
      innerHomπ A Z d := by
    simp [Enriched.FunctorCategory.precompEnrichedHom,
      Enriched.FunctorCategory.precompEnrichedHom', innerHomπ]
  change (scalarTensorLimitAdjunction A).homEquiv K Z f ≫
    (innerHomLimitIso A Z).hom ≫ innerHomπ A Z d = _
  rw [← hp, innerHomLimitIso_hom_precomp_assoc]
  simp [scalarTensorLimitAdjunction, Adjunction.comp_homEquiv,
    underHomAdjunction, MonoidalClosed.FunctorCategory.adj,
    Adjunction.mkOfHomEquiv_homEquiv, Adjunction.mk'_homEquiv, constLimAdj,
    MonoidalClosed.FunctorCategory.homEquiv]
  have hf : ∀ {i j : Under d} (g : i ⟶ j),
      curry (f.app i.right) ≫
          ((Enriched.FunctorCategory.diagram SSet.{u}
            (Under.forget d ⋙ A) (Under.forget d ⋙ Z)).obj (op i)).map g =
        curry (f.app j.right) ≫
          ((Enriched.FunctorCategory.diagram SSet.{u}
            (Under.forget d ⋙ A) (Under.forget d ⋙ Z)).map g.op).app j := by
    intro i j g
    simp only [Enriched.FunctorCategory.diagram_obj_map,
      Enriched.FunctorCategory.diagram_map_app,
      MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    change curry (f.app i.right) ≫ (ihom (A.obj i.right)).map (Z.map g.right) =
      curry (f.app j.right) ≫ (pre (A.map g.right)).app (Z.obj j.right)
    rw [← curry_natural_right, curry_pre_app]
    congr 1
    exact (f.naturality g.right).symm
  change end_.lift
    (F := Enriched.FunctorCategory.diagram SSet.{u}
      (Under.forget d ⋙ A) (Under.forget d ⋙ Z))
    (fun k : Under d => curry (f.app k.right)) (@hf) ≫
      Enriched.FunctorCategory.enrichedHomπ SSet.{u}
        (Under.forget d ⋙ A) (Under.forget d ⋙ Z) (Under.mk (𝟙 d)) = curry (f.app d)
  simp only [Enriched.FunctorCategory.enrichedHomπ, end_.lift_π]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar transposition retains original precomposition by every scalar map. -/
theorem scalarTensorHomEquiv_naturality_left_symm (A : SimplicialPresheaf.{u} D)
    {K L : SSet.{u}} (k : K ⟶ L) (Z : SimplicialPresheaf.{u} D)
    (g : L ⟶ innerHom A Z) :
    (scalarTensorHomEquiv A K Z).symm (k ≫ g) =
      (scalarTensor.obj A).map k ≫ (scalarTensorHomEquiv A L Z).symm g := by
  apply (scalarTensorHomEquiv A K Z).injective
  apply innerHom_ext
  intro d
  simp only [Equiv.apply_symm_apply, scalarTensorHomEquiv_π, NatTrans.comp_app,
    scalarTensor_scalar_map, curry_natural_left, Category.assoc]
  rw [← scalarTensorHomEquiv_π A L Z ((scalarTensorHomEquiv A L Z).symm g) d,
    Equiv.apply_symm_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar transposition retains original postcomposition by every presheaf map. -/
theorem scalarTensorHomEquiv_naturality_right (A : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) {Z Z' : SimplicialPresheaf.{u} D}
    (f : ((scalarTensor.obj A).obj K) ⟶ Z) (g : Z ⟶ Z') :
    scalarTensorHomEquiv A K Z' (f ≫ g) =
      scalarTensorHomEquiv A K Z f ≫ (innerHomFunctor.obj (op A)).map g := by
  apply innerHom_ext
  intro d
  change scalarTensorHomEquiv A K Z' (f ≫ g) ≫ innerHomπ A Z' d =
    scalarTensorHomEquiv A K Z f ≫ innerHomPost A g ≫ innerHomπ A Z' d
  simp only [scalarTensorHomEquiv_π, NatTrans.comp_app, innerHomPost_π]
  rw [← Category.assoc, scalarTensorHomEquiv_π, curry_natural_right]

/-- The actual scalar tensor/end adjunction on original presheaves. -/
def scalarTensorHomAdjunction (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj A ⊣ innerHomFunctor.obj (op A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := scalarTensorHomEquiv A
      homEquiv_naturality_left_symm := by
        intro K L Z k g
        exact scalarTensorHomEquiv_naturality_left_symm A k Z g
      homEquiv_naturality_right := by
        intro K Z Z' f g
        exact scalarTensorHomEquiv_naturality_right A K f g }

/-- The actual adjunction uses the original scalar transposition. -/
theorem scalarTensorHomAdjunction_homEquiv (A : SimplicialPresheaf.{u} D) :
    (scalarTensorHomAdjunction A).homEquiv = scalarTensorHomEquiv A :=
  Adjunction.mkOfHomEquiv_homEquiv _

omit smallD localD

/-- The scalar cotensor is native coefficient internal-Hom postcomposition. -/
def scalarCotensor : SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D :=
  internalHom (C := SSet.{u}) ⋙
    CategoryTheory.Functor.whiskeringRight Dᵒᵖ SSet.{u} SSet.{u}

/-- Cotensor has the original value in the fixed scalar universe. -/
theorem scalarCotensor_obj (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarCotensor.obj (op K)).obj Z).obj d = (ihom K).obj (Z.obj d) := rfl

/-- Cotensor keeps every original site restriction map. -/
theorem scalarCotensor_site_map (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    {d e : Dᵒᵖ} (g : d ⟶ e) :
    ((scalarCotensor.obj (op K)).obj Z).map g = (ihom K).map (Z.map g) := rfl

/-- Cotensor keeps every original target natural map. -/
theorem scalarCotensor_target_map (K : SSet.{u}) {Z Z' : SimplicialPresheaf.{u} D}
    (g : Z ⟶ Z') (d : Dᵒᵖ) :
    ((scalarCotensor.obj (op K)).map g).app d = (ihom K).map (g.app d) := rfl

/-- A scalar map acts contravariantly by the actual coefficient precomposition. -/
theorem scalarCotensor_scalar_map {K L : SSet.{u}} (k : K ⟶ L)
    (Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    (((scalarCotensor.map k.op).app Z).app d) = (pre k).app (Z.obj d) := by
  rfl

/-- The fixed-scalar tensor is the same native pointwise tensor as the original bifunctor. -/
def scalarTensorFixed (K : SSet.{u}) : SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D :=
  CategoryTheory.Functor.whiskeringRight Dᵒᵖ SSet.{u} SSet.{u} |>.obj (tensorRight K)

/-- The fixed-scalar tensor retains the original selected tensor object. -/
theorem scalarTensorFixed_obj (K : SSet.{u}) (A : SimplicialPresheaf.{u} D) :
    (scalarTensorFixed K).obj A = (scalarTensor.obj A).obj K := rfl

/-- The fixed-scalar tensor retains the original selected natural-map tensor. -/
theorem scalarTensorFixed_map (K : SSet.{u}) {A A' : SimplicialPresheaf.{u} D}
    (f : A ⟶ A') :
    (scalarTensorFixed K).map f = (scalarTensor.map f).app K := rfl

/-- The original tensor/cotensor adjunction is the native coefficient adjunction whiskered
through the original site, with its actual braiding comparison. -/
def scalarTensorCotensorAdjunction (K : SSet.{u}) :
    scalarTensorFixed (D := D) K ⊣ (scalarCotensor (D := D)).obj (op K) := by
  let e : tensorLeft (C := SSet.{u}) K ≅ tensorRight (C := SSet.{u}) K :=
    NatIso.ofComponents (fun X : SSet.{u} => β_ K X) (by
      intro X Y f
      exact BraidedCategory.braiding_naturality_right (X := K) f)
  exact ((ihom.adjunction K).ofNatIsoLeft e).whiskerRight Dᵒᵖ

include localD

/-- Evaluate the original representable tensor at the original identity Hom. -/
def discreteYonedaTensorEval (d : D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (f : (discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) ⟶ Z) :
    K ⟶ Z.obj (op d) where
  app Δ := ↾fun k => (f.app (op d)).app Δ
    ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d), k)
  naturality Δ Δ' δ := by
    ext k
    change (f.app (op d)).app Δ'
      ((discreteYonedaObjEquiv d (op d) Δ').symm (𝟙 d), K.map δ k) =
      (Z.obj (op d)).map δ ((f.app (op d)).app Δ
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d), k))
    have h := NatTrans.naturality_apply (D := Type u) (f.app (op d)) δ
      (show ((discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K).obj
          (op d)).obj Δ from
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d), k))
    change (f.app (op d)).app Δ'
      ((discreteYonedaObjEquiv d (op d) Δ').symm (𝟙 d), K.map δ k) =
      (Z.obj (op d)).map δ ((f.app (op d)).app Δ
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d), k)) at h
    exact h

/-- Extend an original scalar map along each original representing Hom. -/
def discreteYonedaTensorLift (d : D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (g : K ⟶ Z.obj (op d)) :
    (discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) ⟶ Z where
  app a :=
    { app Δ := ↾fun z =>
        (Z.map (discreteYonedaObjEquiv d a Δ z.1).op).app Δ (g.app Δ z.2)
      naturality Δ Δ' δ := by
        ext z
        rcases z with ⟨h, k⟩
        change (Z.map (discreteYonedaObjEquiv d a Δ h).op).app Δ' (g.app Δ' (K.map δ k)) =
          (Z.obj a).map δ
            ((Z.map (discreteYonedaObjEquiv d a Δ h).op).app Δ (g.app Δ k))
        rw [g.naturality_apply δ k]
        exact (Z.map (discreteYonedaObjEquiv d a Δ h).op).naturality_apply δ (g.app Δ k) }
  naturality a b η := by
    ext Δ z
    rcases z with ⟨h, k⟩
    change (Z.map (discreteYonedaObjEquiv d b Δ
      (((discreteYoneda.obj d).map η).app Δ h)).op).app Δ (g.app Δ k) =
      (Z.map η).app Δ ((Z.map (discreteYonedaObjEquiv d a Δ h).op).app Δ (g.app Δ k))
    rw [discreteYoneda_obj_map, op_comp, Quiver.Hom.op_unop, Functor.map_comp]
    rfl

/-- The original representable tensor has the scalar evaluation Hom equivalence. -/
def discreteYonedaTensorHomEquiv (d : D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) :
    ((discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) ⟶ Z) ≃
      (K ⟶ Z.obj (op d)) where
  toFun := discreteYonedaTensorEval d K Z
  invFun := discreteYonedaTensorLift d K Z
  left_inv f := by
    ext a Δ z
    rcases z with ⟨h, k⟩
    let t := discreteYonedaObjEquiv d a Δ h
    have hid : (((discreteYoneda.obj d).map t.op).app Δ)
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d)) = h := by
      apply (discreteYonedaObjEquiv d a Δ).injective
      rw [discreteYoneda_obj_map, Equiv.apply_symm_apply]
      simp [t]
    have hn := congrArg (fun q => q.app Δ
      ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d), k)) (f.naturality t.op)
    change (f.app a).app Δ
      ((((discreteYoneda.obj d).map t.op).app Δ)
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d)), k) =
      (Z.map t.op).app Δ ((f.app (op d)).app Δ
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d), k)) at hn
    rw [hid] at hn
    exact hn.symm
  right_inv g := by
    ext Δ k
    change (Z.map ((discreteYonedaObjEquiv d (op d) Δ)
      ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d))).op).app Δ (g.app Δ k) = g.app Δ k
    rw [Equiv.apply_symm_apply]
    simp

/-- Scalar evaluation is natural in every original scalar map. -/
theorem discreteYonedaTensorHomEquiv_scalar (d : D) {K L : SSet.{u}} (k : K ⟶ L)
    (Z : SimplicialPresheaf.{u} D)
    (f : (discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj L) ⟶ Z) :
    discreteYonedaTensorHomEquiv d K Z
        (discreteYoneda.obj d ◁ (CategoryTheory.Functor.const Dᵒᵖ).map k ≫ f) =
      k ≫ discreteYonedaTensorHomEquiv d L Z f := by
  ext Δ x
  rfl

/-- Scalar evaluation is natural in every original target presheaf map. -/
theorem discreteYonedaTensorHomEquiv_target (d : D) (K : SSet.{u})
    {Z Z' : SimplicialPresheaf.{u} D}
    (f : (discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) ⟶ Z) (g : Z ⟶ Z') :
    discreteYonedaTensorHomEquiv d K Z' (f ≫ g) =
      discreteYonedaTensorHomEquiv d K Z f ≫ g.app (op d) := by
  ext Δ x
  rfl

/-- Scalar evaluation is natural in the original representing-object arrow. -/
theorem discreteYonedaTensorHomEquiv_site {d d' : D} (s : d ⟶ d')
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (f : (discreteYoneda.obj d' ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) ⟶ Z) :
    discreteYonedaTensorHomEquiv d K Z
        ((discreteYoneda.map s) ▷ (CategoryTheory.Functor.const Dᵒᵖ).obj K ≫ f) =
      discreteYonedaTensorHomEquiv d' K Z f ≫ Z.map s.op := by
  ext Δ k
  have hy : (((discreteYoneda.map s).app (op d)).app Δ)
        ((discreteYonedaObjEquiv d (op d) Δ).symm (𝟙 d)) =
      (((discreteYoneda.obj d').map s.op).app Δ)
        ((discreteYonedaObjEquiv d' (op d') Δ).symm (𝟙 d')) := by
    apply (discreteYonedaObjEquiv d' (op d) Δ).injective
    rw [discreteYoneda_map_app, discreteYoneda_obj_map, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    simp
  have hn := congrArg (fun q => q.app Δ
      ((discreteYonedaObjEquiv d' (op d') Δ).symm (𝟙 d'), k)) (f.naturality s.op)
  change (f.app (op d)).app Δ
      ((((discreteYoneda.obj d').map s.op).app Δ)
        ((discreteYonedaObjEquiv d' (op d') Δ).symm (𝟙 d')), k) =
      (Z.map s.op).app Δ ((f.app (op d')).app Δ
        ((discreteYonedaObjEquiv d' (op d') Δ).symm (𝟙 d'), k)) at hn
  rw [← hy] at hn
  exact hn

include smallD localD

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar transposition is natural in the original source presheaf map. -/
theorem scalarTensorHomEquiv_source {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (f : ((scalarTensor.obj A).obj K) ⟶ Z) :
    scalarTensorHomEquiv A' K Z ((scalarTensor.map a).app K ≫ f) =
      scalarTensorHomEquiv A K Z f ≫ innerHomPre a Z := by
  apply innerHom_ext
  intro d
  simp only [scalarTensorHomEquiv_π, NatTrans.comp_app,
    scalarTensor_presheaf_map, Category.assoc, innerHomPre_π]
  rw [← Category.assoc, scalarTensorHomEquiv_π, curry_pre_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The true presheaf exponential has the original representable-weighted scalar end. -/
def exponential (A Z : SimplicialPresheaf.{u} D) : SimplicialPresheaf.{u} D where
  obj d := innerHom (discreteYoneda.obj d.unop ⊗ A) Z
  map g := innerHomPre ((discreteYoneda.map g.unop) ▷ A) Z
  map_id d := by
    have hy : (discreteYoneda.{u} (D := D)).map (𝟙 d.unop) =
        𝟙 ((discreteYoneda.{u} (D := D)).obj d.unop) :=
      (discreteYoneda.{u} (D := D)).map_id d.unop
    rw [unop_id, hy, id_whiskerRight, innerHomPre_id]
  map_comp g h := by
    simp only [unop_comp, Functor.map_comp, comp_whiskerRight, ← innerHomPre_comp]

/-- The defining value is the true representable-weighted mapping end. -/
theorem exponential_obj (A Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    (exponential A Z).obj d = innerHom (discreteYoneda.obj d.unop ⊗ A) Z := rfl

/-- Every original site arrow acts by the corresponding original representable precomposition. -/
theorem exponential_map (A Z : SimplicialPresheaf.{u} D) {d e : Dᵒᵖ} (g : d ⟶ e) :
    (exponential A Z).map g = innerHomPre ((discreteYoneda.map g.unop) ▷ A) Z := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original target natural maps act on the true exponential through end postcomposition. -/
def exponentialFunctor (A : SimplicialPresheaf.{u} D) :
    SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D where
  obj Z := exponential A Z
  map g :=
    { app d := innerHomPost (discreteYoneda.obj d.unop ⊗ A) g
      naturality d e η := by
        exact innerHom_exchange ((discreteYoneda.map η.unop) ▷ A) g }
  map_id Z := by
    ext d : 2
    exact innerHomPost_id _ _
  map_comp g h := by
    ext d : 2
    exact (innerHomPost_comp _ g h).symm

/-- Every original target component of the true exponential map is retained. -/
theorem exponentialFunctor_map_app (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') (d : Dᵒᵖ) :
    ((exponentialFunctor A).map g).app d =
      innerHomPost (discreteYoneda.obj d.unop ⊗ A) g := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original source natural map acts contravariantly on the true exponential. -/
def exponentialSourceMap {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A)
    (Z : SimplicialPresheaf.{u} D) : exponential A Z ⟶ exponential A' Z where
  app d := innerHomPre (discreteYoneda.obj d.unop ◁ a) Z
  naturality d e g := by
    dsimp only [exponential]
    rw [innerHomPre_comp, innerHomPre_comp, whisker_exchange]

/-- Original source and target actions on the true exponential commute. -/
theorem exponential_source_target {A A' Z Z' : SimplicialPresheaf.{u} D}
    (a : A' ⟶ A) (g : Z ⟶ Z') :
    exponentialSourceMap a Z ≫ (exponentialFunctor A').map g =
      (exponentialFunctor A).map g ≫ exponentialSourceMap a Z' := by
  ext d : 2
  exact innerHom_exchange (discreteYoneda.obj d.unop ◁ a) g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original representable scalar tensor is left adjoint to evaluation. -/
def discreteYonedaScalarAdjunction (d : D) :
    scalarTensor.obj (discreteYoneda.obj d) ⊣
      (CategoryTheory.evaluation Dᵒᵖ SSet.{u}).obj (op d) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := discreteYonedaTensorHomEquiv d
      homEquiv_naturality_left_symm := by
        intro K L Z k g
        apply (discreteYonedaTensorHomEquiv d K Z).injective
        change discreteYonedaTensorHomEquiv d K Z
          ((discreteYonedaTensorHomEquiv d K Z).symm (k ≫ g)) =
          discreteYonedaTensorHomEquiv d K Z
            ((scalarTensor.obj (discreteYoneda.obj d)).map k ≫
              (discreteYonedaTensorHomEquiv d L Z).symm g)
        rw [Equiv.apply_symm_apply]
        change k ≫ g = discreteYonedaTensorHomEquiv d K Z
          (discreteYoneda.obj d ◁ (CategoryTheory.Functor.const Dᵒᵖ).map k ≫
            (discreteYonedaTensorHomEquiv d L Z).symm g)
        rw [discreteYonedaTensorHomEquiv_scalar, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K Z Z' f g
        exact discreteYonedaTensorHomEquiv_target d K f g }

/-- The original tensor reassociation and braiding compare the two representable left adjoints. -/
def representableTensorLeftIso (d : D) (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj (discreteYoneda.obj d) ⋙ tensorLeft A ≅
      scalarTensor.obj (discreteYoneda.obj d ⊗ A) :=
  CategoryTheory.Functor.associator (CategoryTheory.Functor.const Dᵒᵖ)
    (tensorLeft (discreteYoneda.obj d)) (tensorLeft A) ≪≫
      ((CategoryTheory.Functor.whiskeringLeft SSet.{u}
        (SimplicialPresheaf.{u} D) (SimplicialPresheaf.{u} D)).obj
          (CategoryTheory.Functor.const Dᵒᵖ)).mapIso
        ((tensorLeftTensor A (discreteYoneda.obj d)).symm ≪≫
          (tensoringLeft (SimplicialPresheaf.{u} D)).mapIso (β_ A (discreteYoneda.obj d)))

/-- The representable scalar tensor followed by the original Cartesian left adjoint. -/
def underExpEvaluationAdjunction (d : D) (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj (discreteYoneda.obj d ⊗ A) ⊣
      underHomFunctor.obj (op A) ⋙
        (CategoryTheory.evaluation Dᵒᵖ SSet.{u}).obj (op d) :=
  ((discreteYonedaScalarAdjunction d).comp (underHomAdjunction A)).ofNatIsoLeft
    (representableTensorLeftIso d A)

/-- The genuine representable-weighted end is the actual native under-exponential value,
naturally in every original target presheaf and scalar map. -/
def underExpEvaluationIso (d : D) (A : SimplicialPresheaf.{u} D) :
    underHomFunctor.obj (op A) ⋙
        (CategoryTheory.evaluation Dᵒᵖ SSet.{u}).obj (op d) ≅
      innerHomFunctor.obj (op (discreteYoneda.obj d ⊗ A)) :=
  (underExpEvaluationAdjunction d A).rightAdjointUniq
    (scalarTensorHomAdjunction (discreteYoneda.obj d ⊗ A))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The native evaluation comparison preserves the original transposed map. -/
theorem underExpEvaluationIso_homEquiv_symm (d : D) (A : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ ((underHomFunctor.obj (op A)).obj Z).obj (op d)) :
    (scalarTensorHomEquiv (discreteYoneda.obj d ⊗ A) K Z).symm
        (h ≫ (underExpEvaluationIso d A).hom.app Z) =
      ((underExpEvaluationAdjunction d A).homEquiv K Z).symm h := by
  rw [← scalarTensorHomAdjunction_homEquiv]
  have ht := (scalarTensorHomAdjunction (discreteYoneda.obj d ⊗ A)).homEquiv_naturality_left_symm
    h ((underExpEvaluationIso d A).hom.app Z)
  have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (underExpEvaluationAdjunction d A)
    (scalarTensorHomAdjunction (discreteYoneda.obj d ⊗ A)) Z
  have he := ht.trans (congrArg
    (fun f => (scalarTensor.obj (discreteYoneda.obj d ⊗ A)).map h ≫ f) hc)
  exact he

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Source naturality for the inverse scalar transposition keeps the original tensor map. -/
theorem scalarTensorHomEquiv_source_symm {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A)
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) (h : K ⟶ innerHom A Z) :
    (scalarTensorHomEquiv A' K Z).symm (h ≫ innerHomPre a Z) =
      (scalarTensor.map a).app K ≫ (scalarTensorHomEquiv A K Z).symm h := by
  apply (scalarTensorHomEquiv A' K Z).injective
  rw [Equiv.apply_symm_apply, scalarTensorHomEquiv_source, Equiv.apply_symm_apply]

/-- The represented scalar end is original site evaluation, using both actual transpose inverses. -/
def discreteYonedaEndIso (d : D) (X : SimplicialPresheaf.{u} D) :
    innerHom (discreteYoneda.{u}.obj d) X ≅ X.obj (op d) where
  hom := discreteYonedaTensorHomEquiv d _ X
    ((scalarTensorHomEquiv (discreteYoneda.{u}.obj d) _ X).symm (𝟙 _))
  inv := scalarTensorHomEquiv (discreteYoneda.{u}.obj d) _ X
    ((discreteYonedaTensorHomEquiv d _ X).symm (𝟙 _))
  hom_inv_id := by
    let A := discreteYoneda.{u}.obj d
    let H := innerHom A X
    let V := X.obj (op d)
    let E (K : SSet.{u}) := scalarTensorHomEquiv A K X
    let Y (K : SSet.{u}) := discreteYonedaTensorHomEquiv d K X
    let F (K : SSet.{u}) := (E K).symm.trans (Y K)
    let h : H ⟶ V := Y H ((E H).symm (𝟙 H))
    let k : V ⟶ H := E V ((Y V).symm (𝟙 V))
    change h ≫ k = 𝟙 H
    apply (F H).injective
    have hn : F H (h ≫ k) = h ≫ F V k := by
      exact (congrArg (Y H)
        (scalarTensorHomEquiv_naturality_left_symm A h X k)).trans
          (discreteYonedaTensorHomEquiv_scalar d h X ((E V).symm k))
    have hk : F V k = 𝟙 V := by
      exact (congrArg (Y V)
        (Equiv.symm_apply_apply (E V) ((Y V).symm (𝟙 V)))).trans
          (Equiv.apply_symm_apply (Y V) (𝟙 V))
    calc
      F H (h ≫ k) = h ≫ F V k := hn
      _ = h := by rw [hk]; exact Category.comp_id _
      _ = F H (𝟙 H) := rfl
  inv_hom_id := by
    let A := discreteYoneda.{u}.obj d
    let H := innerHom A X
    let V := X.obj (op d)
    let E (K : SSet.{u}) := scalarTensorHomEquiv A K X
    let Y (K : SSet.{u}) := discreteYonedaTensorHomEquiv d K X
    let F (K : SSet.{u}) := (E K).symm.trans (Y K)
    let h : H ⟶ V := Y H ((E H).symm (𝟙 H))
    let k : V ⟶ H := E V ((Y V).symm (𝟙 V))
    change k ≫ h = 𝟙 V
    have hn : F V (k ≫ 𝟙 H) = k ≫ h := by
      exact (congrArg (Y V)
        (scalarTensorHomEquiv_naturality_left_symm A k X (𝟙 H))).trans
          (discreteYonedaTensorHomEquiv_scalar d k X ((E H).symm (𝟙 H)))
    have hk : F V k = 𝟙 V := by
      exact (congrArg (Y V)
        (Equiv.symm_apply_apply (E V) ((Y V).symm (𝟙 V)))).trans
          (Equiv.apply_symm_apply (Y V) (𝟙 V))
    calc
      k ≫ h = F V (k ≫ 𝟙 H) := hn.symm
      _ = F V k := congrArg (F V) (Category.comp_id k)
      _ = 𝟙 V := hk

private def representedHom (d : D) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) :
    (K ⟶ innerHom (discreteYoneda.{u}.obj d) X) ≃ (K ⟶ X.obj (op d)) :=
  (scalarTensorHomEquiv (discreteYoneda.{u}.obj d) K X).symm.trans
    (discreteYonedaTensorHomEquiv d K X)

private theorem representedHom_scalar (d : D)
    {K L : SSet.{u}} (k : K ⟶ L) (X : SimplicialPresheaf.{u} D)
    (f : L ⟶ innerHom (discreteYoneda.{u}.obj d) X) :
    representedHom d K X (k ≫ f) = k ≫ representedHom d L X f := by
  change discreteYonedaTensorHomEquiv d K X
    ((scalarTensorHomEquiv (discreteYoneda.{u}.obj d) K X).symm (k ≫ f)) = _
  exact (congrArg (discreteYonedaTensorHomEquiv d K X)
    (scalarTensorHomEquiv_naturality_left_symm (discreteYoneda.{u}.obj d) k X f)).trans
      (discreteYonedaTensorHomEquiv_scalar d k X
        ((scalarTensorHomEquiv (discreteYoneda.{u}.obj d) L X).symm f))

private theorem representedHom_eq (d : D) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) (f : K ⟶ innerHom (discreteYoneda.{u}.obj d) X) :
    representedHom d K X f = f ≫ (discreteYonedaEndIso d X).hom := by
  exact (congrArg (representedHom d K X) (Category.comp_id f)).symm.trans
    (representedHom_scalar d f X (𝟙 _))

private theorem representedHom_site {d d' : D}
    (s : d ⟶ d') (K : SSet.{u}) (X : SimplicialPresheaf.{u} D)
    (f : K ⟶ innerHom (discreteYoneda.{u}.obj d') X) :
    representedHom d K X (f ≫ innerHomPre (discreteYoneda.{u}.map s) X) =
      representedHom d' K X f ≫ X.map s.op := by
  exact (congrArg (discreteYonedaTensorHomEquiv d K X)
    (scalarTensorHomEquiv_source_symm (discreteYoneda.{u}.map s) K X f)).trans
      (discreteYonedaTensorHomEquiv_site s K X
        ((scalarTensorHomEquiv (discreteYoneda.{u}.obj d') K X).symm f))

/-- Representing-site precomposition is the original contravariant site restriction. -/
theorem discreteYonedaEndIso_site {d d' : D}
    (s : d ⟶ d') (X : SimplicialPresheaf.{u} D) :
    innerHomPre (discreteYoneda.{u}.map s) X ≫ (discreteYonedaEndIso d X).hom =
      (discreteYonedaEndIso d' X).hom ≫ X.map s.op := by
  let K := innerHom (discreteYoneda.{u}.obj d') X
  calc
    innerHomPre (discreteYoneda.{u}.map s) X ≫ (discreteYonedaEndIso d X).hom =
        representedHom d K X (innerHomPre (discreteYoneda.{u}.map s) X) :=
      (representedHom_eq d K X _).symm
    _ = representedHom d K X (𝟙 K ≫ innerHomPre (discreteYoneda.{u}.map s) X) := by
      rw [Category.id_comp]
    _ = representedHom d' K X (𝟙 K) ≫ X.map s.op :=
      representedHom_site s K X (𝟙 K)
    _ = _ := rfl

/-- Target postcomposition is the original evaluation component. -/
theorem discreteYonedaEndIso_target (d : D)
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    innerHomPost (discreteYoneda.{u}.obj d) f ≫ (discreteYonedaEndIso d Y).hom =
      (discreteYonedaEndIso d X).hom ≫ f.app (op d) := by
  let K := innerHom (discreteYoneda.{u}.obj d) X
  let T₀ := scalarTensorHomEquiv (discreteYoneda.{u}.obj d) K X
  let T₁ := scalarTensorHomEquiv (discreteYoneda.{u}.obj d) K Y
  have ht : T₁.symm (innerHomPost (discreteYoneda.{u}.obj d) f) = T₀.symm (𝟙 K) ≫ f := by
    apply T₁.injective
    rw [scalarTensorHomEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    change innerHomPost (discreteYoneda.{u}.obj d) f =
      𝟙 K ≫ innerHomPost (discreteYoneda.{u}.obj d) f
    exact (Category.id_comp _).symm
  calc
    innerHomPost (discreteYoneda.{u}.obj d) f ≫ (discreteYonedaEndIso d Y).hom =
        representedHom d K Y (innerHomPost (discreteYoneda.{u}.obj d) f) :=
      (representedHom_eq d K Y _).symm
    _ = discreteYonedaTensorHomEquiv d K Y (T₀.symm (𝟙 K) ≫ f) := by
      change discreteYonedaTensorHomEquiv d K Y
        (T₁.symm (innerHomPost (discreteYoneda.{u}.obj d) f)) = _
      rw [ht]
      rfl
    _ = discreteYonedaTensorHomEquiv d K X (T₀.symm (𝟙 K)) ≫ f.app (op d) :=
      discreteYonedaTensorHomEquiv_target d K _ f
    _ = _ := rfl

omit smallD in
/-- Original site variance for inverse representable scalar evaluation. -/
theorem discreteYonedaTensorHomEquiv_site_symm {d d' : D} (s : d ⟶ d')
    (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) (h : K ⟶ Z.obj (op d')) :
    (discreteYonedaTensorHomEquiv d K Z).symm (h ≫ Z.map s.op) =
      (discreteYoneda.map s) ▷ (CategoryTheory.Functor.const Dᵒᵖ).obj K ≫
        (discreteYonedaTensorHomEquiv d' K Z).symm h := by
  apply (discreteYonedaTensorHomEquiv d K Z).injective
  rw [Equiv.apply_symm_apply, discreteYonedaTensorHomEquiv_site, Equiv.apply_symm_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem underExpEvaluationAdjunction_homEquiv_symm (d : D)
    (A : SimplicialPresheaf.{u} D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ ((underHomFunctor.obj (op A)).obj Z).obj (op d)) :
    ((underExpEvaluationAdjunction d A).homEquiv K Z).symm h =
      (representableTensorLeftIso d A).inv.app K ≫
        ((underHomAdjunction A).homEquiv
          (discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) Z).symm
          ((discreteYonedaTensorHomEquiv d K ((underHomFunctor.obj (op A)).obj Z)).symm h) := by
  simp only [underExpEvaluationAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  congr 2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit smallD in
/-- The actual inverse representable tensor comparison is the native braid and associator. -/
private theorem representableTensorLeftIso_inv_app (d : D) (A : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) :
    (representableTensorLeftIso d A).inv.app K =
      (β_ A (discreteYoneda.obj d)).inv ▷ (CategoryTheory.Functor.const Dᵒᵖ).obj K ≫
        (α_ A (discreteYoneda.obj d) ((CategoryTheory.Functor.const Dᵒᵖ).obj K)).hom := by
  change ((β_ A (discreteYoneda.obj d)).inv ▷ (CategoryTheory.Functor.const Dᵒᵖ).obj K ≫
    (α_ A (discreteYoneda.obj d) ((CategoryTheory.Functor.const Dᵒᵖ).obj K)).hom) ≫ 𝟙 _ = _
  simp only [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit smallD in
/-- The actual representable reassociation retains the original site map. -/
private theorem representableTensorLeftIso_inv_site {d e : Dᵒᵖ} (g : d ⟶ e)
    (A : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    (representableTensorLeftIso e.unop A).inv.app K ≫
        A ◁ ((discreteYoneda.map g.unop) ▷ (CategoryTheory.Functor.const Dᵒᵖ).obj K) =
      (scalarTensor.map ((discreteYoneda.map g.unop) ▷ A)).app K ≫
        (representableTensorLeftIso d.unop A).inv.app K := by
  rw [representableTensorLeftIso_inv_app, representableTensorLeftIso_inv_app]
  simp only [Category.assoc]
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc,
    ← BraidedCategory.braiding_inv_naturality_left, comp_whiskerRight_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem underExpEvaluationAdjunction_site {d e : Dᵒᵖ} (g : d ⟶ e)
    (A : SimplicialPresheaf.{u} D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D)
    (h : K ⟶ ((underHomFunctor.obj (op A)).obj Z).obj d) :
    ((underExpEvaluationAdjunction e.unop A).homEquiv K Z).symm
        (h ≫ ((underHomFunctor.obj (op A)).obj Z).map g) =
      (scalarTensor.map ((discreteYoneda.map g.unop) ▷ A)).app K ≫
        ((underExpEvaluationAdjunction d.unop A).homEquiv K Z).symm h := by
  rw [underExpEvaluationAdjunction_homEquiv_symm,
    underExpEvaluationAdjunction_homEquiv_symm]
  have hs := discreteYonedaTensorHomEquiv_site_symm g.unop K
    ((underHomFunctor.obj (op A)).obj Z) h
  simp only [Quiver.Hom.op_unop] at hs
  rw [hs]
  rw [Adjunction.homEquiv_naturality_left_symm]
  have hx := representableTensorLeftIso_inv_site g A K
  change (representableTensorLeftIso e.unop A).inv.app K ≫
      (tensorLeft A).map ((discreteYoneda.map g.unop) ▷ (CategoryTheory.Functor.const Dᵒᵖ).obj K) =
      (scalarTensor.map ((discreteYoneda.map g.unop) ▷ A)).app K ≫
        (representableTensorLeftIso d.unop A).inv.app K at hx
  rw [← Category.assoc, hx, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The native under-end comparison commutes with every original presheaf restriction. -/
theorem underExpEvaluationIso_site {d e : Dᵒᵖ} (g : d ⟶ e)
    (A Z : SimplicialPresheaf.{u} D) :
    ((underHomFunctor.obj (op A)).obj Z).map g ≫ (underExpEvaluationIso e.unop A).hom.app Z =
      (underExpEvaluationIso d.unop A).hom.app Z ≫ (exponential A Z).map g := by
  let K := ((underHomFunctor.obj (op A)).obj Z).obj d
  apply (scalarTensorHomEquiv (discreteYoneda.obj e.unop ⊗ A) K Z).symm.injective
  change (scalarTensorHomEquiv (discreteYoneda.obj e.unop ⊗ A) K Z).symm
      (((underHomFunctor.obj (op A)).obj Z).map g ≫
        (underExpEvaluationIso e.unop A).hom.app Z) =
    (scalarTensorHomEquiv (discreteYoneda.obj e.unop ⊗ A) K Z).symm
      ((underExpEvaluationIso d.unop A).hom.app Z ≫
        innerHomPre ((discreteYoneda.map g.unop) ▷ A) Z)
  rw [underExpEvaluationIso_homEquiv_symm, scalarTensorHomEquiv_source_symm]
  have hd := underExpEvaluationIso_homEquiv_symm d.unop A K Z (𝟙 K)
  simp only [Category.id_comp] at hd
  rw [hd]
  simpa only [Category.id_comp] using underExpEvaluationAdjunction_site g A K Z (𝟙 K)

/-- The genuine exponential is the whole original native under-end right adjoint. -/
def underExponentialIso (A : SimplicialPresheaf.{u} D) :
    underHomFunctor.obj (op A) ≅ exponentialFunctor A :=
  NatIso.ofComponents (fun Z => NatIso.ofComponents
    (fun d => (underExpEvaluationIso d.unop A).app Z)
    (fun {d e} g => underExpEvaluationIso_site (d := d) (e := e) g A Z)) (by
      intro Z Z' g
      ext d : 2
      exact (underExpEvaluationIso d.unop A).hom.naturality g)

/-- The Cartesian adjunction uses the true representable-weighted exponential on the
original presheaf category. -/
def exponentialAdjunction (A : SimplicialPresheaf.{u} D) : tensorLeft A ⊣ exponentialFunctor A :=
  (underHomAdjunction A).ofNatIsoRight (underExponentialIso A)

/-- Its transposition preserves the original native Cartesian map and exponential comparison. -/
theorem exponentialAdjunction_homEquiv (A B Z : SimplicialPresheaf.{u} D)
    (f : A ⊗ B ⟶ Z) :
    (exponentialAdjunction A).homEquiv B Z f =
      (underHomAdjunction A).homEquiv B Z f ≫ (underExponentialIso A).hom.app Z :=
  Adjunction.homEquiv_ofNatIsoRight_apply _ _ _

/-- Actual end simplices correspond to original natural maps from the chosen scalar simplex
tensor. -/
def innerHomSimplexEquiv (A Z : SimplicialPresheaf.{u} D) (Δ : SimplexCategoryᵒᵖ) :
    (innerHom A Z).obj Δ ≃
      (((scalarTensor.obj A).obj (SSet.stdSimplex.obj Δ.unop)) ⟶ Z) :=
  SSet.yonedaEquiv.symm.trans
    (scalarTensorHomEquiv A (SSet.stdSimplex.obj Δ.unop) Z).symm

/-- Every original simplex operator is original scalar-simplex precomposition. -/
theorem innerHomSimplexEquiv_operator (A Z : SimplicialPresheaf.{u} D)
    {Δ Δ' : SimplexCategoryᵒᵖ} (δ : Δ ⟶ Δ') (x : (innerHom A Z).obj Δ) :
    innerHomSimplexEquiv A Z Δ' ((innerHom A Z).map δ x) =
      (scalarTensor.obj A).map (SSet.stdSimplex.map δ.unop) ≫ innerHomSimplexEquiv A Z Δ x := by
  change (scalarTensorHomEquiv A (SSet.stdSimplex.obj Δ'.unop) Z).symm
      (SSet.yonedaEquiv.symm ((innerHom A Z).map δ x)) =
    (scalarTensor.obj A).map (SSet.stdSimplex.map δ.unop) ≫
      (scalarTensorHomEquiv A (SSet.stdSimplex.obj Δ.unop) Z).symm (SSet.yonedaEquiv.symm x)
  have hn := SSet.yonedaEquiv_symm_naturality_left (X := innerHom A Z) δ.unop x
  simp only [Quiver.Hom.op_unop] at hn
  rw [← hn, scalarTensorHomEquiv_naturality_left_symm]

/-- End simplex transposition retains each original source natural map. -/
theorem innerHomSimplexEquiv_source {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A)
    (Z : SimplicialPresheaf.{u} D) (Δ : SimplexCategoryᵒᵖ) (x : (innerHom A Z).obj Δ) :
    innerHomSimplexEquiv A' Z Δ ((innerHomPre a Z).app Δ x) =
      (scalarTensor.map a).app (SSet.stdSimplex.obj Δ.unop) ≫ innerHomSimplexEquiv A Z Δ x := by
  change (scalarTensorHomEquiv A' (SSet.stdSimplex.obj Δ.unop) Z).symm
      (SSet.yonedaEquiv.symm ((innerHomPre a Z).app Δ x)) = _
  rw [← SSet.yonedaEquiv_symm_comp, scalarTensorHomEquiv_source_symm]
  rfl

/-- End simplex transposition retains each original target natural map. -/
theorem innerHomSimplexEquiv_target (A : SimplicialPresheaf.{u} D)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z')
    (Δ : SimplexCategoryᵒᵖ) (x : (innerHom A Z).obj Δ) :
    innerHomSimplexEquiv A Z' Δ ((innerHomPost A g).app Δ x) =
      innerHomSimplexEquiv A Z Δ x ≫ g := by
  change (scalarTensorHomEquiv A (SSet.stdSimplex.obj Δ.unop) Z').symm
      (SSet.yonedaEquiv.symm ((innerHomPost A g).app Δ x)) =
    (scalarTensorHomEquiv A (SSet.stdSimplex.obj Δ.unop) Z).symm (SSet.yonedaEquiv.symm x) ≫ g
  rw [← SSet.yonedaEquiv_symm_comp, ← scalarTensorHomAdjunction_homEquiv]
  exact (scalarTensorHomAdjunction A).homEquiv_naturality_right_symm (SSet.yonedaEquiv.symm x) g

/-- The actual scalar enrichment gives the native lower-Hom category with all original objects. -/
def enrichedCarrierEquivalence : SimplicialPresheaf.{u} D ≌
    ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D) :=
  (ForgetEnrichment.equiv (V := SSet.{u}) (D := SimplicialPresheaf.{u} D)).symm

/-- Native simplicial-category data is on the actual lower-Hom carrier in universe u. -/
@[instance_reducible]
def enrichedCarrierSimplicialCategory :
    SimplicialCategory (ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D)) :=
  inferInstanceAs (EnrichedOrdinaryCategory SSet.{u}
    (ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D)))

/-- The original natural transformation is transported by its actual enriched-Hom equivalence. -/
theorem enrichedCarrierEquivalence_functor_map {A Z : SimplicialPresheaf.{u} D} (f : A ⟶ Z) :
    (enrichedCarrierEquivalence (D := D)).functor.map f =
      ForgetEnrichment.homOf SSet.{u} (eHomEquiv SSet.{u} f) := rfl

/-- The native Hom-shrink and enrichment carriers are compared by their actual equivalences. -/
def homShrinkEnrichmentEquivalence :
    letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := locallySmall
    ShrinkHoms (SimplicialPresheaf.{u} D) ≌
      ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D) := by
  letI : LocallySmall.{u} (SimplicialPresheaf.{u} D) := locallySmall
  exact (ShrinkHoms.equivalence.{u} (SimplicialPresheaf.{u} D)).symm.trans
      enrichedCarrierEquivalence

/-- The original whole Arrow and both endpoint maps are retained by enrichment normalization. -/
theorem enrichedCarrier_arrow_unit (f : Arrow (SimplicialPresheaf.{u} D)) :
    let E := enrichedCarrierEquivalence (D := D)
    let F := CategoryTheory.Functor.mapArrowEquivalence E
    (F.unitIso.app f).hom.left = (E.unitIso.app f.left).hom ∧
      (F.unitIso.app f).hom.right = (E.unitIso.app f.right).hom ∧
      (F.unitIso.app f).hom.left ≫ E.inverse.map (E.functor.map f.hom) =
        f.hom ≫ (F.unitIso.app f).hom.right := by
  dsimp only
  exact ⟨rfl, rfl,
      ((CategoryTheory.Functor.mapArrowEquivalence
        enrichedCarrierEquivalence).unitIso.app f).hom.w⟩

/-- The lower-Hom whole Arrow and both endpoint maps are retained by the actual counit. -/
theorem enrichedCarrier_arrow_counit
    (f : Arrow (ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D))) :
    let E := enrichedCarrierEquivalence (D := D)
    let F := CategoryTheory.Functor.mapArrowEquivalence E
    (F.counitIso.app f).hom.left = (E.counitIso.app f.left).hom ∧
      (F.counitIso.app f).hom.right = (E.counitIso.app f.right).hom ∧
      (F.counitIso.app f).hom.left ≫ f.hom =
        E.functor.map (E.inverse.map f.hom) ≫ (F.counitIso.app f).hom.right := by
  dsimp only
  exact ⟨rfl, rfl,
      ((CategoryTheory.Functor.mapArrowEquivalence
        enrichedCarrierEquivalence).counitIso.app f).hom.w⟩

section SiteComparison

variable {E : Type w'} [Category.{v'} E] [Small.{u} E] [LocallySmall.{u} E]

/-- Actual inverse-opposite site precomposition preserves the original scalar tensor functor. -/
def scalarTensorTransportIso (e : D ≌ E) (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj A ⋙ (transport e).functor ≅
      scalarTensor.obj ((transport e).functor.obj A) :=
  NatIso.ofComponents (fun K => Iso.refl _) (by
    intro K L k
    rfl)

/-- Transport the actual scalar adjunction along the original carrier equivalence. -/
def transportedScalarAdjunction (e : D ≌ E) (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj ((transport e).functor.obj A) ⊣
      (transport e).inverse ⋙ innerHomFunctor.obj (op A) :=
  ((scalarTensorHomAdjunction A).comp (transport e).toAdjunction).ofNatIsoLeft
    (scalarTensorTransportIso e A)

/-- Native adjoint uniqueness compares the actual two fixed-u scalar mapping functors. -/
def innerHomTransportRightIso (e : D ≌ E) (A : SimplicialPresheaf.{u} D) :
    (transport e).inverse ⋙ innerHomFunctor.obj (op A) ≅
      innerHomFunctor.obj (op ((transport e).functor.obj A)) :=
  (transportedScalarAdjunction e A).rightAdjointUniq
    (scalarTensorHomAdjunction ((transport e).functor.obj A))

/-- The actual original mapping end is transported using the carrier unit and native scalar
adjunctions. -/
def innerHomTransportIso (e : D ≌ E) (A Z : SimplicialPresheaf.{u} D) :
    innerHom A Z ≅ innerHom ((transport e).functor.obj A) ((transport e).functor.obj Z) :=
  (innerHomFunctor.obj (op A)).mapIso ((transport e).unitIso.app Z) ≪≫
    (innerHomTransportRightIso e A).app ((transport e).functor.obj Z)

omit smallD localD [Small.{u} E] [LocallySmall.{u} E] in
/-- Both original Arrow endpoints and the whole original unit square survive the same site
change. -/
theorem innerHomTransport_arrow_unit (e : D ≌ E) (f : Arrow (SimplicialPresheaf.{u} D)) :
    let Φ := transport e
    let Ψ := CategoryTheory.Functor.mapArrowEquivalence Φ
    (Ψ.unitIso.app f).hom.left = (Φ.unitIso.app f.left).hom ∧
      (Ψ.unitIso.app f).hom.right = (Φ.unitIso.app f.right).hom ∧
      (Ψ.unitIso.app f).hom.left ≫ Φ.inverse.map (Φ.functor.map f.hom) =
        f.hom ≫ (Ψ.unitIso.app f).hom.right :=
  transport_arrow_unit e f

omit smallD localD [Small.{u} E] [LocallySmall.{u} E] in
/-- Both target Arrow endpoints and the whole original counit square survive the same site
change. -/
theorem innerHomTransport_arrow_counit (e : D ≌ E) (f : Arrow (SimplicialPresheaf.{u} E)) :
    let Φ := transport e
    let Ψ := CategoryTheory.Functor.mapArrowEquivalence Φ
    (Ψ.counitIso.app f).hom.left = (Φ.counitIso.app f.left).hom ∧
      (Ψ.counitIso.app f).hom.right = (Φ.counitIso.app f.right).hom ∧
      (Ψ.counitIso.app f).hom.left ≫ f.hom =
        Φ.functor.map (Φ.inverse.map f.hom) ≫ (Ψ.counitIso.app f).hom.right :=
  transport_arrow_counit e f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem innerHomTransportRightIso_homEquiv (e : D ≌ E) (A : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (Y : SimplicialPresheaf.{u} E)
    (f : ((scalarTensor.obj ((transport e).functor.obj A)).obj K) ⟶ Y) :
    (transportedScalarAdjunction e A).homEquiv K Y f ≫ (innerHomTransportRightIso e A).hom.app Y =
      scalarTensorHomEquiv ((transport e).functor.obj A) K Y f := by
  rw [← scalarTensorHomAdjunction_homEquiv]
  change (transportedScalarAdjunction e A).unit.app K ≫
      ((transport e).inverse ⋙ innerHomFunctor.obj (op A)).map f ≫
        (innerHomTransportRightIso e A).hom.app Y =
    (scalarTensorHomAdjunction ((transport e).functor.obj A)).unit.app K ≫
      (innerHomFunctor.obj (op ((transport e).functor.obj A))).map f
  rw [(innerHomTransportRightIso e A).hom.naturality, ← Category.assoc]
  rw [innerHomTransportRightIso, Adjunction.unit_rightAdjointUniq_hom_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [Small.{u} E] [LocallySmall.{u} E] in
private theorem transportedScalarAdjunction_homEquiv_map (e : D ≌ E)
    (A Z : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (f : ((scalarTensor.obj A).obj K) ⟶ Z) :
    (transportedScalarAdjunction e A).homEquiv K ((transport e).functor.obj Z)
        ((transport e).functor.map f) =
      scalarTensorHomEquiv A K ((transport e).inverse.obj ((transport e).functor.obj Z))
        (f ≫ ((transport e).unitIso.app Z).hom) := by
  simp only [transportedScalarAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv, scalarTensorHomAdjunction_homEquiv]
  change scalarTensorHomEquiv A K ((transport e).inverse.obj ((transport e).functor.obj Z))
      (((transport e).unitIso.app ((scalarTensor.obj A).obj K)).hom ≫
        (transport e).inverse.map ((transport e).functor.map f)) = _
  exact congrArg
    (scalarTensorHomEquiv A K ((transport e).inverse.obj ((transport e).functor.obj Z)))
    ((transport e).unitIso.hom.naturality f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Site normalization retains every original scalar-transposed natural map. -/
theorem innerHomTransportIso_scalar_map (e : D ≌ E) (A Z : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (f : ((scalarTensor.obj A).obj K) ⟶ Z) :
    scalarTensorHomEquiv A K Z f ≫ (innerHomTransportIso e A Z).hom =
      scalarTensorHomEquiv ((transport e).functor.obj A) K ((transport e).functor.obj Z)
        ((transport e).functor.map f) := by
  rw [innerHomTransportIso, Iso.trans_hom]
  change scalarTensorHomEquiv A K Z f ≫
      (innerHomFunctor.obj (op A)).map ((transport e).unitIso.app Z).hom ≫
        (innerHomTransportRightIso e A).hom.app ((transport e).functor.obj Z) = _
  rw [← Category.assoc, ← scalarTensorHomEquiv_naturality_right]
  have ht := transportedScalarAdjunction_homEquiv_map e A Z K f
  exact (congrArg
    (fun q => q ≫ (innerHomTransportRightIso e A).hom.app ((transport e).functor.obj Z))
        ht.symm).trans
      (innerHomTransportRightIso_homEquiv e A K ((transport e).functor.obj Z)
        ((transport e).functor.map f))

end SiteComparison

/-- The actual native small-model site retains the fixed-u original mapping end. -/
def innerHomSmallModelIso (A Z : SimplicialPresheaf.{u} D) :
    innerHom A Z ≅ innerHom ((smallModelTransport (D := D)).functor.obj A)
      ((smallModelTransport (D := D)).functor.obj Z) :=
  innerHomTransportIso (equivSmallModel.{u} D) A Z

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar unit projects to the original coefficient coevaluation. -/
theorem scalarTensorHomAdjunction_unit_π (A : SimplicialPresheaf.{u} D)
    (K : SSet.{u}) (d : Dᵒᵖ) :
    (scalarTensorHomAdjunction A).unit.app K ≫ innerHomπ A ((scalarTensor.obj A).obj K) d =
      curry (𝟙 (((scalarTensor.obj A).obj K).obj d)) := by
  have hu : scalarTensorHomEquiv A K ((scalarTensor.obj A).obj K) (𝟙 _) =
      (scalarTensorHomAdjunction A).unit.app K := by
    rw [← scalarTensorHomAdjunction_homEquiv]
    exact (scalarTensorHomAdjunction A).homEquiv_id K
  have hp := scalarTensorHomEquiv_π A K ((scalarTensor.obj A).obj K) (𝟙 _) d
  simpa only [NatTrans.id_app] using
    (congrArg (fun q => q ≫ innerHomπ A ((scalarTensor.obj A).obj K) d) hu).symm.trans hp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar counit is the original evaluation at the end projection. -/
theorem scalarTensorHomAdjunction_counit_app (A Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarTensorHomAdjunction A).counit.app Z).app d = uncurry (innerHomπ A Z d) := by
  let K := (innerHomFunctor.obj (op A)).obj Z
  have hc : (scalarTensorHomEquiv A K Z).symm (𝟙 K) =
      (scalarTensorHomAdjunction A).counit.app Z := by
    rw [← scalarTensorHomAdjunction_homEquiv]
    exact (scalarTensorHomAdjunction A).homEquiv_symm_id Z
  have he := (scalarTensorHomEquiv A K Z).apply_symm_apply (𝟙 K)
  rw [hc] at he
  have hp := scalarTensorHomEquiv_π A K Z ((scalarTensorHomAdjunction A).counit.app Z) d
  rw [he, Category.id_comp] at hp
  have h := congrArg uncurry hp
  simpa only [uncurry_curry] using h.symm

/-- The whole original scalar left triangle retains its exact two maps. -/
theorem scalarTensorHomAdjunction_leftTriangle (A : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    (scalarTensor.obj A).map ((scalarTensorHomAdjunction A).unit.app K) ≫
      (scalarTensorHomAdjunction A).counit.app ((scalarTensor.obj A).obj K) = 𝟙 _ :=
  (scalarTensorHomAdjunction A).left_triangle_components K

/-- The whole original scalar right triangle retains its exact two maps. -/
theorem scalarTensorHomAdjunction_rightTriangle (A Z : SimplicialPresheaf.{u} D) :
    (scalarTensorHomAdjunction A).unit.app ((innerHomFunctor.obj (op A)).obj Z) ≫
      (innerHomFunctor.obj (op A)).map ((scalarTensorHomAdjunction A).counit.app Z) = 𝟙 _ :=
  (scalarTensorHomAdjunction A).right_triangle_components Z

/-- The genuine Cartesian unit uses the original under-end unit and the proved comparison. -/
theorem exponentialAdjunction_unit (A B : SimplicialPresheaf.{u} D) :
    (exponentialAdjunction A).unit.app B =
      (underHomAdjunction A).unit.app B ≫ (underExponentialIso A).hom.app (A ⊗ B) := by
  rfl

/-- The genuine Cartesian counit uses the actual inverse comparison and original under-end
counit. -/
theorem exponentialAdjunction_counit (A Z : SimplicialPresheaf.{u} D) :
    (exponentialAdjunction A).counit.app Z =
      (tensorLeft A).map ((underExponentialIso A).inv.app Z) ≫
          (underHomAdjunction A).counit.app Z := by
  rfl

/-- The whole original Cartesian left triangle retains the genuine exponential. -/
theorem exponentialAdjunction_leftTriangle (A B : SimplicialPresheaf.{u} D) :
    (tensorLeft A).map ((exponentialAdjunction A).unit.app B) ≫
      (exponentialAdjunction A).counit.app (A ⊗ B) = 𝟙 _ :=
  (exponentialAdjunction A).left_triangle_components B

/-- The whole original Cartesian right triangle retains the genuine exponential. -/
theorem exponentialAdjunction_rightTriangle (A Z : SimplicialPresheaf.{u} D) :
    (exponentialAdjunction A).unit.app ((exponentialFunctor A).obj Z) ≫
      (exponentialFunctor A).map ((exponentialAdjunction A).counit.app Z) = 𝟙 _ :=
  (exponentialAdjunction A).right_triangle_components Z

omit smallD localD in
/-- The pointwise cotensor unit uses the actual coefficient unit and braiding on original values. -/
theorem scalarTensorCotensorAdjunction_unit_app (K : SSet.{u})
    (A : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarTensorCotensorAdjunction (D := D) K).unit.app A).app d =
      (ihom.adjunction K).unit.app (A.obj d) ≫ (ihom K).map (β_ K (A.obj d)).hom := by
  simp [scalarTensorCotensorAdjunction, Adjunction.whiskerRight, Adjunction.ofNatIsoLeft]
  rfl

omit smallD localD in
/-- The pointwise cotensor counit uses the actual coefficient counit and inverse braiding. -/
theorem scalarTensorCotensorAdjunction_counit_app (K : SSet.{u})
    (Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarTensorCotensorAdjunction (D := D) K).counit.app Z).app d =
      (β_ K ((ihom K).obj (Z.obj d))).inv ≫ (ihom.adjunction K).counit.app (Z.obj d) := by
  simp [scalarTensorCotensorAdjunction, Adjunction.whiskerRight, Adjunction.ofNatIsoLeft]
  rfl

end SimplicialPresheaf
