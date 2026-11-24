/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import MathlibExt.AlgebraicTopology.SimplicialCategory.PointwiseHom
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Pointwise inner enrichment of the designated simplicial-space category

The enrichment is the end of the inner internal-Hom objects in each outer
degree. It is installed only on `SimplicialSpace`, preserving the raw outer
simplicial enrichment. The inner scalar acts by `X_(m,n) × K_n`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SimplicialSpace

/-- The native pointwise enriched ordinary category on raw simplicial objects.
This is the actual enriched-end data transported to the designated carrier. -/
abbrev rawInnerEnrichment :
    EnrichedOrdinaryCategory SSet.{u} (SimplicialObject SSet.{u}) := by
  letI : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  letI : ∀ X Y : SimplicialObject SSet.{u},
      Enriched.FunctorCategory.HasEnrichedHom SSet.{u} X Y := inferInstance
  exact Enriched.FunctorCategory.enrichedOrdinaryCategory
    SSet.{u} SSet.{u} SimplexCategoryᵒᵖ

/-- The native pointwise inner enrichment on the designated carrier. -/
@[instance_reducible]
def innerEnrichedOrdinaryCategory : EnrichedOrdinaryCategory SSet.{u} SimplicialSpace.{u} := by
  let E := rawInnerEnrichment.{u}
  exact
    { Hom := fun X Y => E.Hom X.diagram Y.diagram
      id := fun X => E.id X.diagram
      comp := fun X Y Z => E.comp X.diagram Y.diagram Z.diagram
      id_comp := fun X Y => E.id_comp X.diagram Y.diagram
      comp_id := fun X Y => E.comp_id X.diagram Y.diagram
      assoc := fun W X Y Z => E.assoc W.diagram X.diagram Y.diagram Z.diagram
      homEquiv := fun {X Y} => (SimplicialSpace.homEquiv).trans E.homEquiv
      homEquiv_id := fun X => E.homEquiv_id X.diagram
      homEquiv_comp := fun f g => E.homEquiv_comp f.hom g.hom }

namespace Inner

/-- Select the native inner enrichment on the designated simplicial-space carrier. -/
scoped instance : EnrichedOrdinaryCategory SSet.{u} SimplicialSpace.{u} :=
  innerEnrichedOrdinaryCategory

end Inner

section
open scoped SimplicialSpace.Inner

/-- The chosen mapping object is exactly the existing pointwise enriched end. -/
lemma innerHom_eq_pointwise (X Y : SimplicialSpace.{u}) :
    (X ⟶[SSet.{u}] Y) =
      (SSet.simplicialSpacePointwiseHom.obj (op X.diagram)).obj Y.diagram := rfl

/-- Ordinary maps are precisely the inner vertices of the chosen mapping object. -/
def innerHomEquiv (X Y : SimplicialSpace.{u}) :
    (X ⟶ Y) ≃ (X ⟶[SSet.{u}] Y) _⦋0⦌ :=
  SimplicialCategory.homEquiv' X Y

/-- The outer-degree projection from the inner mapping end. -/
abbrev innerHomπ (X Y : SimplicialSpace.{u}) (m : SimplexCategoryᵒᵖ) :
    (X ⟶[SSet.{u}] Y) ⟶ (ihom (X.diagram.obj m)).obj (Y.diagram.obj m) :=
  SSet.simplicialSpacePointwiseHomπ X.diagram Y.diagram m

/-- The projections satisfy the complete end naturality equation. -/
lemma innerHomπ_naturality (X Y : SimplicialSpace.{u}) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) :
    innerHomπ X Y m ≫ (ihom (X.diagram.obj m)).map (Y.diagram.map f) =
      innerHomπ X Y n ≫ (pre (X.diagram.map f)).app (Y.diagram.obj n) :=
  SSet.simplicialSpacePointwiseHomπ_outer X.diagram Y.diagram f

/-- Inner mapping-end projections detect equality of the entire maps. -/
lemma innerHom_ext (X Y : SimplicialSpace.{u}) {K : SSet.{u}}
    {f g : K ⟶ (X ⟶[SSet.{u}] Y)}
    (h : ∀ m, f ≫ innerHomπ X Y m = g ≫ innerHomπ X Y m) : f = g :=
  SSet.simplicialSpacePointwiseHom_hom_ext X.diagram Y.diagram h

/-- Ordinary identity is the native enriched identity. -/
lemma innerHom_id (X : SimplicialSpace.{u}) : eHomEquiv SSet.{u} (𝟙 X) = eId SSet.{u} X :=
  eHomEquiv_id _ X

/-- Ordinary composition is represented by the native enriched composition. -/
lemma innerHom_comp {X Y Z : SimplicialSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv SSet.{u} (f ≫ g) =
      (λ_ _).inv ≫ (eHomEquiv SSet.{u} f ⊗ₘ eHomEquiv SSet.{u} g) ≫
        eComp SSet.{u} X Y Z := eHomEquiv_comp _ f g

end

/-- Tensor in the inner simplicial direction; its scalar is constant outerly. -/
abbrev innerTensor (K : SSet.{u}) : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  forget ⋙ (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
    (tensorRight K) ⋙ ofSimplicialObject

/-- Cotensor in the inner direction is pointwise internal Hom with the scalar. -/
abbrev innerCotensor (K : SSet.{u}) : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  forget ⋙ (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
    (ihom K) ⋙ ofSimplicialObject

/-- The inner tensor has bidegree `X_(m,n) × K_n`. -/
lemma innerTensor_obj_obj (K : SSet.{u}) (X : SimplicialSpace.{u})
    (m n : SimplexCategoryᵒᵖ) :
    (((innerTensor K).obj X).diagram.obj m).obj n =
      ((X.diagram.obj m).obj n × K.obj n) := rfl

/-- The actual inner tensor/cotensor adjunction on the chosen carrier. -/
def innerTensorCotensorAdjunction (K : SSet.{u}) : innerTensor K ⊣ innerCotensor K := by
  let a := ((ihom.adjunction K).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight K)).whiskerRight SimplexCategoryᵒᵖ
  exact (equivalenceSimplicialObject.toAdjunction.comp
    (a.comp equivalenceSimplicialObject.symm.toAdjunction))

/-- The inner tensor/cotensor left triangle is an equality of original maps. -/
lemma innerTensorCotensor_left_triangle (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    (innerTensor K).map ((innerTensorCotensorAdjunction K).unit.app X) ≫
      (innerTensorCotensorAdjunction K).counit.app ((innerTensor K).obj X) =
        𝟙 ((innerTensor K).obj X) :=
  (innerTensorCotensorAdjunction K).left_triangle_components X

/-- The inner tensor/cotensor right triangle is an equality of original maps. -/
lemma innerTensorCotensor_right_triangle (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    (innerTensorCotensorAdjunction K).unit.app ((innerCotensor K).obj X) ≫
      (innerCotensor K).map ((innerTensorCotensorAdjunction K).counit.app X) =
        𝟙 ((innerCotensor K).obj X) :=
  (innerTensorCotensorAdjunction K).right_triangle_components X

section
open scoped SimplicialSpace.Inner

/-- The original outer component of an inner tensor map.
It is the literal map `X.diagram.obj m ⊗ K ⟶ Y.diagram.obj m`. -/
abbrev tensorComponent (K : SSet.{u}) (X Y : SimplicialSpace.{u})
    (f : (innerTensor K).obj X ⟶ Y) (m : SimplexCategoryᵒᵖ) :
    X.diagram.obj m ⊗ K ⟶ Y.diagram.obj m := f.hom.app m

/-- Transpose an original inner tensor map into the actual enriched end.
The map is the native end lift of its componentwise currying maps. -/
def tensorToInnerHom (K : SSet.{u}) (X Y : SimplicialSpace.{u})
    (f : (innerTensor K).obj X ⟶ Y) : K ⟶ (X ⟶[SSet.{u}] Y) := by
  letI : EnrichedCategory SSet.{u} SSet.{u} := MonoidalClosed.enrichedCategorySelf _
  letI : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf _
  change K ⟶ Enriched.FunctorCategory.enrichedHom SSet.{u} X.diagram Y.diagram
  refine end_.lift (fun m => curry (tensorComponent K X Y f m)) ?_
  intro m n a
  simp only [Enriched.FunctorCategory.diagram_obj_map,
    Enriched.FunctorCategory.diagram_map_app,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  change curry (tensorComponent K X Y f m) ≫
      (ihom (X.diagram.obj m)).map (Y.diagram.map a) =
    curry (tensorComponent K X Y f n) ≫ (pre (X.diagram.map a)).app (Y.diagram.obj n)
  rw [← curry_natural_right, curry_pre_app]
  congr 1
  exact (f.hom.naturality a).symm

private lemma tensorToInnerHom_π (K : SSet.{u}) (X Y : SimplicialSpace.{u})
    (f : (innerTensor K).obj X ⟶ Y) (m : SimplexCategoryᵒᵖ) :
    tensorToInnerHom K X Y f ≫ innerHomπ X Y m =
      curry (tensorComponent K X Y f m) := by
  let _ : EnrichedCategory SSet.{u} SSet.{u} := MonoidalClosed.enrichedCategorySelf _
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf _
  dsimp [tensorToInnerHom, innerHomπ, SSet.simplicialSpacePointwiseHomπ]
  exact end_.lift_π _ _ _

/-- Uncurry a map into the actual enriched end to an original inner tensor map.
Its components are the native uncurrying maps and satisfy end naturality. -/
def innerHomToTensor (K : SSet.{u}) (X Y : SimplicialSpace.{u})
    (f : K ⟶ (X ⟶[SSet.{u}] Y)) : (innerTensor K).obj X ⟶ Y :=
  InducedCategory.homMk
    { app := fun m => uncurry (A := X.diagram.obj m) (f ≫ innerHomπ X Y m)
      naturality := by
        intro m n a
        have h := congrArg (fun g => f ≫ g) (innerHomπ_naturality X Y a)
        simp only [← Category.assoc] at h
        have hu := congrArg MonoidalClosed.uncurry h
        rw [uncurry_natural_right, uncurry_pre_app] at hu
        exact hu.symm }

/-- The inner tensor represents the actual enriched end at every scalar. -/
def innerTensorHomEquiv (K : SSet.{u}) (X Y : SimplicialSpace.{u}) :
    ((innerTensor K).obj X ⟶ Y) ≃ (K ⟶ (X ⟶[SSet.{u}] Y)) where
  toFun := tensorToInnerHom K X Y
  invFun := innerHomToTensor K X Y
  left_inv f := by
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext m
    change uncurry (tensorToInnerHom K X Y f ≫ innerHomπ X Y m) = f.hom.app m
    rw [tensorToInnerHom_π, uncurry_curry]
  right_inv f := by
    apply innerHom_ext X Y
    intro m
    rw [tensorToInnerHom_π]
    change curry (uncurry (f ≫ innerHomπ X Y m)) = _
    exact curry_uncurry _

/-- Currying into the end has its literal outer projection. -/
lemma innerTensorHomEquiv_π (K : SSet.{u}) (X Y : SimplicialSpace.{u})
    (f : (innerTensor K).obj X ⟶ Y) (m : SimplexCategoryᵒᵖ) :
    innerTensorHomEquiv K X Y f ≫ innerHomπ X Y m =
      curry (tensorComponent K X Y f m) := by
  exact tensorToInnerHom_π K X Y f m

/-- Inner mapping objects, functorial in both original designated variables. -/
abbrev innerHomFunctor : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  eHomFunctor SSet.{u} SimplicialSpace.{u}

/-- The inner tensor as a bifunctor, with the original space as first variable. -/
abbrev innerTensorBifunctor : SimplicialSpace.{u} ⥤ SSet.{u} ⥤ SimplicialSpace.{u} where
  obj X :=
    { obj := fun K => (innerTensor K).obj X
      map := fun f => InducedCategory.homMk
        { app := fun m => X.diagram.obj m ◁ f
          naturality := by
            intro m n a
            change (X.diagram.map a ▷ _) ≫ (X.diagram.obj n ◁ f) =
              (X.diagram.obj m ◁ f) ≫ (X.diagram.map a ▷ _)
            exact (whisker_exchange (X.diagram.map a) f).symm }
      map_id := by
        intro K
        apply InducedCategory.hom_ext
        apply NatTrans.ext
        funext m
        change X.diagram.obj m ◁ (𝟙 K) = 𝟙 (X.diagram.obj m ⊗ K)
        exact MonoidalCategory.whiskerLeft_id (X.diagram.obj m) K
      map_comp := by
        intro K L M f g
        apply InducedCategory.hom_ext
        apply NatTrans.ext
        funext m
        change X.diagram.obj m ◁ (f ≫ g) =
          (X.diagram.obj m ◁ f) ≫ (X.diagram.obj m ◁ g)
        exact MonoidalCategory.whiskerLeft_comp (X.diagram.obj m) f g }
  map {X Y} f :=
    { app := fun K => (innerTensor K).map f
      naturality := by
        intro K L a
        apply InducedCategory.hom_ext
        apply NatTrans.ext
        funext m
        change (f.hom.app m ▷ K) ≫ (Y.diagram.obj m ◁ a) =
          (X.diagram.obj m ◁ a) ≫ (f.hom.app m ▷ L)
        exact (whisker_exchange (f.hom.app m) a).symm }
  map_id := by
    intro X
    apply NatTrans.ext
    funext K
    exact (innerTensor K).map_id X
  map_comp := by
    intro X Y Z f g
    apply NatTrans.ext
    funext K
    exact (innerTensor K).map_comp f g

/-- Naturality of the inner end representation in the scalar. -/
lemma innerTensorHomEquiv_scalar {K L : SSet.{u}} (a : K ⟶ L)
    (X Y : SimplicialSpace.{u}) (f : (innerTensor L).obj X ⟶ Y) :
    innerTensorHomEquiv K X Y ((innerTensorBifunctor.obj X).map a ≫ f) =
      a ≫ innerTensorHomEquiv L X Y f := by
  apply innerHom_ext X Y
  intro m
  rw [Category.assoc, innerTensorHomEquiv_π, innerTensorHomEquiv_π]
  change curry (X.diagram.obj m ◁ a ≫ tensorComponent L X Y f m) =
    a ≫ curry (tensorComponent L X Y f m)
  exact curry_natural_left _ _

/-- Naturality in the original source, with the actual contravariant end map. -/
lemma innerTensorHomEquiv_source {X X' : SimplicialSpace.{u}} (a : X ⟶ X')
    (K : SSet.{u}) (Y : SimplicialSpace.{u}) (f : (innerTensor K).obj X' ⟶ Y) :
    innerTensorHomEquiv K X Y ((innerTensor K).map a ≫ f) =
      innerTensorHomEquiv K X' Y f ≫ (innerHomFunctor.map a.op).app Y := by
  apply innerHom_ext X Y
  intro m
  have hm : (innerHomFunctor.map a.op).app Y ≫ innerHomπ X Y m =
      innerHomπ X' Y m ≫ (pre (a.hom.app m)).app (Y.diagram.obj m) :=
    SSet.simplicialSpacePointwiseHomπ_map_source a.hom Y.diagram m
  rw [innerTensorHomEquiv_π]
  have hw := congrArg (fun z => innerTensorHomEquiv K X' Y f ≫ z) hm
  rw [← Category.assoc, innerTensorHomEquiv_π] at hw
  calc
    _ = curry (tensorComponent K X' Y f m) ≫
        (pre (a.hom.app m)).app (Y.diagram.obj m) :=
      (curry_pre_app (a.hom.app m) (tensorComponent K X' Y f m)).symm
    _ = _ := hw.symm.trans (Category.assoc _ _ _).symm

/-- Naturality in the original target, with the actual covariant end map. -/
lemma innerTensorHomEquiv_target (K : SSet.{u}) (X : SimplicialSpace.{u})
    {Y Y' : SimplicialSpace.{u}} (a : Y ⟶ Y') (f : (innerTensor K).obj X ⟶ Y) :
    innerTensorHomEquiv K X Y' (f ≫ a) =
      innerTensorHomEquiv K X Y f ≫ (innerHomFunctor.obj (op X)).map a := by
  apply innerHom_ext X Y'
  intro m
  have hm : (innerHomFunctor.obj (op X)).map a ≫ innerHomπ X Y' m =
      innerHomπ X Y m ≫ (ihom (X.diagram.obj m)).map (a.hom.app m) :=
    SSet.simplicialSpacePointwiseHomπ_map_target X.diagram a.hom m
  rw [innerTensorHomEquiv_π]
  have hw := congrArg (fun z => innerTensorHomEquiv K X Y f ≫ z) hm
  rw [← Category.assoc, innerTensorHomEquiv_π] at hw
  calc
    _ = curry (tensorComponent K X Y f m) ≫
        (ihom (X.diagram.obj m)).map (a.hom.app m) := curry_natural_right _ _
    _ = _ := hw.symm.trans (Category.assoc _ _ _).symm

/-- The ordinary tensor/end Hom-equivalence core at each original simplicial space.
Both native naturality fields use the actual scalar and target laws. -/
def innerTensorHomCore (X : SimplicialSpace.{u}) :
    Adjunction.CoreHomEquiv (innerTensorBifunctor.obj X) (innerHomFunctor.obj (op X)) where
  homEquiv := fun K Y => innerTensorHomEquiv K X Y
  homEquiv_naturality_left_symm := by
    intro K L Y a f
    let eK : ((innerTensorBifunctor.obj X).obj K ⟶ Y) ≃
        (K ⟶ (innerHomFunctor.obj (op X)).obj Y) := innerTensorHomEquiv K X Y
    let eL : ((innerTensorBifunctor.obj X).obj L ⟶ Y) ≃
        (L ⟶ (innerHomFunctor.obj (op X)).obj Y) := innerTensorHomEquiv L X Y
    apply eK.injective
    have h := innerTensorHomEquiv_scalar a X Y (eL.symm f)
    exact (eK.apply_symm_apply (a ≫ f)).trans
      (h.trans (congrArg (fun z => a ≫ z) (eL.apply_symm_apply f))).symm
  homEquiv_naturality_right := by
    intro K Y Y' f a
    exact innerTensorHomEquiv_target K X a f

/-- The ordinary inner tensor/end adjunction at each original simplicial space.
Its Hom equivalence is the actual public `innerTensorHomEquiv`. -/
def innerTensorHomAdjunction (X : SimplicialSpace.{u}) :
    innerTensorBifunctor.obj X ⊣ innerHomFunctor.obj (op X) :=
  Adjunction.mkOfHomEquiv (innerTensorHomCore X)

/-- The genuine native parametrized tensor/end adjunction. -/
def innerTensorHomAdjunction₂ : innerTensorBifunctor.{u} ⊣₂ innerHomFunctor.{u} :=
  ParametrizedAdjunction.mk' innerTensorHomAdjunction
    (by
      intro X Y a K Z f
      simp only [innerTensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
      exact innerTensorHomEquiv_source a K Z f)

end

end SimplicialSpace
