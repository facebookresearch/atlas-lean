/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseIff
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# A small dense reflective presentation of the original category

Starting with local presentability at a supplied regular cardinal, the actual
Hom-shrinking equivalence and the small model of the actual presentable-object
subcategory produce a working-small dense index. The native lifted-Yoneda
left Kan extension is composed with that same equivalence to give an
adjunction whose right functor starts at the original coefficient category.

Every comparison with the shrunk Hom sets is an explicit equivalence. The
original objects and arrows, the two adjoint functors, their unit and counit,
and the original comma-colimit legs remain visible. No limit, opposite
well-poweredness or opposite generation hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM

namespace CategoryTheory.DenseReflectivePresentation

open Limits Opposite

variable (M : Type uM) [Category.{vM} M] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable M κ]

/-- Local presentability is transported by the genuine object-preserving
Hom-shrinking equivalence at the same supplied cardinal. -/
instance normalizedLocallyPresentable :
    IsCardinalLocallyPresentable (ShrinkHoms M) κ :=
  (ShrinkHoms.equivalence.{w} M).isCardinalLocallyPresentable κ

/-- The actual full subcategory of presentable normalized objects. -/
abbrev compactObjects := (isCardinalPresentable (ShrinkHoms M) κ).FullSubcategory

/-- A genuine small model of the actual presentable-object subcategory. -/
abbrev index := SmallModel.{w} (compactObjects M κ)

/-- The actual small-model equivalence used in this presentation. -/
def indexEquivalence : compactObjects M κ ≌ index M κ :=
  equivSmallModel.{w} (compactObjects M κ)

/-- The normalized dense diagram consists of the chosen presentable
representatives, with their actual original subcategory morphisms. -/
def normalizedDense : index M κ ⥤ ShrinkHoms M :=
  (indexEquivalence M κ).inverse ⋙ (isCardinalPresentable (ShrinkHoms M) κ).ι

instance normalizedDense_isDense : (normalizedDense M κ).IsDense := by
  dsimp [normalizedDense, indexEquivalence]
  infer_instance

/-- The dense functor lands in the original coefficient category. -/
def dense : index M κ ⥤ M :=
  normalizedDense M κ ⋙ (ShrinkHoms.equivalence.{w} M).inverse

instance dense_isDense : (dense M κ).IsDense := by
  dsimp [dense]
  infer_instance

instance normalizedDense_obj_presentable (d : index M κ) :
    IsCardinalPresentable ((normalizedDense M κ).obj d) κ :=
  ((indexEquivalence M κ).inverse.obj d).property

/-- Each dense representative is presentable in the original category at
the same supplied cardinal. -/
theorem dense_obj_presentable (d : index M κ) :
    IsCardinalPresentable ((dense M κ).obj d) κ :=
  (ShrinkHoms.equivalence.{w} M).symm.toAdjunction.isCardinalPresentable_leftAdjoint_obj κ
    ((normalizedDense M κ).obj d)

/-- The restricted Yoneda functor starts at the original category and
uses the explicit native Hom-shrinking map on each original arrow. -/
def restrictedYoneda : M ⥤ (index M κ)ᵒᵖ ⥤ Type w :=
  (ShrinkHoms.equivalence.{w} M).functor ⋙
    Presheaf.restrictedULiftYoneda.{w} (normalizedDense M κ)

instance restrictedYoneda_full : (restrictedYoneda M κ).Full := by
  dsimp [restrictedYoneda]
  infer_instance

instance restrictedYoneda_faithful : (restrictedYoneda M κ).Faithful := by
  dsimp [restrictedYoneda]
  infer_instance

/-- The reflector is the actual native left Kan extension followed by the
inverse of the same Hom-shrinking equivalence. -/
def left : ((index M κ)ᵒᵖ ⥤ Type w) ⥤ M :=
  (uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)) ⋙
    (ShrinkHoms.equivalence.{w} M).inverse

/-- The actual original-category adjunction is the composite of the native
lifted-Yoneda adjunction and the actual normalization equivalence adjunction. -/
def adjunction : left M κ ⊣ restrictedYoneda M κ :=
  (Presheaf.restrictedULiftYonedaAdjunction.{w}
    (uliftYoneda.{w}.leftKanExtensionUnit (normalizedDense M κ))).comp
      (ShrinkHoms.equivalence.{w} M).symm.toAdjunction

instance restrictedYonedaReflective : Reflective (restrictedYoneda M κ) where
  L := left M κ
  adj := adjunction M κ

/-- The original Hom set is explicitly equivalent to the corresponding
working-size restricted-Yoneda component, using the same native shrinking. -/
def homEquiv (d : index M κ) (X : M) :
    ((dense M κ).obj d ⟶ X) ≃ ((restrictedYoneda M κ).obj X).obj (op d) where
  toFun f := ULift.up (equivShrink _ f)
  invFun z := (equivShrink _).symm z.down
  left_inv f := (equivShrink _).symm_apply_apply f
  right_inv z := ULift.ext ((equivShrink _).apply_symm_apply z.down)

/-- The full component function is the actual Hom-shrinking functor map. -/
theorem homEquiv_apply (d : index M κ) (X : M) (f : (dense M κ).obj d ⟶ X) :
    homEquiv M κ d X f =
      ULift.up ((ShrinkHoms.equivalence.{w} M).functor.map f) := rfl

/-- The full inverse component function is the actual inverse functor map. -/
theorem homEquiv_symm_apply (d : index M κ) (X : M)
    (z : ((restrictedYoneda M κ).obj X).obj (op d)) :
    (homEquiv M κ d X).symm z =
      (ShrinkHoms.equivalence.{w} M).inverse.map z.down := rfl

/-- Postcomposition by any original arrow is retained in the component
equivalence and the actual restricted-Yoneda arrow function. -/
theorem homEquiv_naturality_right (d : index M κ) {X Y : M}
    (f : (dense M κ).obj d ⟶ X) (g : X ⟶ Y) :
    homEquiv M κ d Y (f ≫ g) =
      ((restrictedYoneda M κ).map g).app (op d) (homEquiv M κ d X f) := by
  change ULift.up ((ShrinkHoms.equivalence.{w} M).functor.map (f ≫ g)) =
    ULift.up ((ShrinkHoms.equivalence.{w} M).functor.map f ≫
      (ShrinkHoms.equivalence.{w} M).functor.map g)
  rw [Functor.map_comp]

/-- Precomposition by an actual dense-index arrow is retained without
identifying the original and shrunk Hom functions. -/
theorem homEquiv_naturality_left {d e : index M κ} (a : d ⟶ e) (X : M)
    (f : (dense M κ).obj e ⟶ X) :
    homEquiv M κ d X ((dense M κ).map a ≫ f) =
      ((restrictedYoneda M κ).obj X).map a.op (homEquiv M κ e X f) := by
  change ULift.up ((ShrinkHoms.equivalence.{w} M).functor.map
    ((dense M κ).map a ≫ f)) =
      ULift.up ((normalizedDense M κ).map a ≫
        (ShrinkHoms.equivalence.{w} M).functor.map f)
  rw [Functor.map_comp]
  congr 2
  exact (equivShrink _).apply_symm_apply _

/-- The actual native comma shape used by the left Kan extension. -/
abbrev presentationShape (P : (index M κ)ᵒᵖ ⥤ Type w) :=
  CostructuredArrow uliftYoneda.{w} P

/-- Every actual source comma shape is working-small. -/
theorem presentationShape_small (P : (index M κ)ᵒᵖ ⥤ Type w) :
    Small.{w} (presentationShape M κ P) := inferInstance

/-- The original diagram is the actual comma projection followed by the
normalized dense functor and its inverse normalization. -/
def presentationDiagram (P : (index M κ)ᵒᵖ ⥤ Type w) : presentationShape M κ P ⥤ M :=
  (CostructuredArrow.proj uliftYoneda.{w} P ⋙ normalizedDense M κ) ⋙
    (ShrinkHoms.equivalence.{w} M).inverse

/-- The chosen original cocone is the actual native pointwise Kan cocone
mapped through the same inverse equivalence. -/
def presentationCocone (P : (index M κ)ᵒᵖ ⥤ Type w) :
    Cocone (presentationDiagram M κ P) :=
  (ShrinkHoms.equivalence.{w} M).inverse.mapCocone
    ((Functor.LeftExtension.mk _ (uliftYoneda.{w}.leftKanExtensionUnit
      (normalizedDense M κ))).coconeAt P)

/-- Local presentability supplies the native working-size comma colimit;
the same original cocone is colimiting by equivalence preservation. -/
def presentationIsColimit (P : (index M κ)ᵒᵖ ⥤ Type w) :
    IsColimit (presentationCocone M κ P) :=
  isColimitOfPreserves (ShrinkHoms.equivalence.{w} M).inverse
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      uliftYoneda.{w} (normalizedDense M κ) P)

/-- The original diagram retains the actual dense object of every comma leg. -/
theorem presentationDiagram_obj (P : (index M κ)ᵒᵖ ⥤ Type w)
    (j : presentationShape M κ P) :
    (presentationDiagram M κ P).obj j = (dense M κ).obj j.left := rfl

/-- The original diagram retains the actual dense arrow of every comma square. -/
theorem presentationDiagram_map (P : (index M κ)ᵒᵖ ⥤ Type w)
    {j k : presentationShape M κ P} (a : j ⟶ k) :
    (presentationDiagram M κ P).map a = (dense M κ).map a.left := rfl

/-- Every original colimit leg is the actual inverse image of the full
native Kan unit and arrow composite. -/
theorem presentationCocone_ι (P : (index M κ)ᵒᵖ ⥤ Type w)
    (j : presentationShape M κ P) :
    (presentationCocone M κ P).ι.app j =
      (ShrinkHoms.equivalence.{w} M).inverse.map
        ((uliftYoneda.{w}.leftKanExtensionUnit (normalizedDense M κ)).app j.left ≫
          (uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)).map j.hom) := rfl

/-- The original cocone leg indexed by a presheaf element. -/
def generatorLeg (P : (index M κ)ᵒᵖ ⥤ Type w) (d : index M κ) (x : P.obj (op d)) :
    (dense M κ).obj d ⟶ (left M κ).obj P :=
  (presentationCocone M κ P).ι.app
    (CostructuredArrow.mk (uliftYonedaEquiv.symm x))

/-- The entire original adjunction transpose is determined on every
element by the actual original generator leg and original arrow. -/
theorem adjunction_homEquiv_app (P : (index M κ)ᵒᵖ ⥤ Type w) (X : M)
    (f : (left M κ).obj P ⟶ X) (d : index M κ) (x : P.obj (op d)) :
    ((adjunction M κ).homEquiv P X f).app (op d) x =
      homEquiv M κ d X (generatorLeg M κ P d x ≫ f) := by
  let a := Presheaf.restrictedULiftYonedaAdjunction.{w}
    (uliftYoneda.{w}.leftKanExtensionUnit (normalizedDense M κ))
  let e := (ShrinkHoms.equivalence.{w} M).symm.toAdjunction
  let f' : (ShrinkHoms.equivalence.{w} M).inverse.obj
    ((uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)).obj P) ⟶ X := f
  let leg : (dense M κ).obj d ⟶ (ShrinkHoms.equivalence.{w} M).inverse.obj
    ((uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)).obj P) :=
      generatorLeg M κ P d x
  change ((a.comp e).homEquiv P X f').app (op d) x =
    ULift.up ((ShrinkHoms.equivalence.{w} M).functor.map (leg ≫ f'))
  rw [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply, a]
  rw [Presheaf.restrictedULiftYonedaAdjunction_homEquiv_app]
  change ULift.up (_ ≫ _ ≫ _) = ULift.up
    ((ShrinkHoms.equivalence.{w} M).functor.map (leg ≫ f'))
  rw [Functor.map_comp]
  have hf : (e.homEquiv _ X) f' =
      (ShrinkHoms.equivalence.{w} M).functor.map f' := by
    rw [Adjunction.homEquiv_unit]
    change (𝟙 _) ≫ (ShrinkHoms.equivalence.{w} M).functor.map f' = _
    rw [Category.id_comp]
  let u : (normalizedDense M κ).obj d ⟶
      (uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)).obj P :=
    (uliftYoneda.{w}.leftKanExtensionUnit (normalizedDense M κ)).app d ≫
      (uliftYoneda.{w}.leftKanExtension (normalizedDense M κ)).map
        (uliftYonedaEquiv.symm x)
  have hleg : (ShrinkHoms.equivalence.{w} M).functor.map leg = u := by
    change (equivShrink _) ((equivShrink _).symm u) = u
    exact (equivShrink _).apply_symm_apply u
  rw [hf, hleg]
  dsimp only [u]
  congr 1
  exact (Category.assoc _ _ _).symm

/-- The actual unit has the full original generator-leg component function. -/
theorem unit_app_app (P : (index M κ)ᵒᵖ ⥤ Type w) (d : index M κ)
    (x : P.obj (op d)) :
    ((adjunction M κ).unit.app P).app (op d) x =
      homEquiv M κ d ((left M κ).obj P) (generatorLeg M κ P d x) := by
  have h := adjunction_homEquiv_app M κ P ((left M κ).obj P) (𝟙 _) d x
  rw [(adjunction M κ).homEquiv_id] at h
  simpa using h

/-- Both adjunction directions retain the original arrow on every
generator leg, including the full inverse transpose function. -/
theorem generatorLeg_homEquiv_symm (P : (index M κ)ᵒᵖ ⥤ Type w) (X : M)
    (α : P ⟶ (restrictedYoneda M κ).obj X) (d : index M κ) (x : P.obj (op d)) :
    generatorLeg M κ P d x ≫ ((adjunction M κ).homEquiv P X).symm α =
      (homEquiv M κ d X).symm (α.app (op d) x) := by
  apply (homEquiv M κ d X).injective
  rw [Equiv.apply_symm_apply]
  rw [← adjunction_homEquiv_app]
  simp

/-- The actual counit composes with every original restricted-Yoneda
element leg to recover precisely the original arrow represented by it. -/
theorem counit_generatorLeg (X : M) (d : index M κ) (f : (dense M κ).obj d ⟶ X) :
    generatorLeg M κ ((restrictedYoneda M κ).obj X) d (homEquiv M κ d X f) ≫
      (adjunction M κ).counit.app X = f := by
  have h := generatorLeg_homEquiv_symm M κ ((restrictedYoneda M κ).obj X) X
    (𝟙 _) d (homEquiv M κ d X f)
  rw [(adjunction M κ).homEquiv_symm_id] at h
  simpa using h

end CategoryTheory.DenseReflectivePresentation
