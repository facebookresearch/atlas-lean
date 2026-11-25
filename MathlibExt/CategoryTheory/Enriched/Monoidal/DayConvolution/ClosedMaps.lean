/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Closed

/-!
# Original maps of the enriched Day closed adjunction

The composite adjunction's Hom functions are the actual generator transpose
and evaluation descent. Its unit projects to the curry of the whole original
Day generator, and its counit retains every full output-weight evaluation
component. Both original triangle identities are preserved.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.Closed

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)

/-- The actual composite Day adjunction transposes the literal original generators. -/
theorem adjunction_homEquiv (F G Y : EnrichedFunctorCat V I)
    (f : tensorObject d F G ⟶ Y) :
    (adjunction d F).homEquiv G Y f = transpose d F G Y f := by
  rw [adjunction, Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv,
    leftKanRestrictionAdjunction_homEquiv,
    ExternalTensorMappingEndAdjunction.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  dsimp only [rightFunctor, ExternalTensorMappingEndAdjunction.rightFunctor,
    leftKan, Functor.comp_obj]
  rw [Equiv.trans_apply, leftKanHomEquiv_apply,
    ExternalTensorMappingEndAdjunction.homEquiv]
  change ExternalTensorMappingEndAdjunction.transpose F G (tensorRestriction d Y)
      (leftKanHomToRestriction d.tensorEnrichedFunctor
        (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) Y
        (LeftKanComparison.fromKan d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor ≫ f)) = _
  rw [leftKanHomToRestriction, Functor.map_comp, ← Category.assoc,
    LeftKanComparison.unit_fromKan]
  rfl

/-- Transposition followed by actual Day evaluation descent recovers the entire original map. -/
theorem untranspose_transpose (F G Y : EnrichedFunctorCat V I)
    (f : tensorObject d F G ⟶ Y) :
    untranspose d F G Y (transpose d F G Y f) = f := by
  rw [untranspose, transpose, ExternalTensorMappingEndAdjunction.untranspose_transpose]
  exact ActionFromTransformation.transformation_extract d.tensorEnrichedFunctor
    F.toEnrichedFunctor G.toEnrichedFunctor Y.toEnrichedFunctor f

/-- The inverse composite Hom map is the full original evaluation descent. -/
theorem adjunction_homEquiv_symm (F G Y : EnrichedFunctorCat V I)
    (f : G ⟶ rightObject d F Y) :
    ((adjunction d F).homEquiv G Y).symm f = untranspose d F G Y f := by
  have h := untranspose_transpose d F G Y (((adjunction d F).homEquiv G Y).symm f)
  rw [← adjunction_homEquiv, Equiv.apply_symm_apply] at h
  exact h.symm

/-- Actual evaluation descent followed by generator transposition recovers the whole map
into the original parameterized end. -/
theorem transpose_untranspose (F G Y : EnrichedFunctorCat V I)
    (f : G ⟶ rightObject d F Y) :
    transpose d F G Y (untranspose d F G Y f) = f := by
  rw [← adjunction_homEquiv_symm, ← adjunction_homEquiv, Equiv.apply_symm_apply]

/-- The original Day Hom equivalence includes both entire original universal-property maps. -/
def homEquiv (F G Y : EnrichedFunctorCat V I) :
    (tensorObject d F G ⟶ Y) ≃ (G ⟶ rightObject d F Y) where
  toFun := transpose d F G Y
  invFun := untranspose d F G Y
  left_inv := untranspose_transpose d F G Y
  right_inv := transpose_untranspose d F G Y

/-- The actual closed unit is the generator transpose of the entire tensor identity. -/
theorem adjunction_unit_app (F G : EnrichedFunctorCat V I) :
    (adjunction d F).unit.app G =
      transpose d F G (tensorObject d F G) (𝟙 (tensorObject d F G)) := by
  have h := (adjunction d F).homEquiv_unit G (tensorObject d F G)
    (𝟙 (tensorObject d F G))
  rw [adjunction_homEquiv] at h
  rw [Functor.map_id] at h
  change transpose d F G (tensorObject d F G) (𝟙 (tensorObject d F G)) =
    (adjunction d F).unit.app G ≫ 𝟙 (rightObject d F (tensorObject d F G)) at h
  exact (h.trans (Category.comp_id ((adjunction d F).unit.app G))).symm

/-- Every full original unit projection is the curry of its original actual Day generator. -/
@[reassoc]
theorem adjunction_unit_π (F G : EnrichedFunctorCat V I) (c j : I) :
    component ((adjunction d F).unit.app G) c ≫ π d F (tensorObject d F G) c j =
      MonoidalClosed.curry
        (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor
          (j, c)) := by
  rw [adjunction_unit_app]
  have h := transpose_component_π d F G (tensorObject d F G) (𝟙 (tensorObject d F G)) c j
  rw [component_id] at h
  exact h.trans (congrArg MonoidalClosed.curry
    (Category.comp_id (Generators.point d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor (j, c))))

/-- The actual composite counit is the original complete weighted-end evaluation descent. -/
theorem adjunction_counit_app (F Y : EnrichedFunctorCat V I) :
    (adjunction d F).counit.app Y = evaluation d F Y := by
  have h := (adjunction d F).homEquiv_counit (rightObject d F Y) Y
    (𝟙 (rightObject d F Y))
  rw [adjunction_homEquiv_symm] at h
  simpa only [Functor.map_id, Category.id_comp, evaluation] using h.symm

/-- Every complete original output weight projects the counit to actual closed evaluation. -/
@[reassoc]
theorem adjunction_counit_gen (F Y : EnrichedFunctorCat V I) (k : I) (p : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F.toEnrichedFunctor
        (rightObject d F Y).toEnrichedFunctor k p ≫
        component ((adjunction d F).counit.app Y) k =
      (𝟙 ((p.1 ⊗ p.2) ⟶[V] k) ⊗ₘ MonoidalClosed.uncurry (π d F Y p.2 p.1)) ≫
        (β_ ((p.1 ⊗ p.2) ⟶[V] k) (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k) := by
  rw [adjunction_counit_app]
  exact evaluation_gen d F Y k p

/-- The whole source tensor triangle retains the actual original Day evaluation. -/
theorem adjunction_left_triangle (F G : EnrichedFunctorCat V I) :
    (leftFunctor d F).map ((adjunction d F).unit.app G) ≫
      evaluation d F (tensorObject d F G) = 𝟙 (tensorObject d F G) := by
  rw [← adjunction_counit_app]
  exact (adjunction d F).left_triangle_components G

/-- The whole source end triangle retains the actual original Day evaluation and target map. -/
theorem adjunction_right_triangle (F Y : EnrichedFunctorCat V I) :
    (adjunction d F).unit.app (rightObject d F Y) ≫
      (rightFunctor d F).map (evaluation d F Y) = 𝟙 (rightObject d F Y) := by
  rw [← adjunction_counit_app]
  exact (adjunction d F).right_triangle_components Y

/-- Every actual identity-weight Day point evaluates by the original full end projection. -/
@[reassoc]
theorem evaluation_point (F Y : EnrichedFunctorCat V I) (j c : I) :
    Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor
        (rightObject d F Y).toEnrichedFunctor (j, c) ≫ component (evaluation d F Y) (j ⊗ c) =
      MonoidalClosed.uncurry (π d F Y c j) := by
  have h := transpose_untranspose d F (rightObject d F Y) Y (𝟙 (rightObject d F Y))
  have hp := congrArg (fun t => component t c ≫ π d F Y c j) h
  change component (transpose d F (rightObject d F Y) Y (evaluation d F Y)) c ≫
    π d F Y c j = component (𝟙 (rightObject d F Y)) c ≫ π d F Y c j at hp
  rw [transpose_component_π, component_id, Category.id_comp] at hp
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_uncurry]
  exact hp

/-- The closed-class curry is the original full generator transpose at every right index. -/
@[reassoc]
theorem closedCurry_π (F G Y : EnrichedFunctorCat V I)
    (f : tensorObject d F G ⟶ Y) (c j : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := monoidalClosed d
    component (MonoidalClosed.curry f) c ≫ π d F Y c j =
      MonoidalClosed.curry
        (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor
          G.toEnrichedFunctor (j, c) ≫ component f (j ⊗ c)) := by
  let := ColimitMonoidal.monoidalCategory d
  let := monoidalClosed d
  change component ((adjunction d F).homEquiv G Y f) c ≫ π d F Y c j = _
  rw [adjunction_homEquiv, transpose_component_π]

/-- Actual closed-class source precomposition preserves each original complete internal-Hom
projection, with the literal source carrier map. -/
@[reassoc]
theorem closedPre_π {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (Y : EnrichedFunctorCat V I) (c j : I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := monoidalClosed d
    component ((MonoidalClosed.pre f).app Y) c ≫ π d F' Y c j =
      π d F Y c j ≫ (MonoidalClosed.pre (component f j)).app
        (Y.toEnrichedFunctor.obj (j ⊗ c)) := by
  let := ColimitMonoidal.monoidalCategory d
  let := monoidalClosed d
  let H := rightObject d F Y
  have hpre : (MonoidalClosed.pre f).app Y =
      MonoidalClosed.curry ((f ▷ H) ≫ evaluation d F Y) := by
    rw [← adjunction_counit_app]
    change (MonoidalClosed.pre f).app Y =
      MonoidalClosed.curry ((f ▷ (ihom F).obj Y) ≫ (ihom.ev F).app Y)
    rw [← MonoidalClosed.uncurry_pre, MonoidalClosed.curry_uncurry]
  have hmap : component (f ▷ H) (j ⊗ c) =
      Input.mapAt d.tensorEnrichedFunctor f (𝟙 H) (j ⊗ c) := by
    rw [← tensorHom_id, ColimitMonoidal.tensorHom_eq]
    exact Input.bifunctor_map_component d.tensorEnrichedFunctor f (𝟙 H) (j ⊗ c)
  have hp := Generators.point_input_natural d.tensorEnrichedFunctor f (𝟙 H) (j, c)
  change Generators.point d.tensorEnrichedFunctor F'.toEnrichedFunctor H.toEnrichedFunctor
      (j, c) ≫ Input.mapAt d.tensorEnrichedFunctor f (𝟙 H) (j ⊗ c) =
    (component f j ⊗ₘ component (𝟙 H) c) ≫
      Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor H.toEnrichedFunctor
        (j, c) at hp
  rw [component_id, tensorHom_id] at hp
  rw [hpre, closedCurry_π]
  change MonoidalClosed.curry
    (Generators.point d.tensorEnrichedFunctor F'.toEnrichedFunctor H.toEnrichedFunctor
      (j, c) ≫ component ((f ▷ H) ≫ evaluation d F Y) (j ⊗ c)) = _
  rw [component_comp, ← Category.assoc, hmap, hp,
    Category.assoc, evaluation_point, ← MonoidalClosed.curry_pre_app,
    MonoidalClosed.curry_uncurry]

/-- The closed-class source map is the same actual complete source map as the original
parameterized-end construction. -/
theorem closedPre_eq {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (Y : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := monoidalClosed d
    (MonoidalClosed.pre f).app Y = pre d f Y := by
  let := ColimitMonoidal.monoidalCategory d
  let := monoidalClosed d
  apply EnrichedFunctorCat.hom_ext
  intro c
  apply hom_ext d F' Y c
  intro j
  exact (closedPre_π d f Y c j).trans (pre_π d f Y c j).symm

end CategoryTheory.EnrichedDayKernel.Closed
