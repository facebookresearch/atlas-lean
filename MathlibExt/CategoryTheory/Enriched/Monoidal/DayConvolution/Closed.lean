/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.ExternalTensorMappingEndAdjunction
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LeftKanNaturality
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ColimitMonoidal
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ActionReconstruction
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The genuine enriched Day internal Hom

The right adjoint to the selected Day tensor is the parameterized weighted end
of the actual right translation of its target. At parameter `c` its projections
land in `[F(j), Y(j ⊗ c)]`. Both index factors act through their entire enriched
Hom objects. The construction uses the external tensor adjunction, the genuine
left Kan adjunction, and the original Day/Kan comparison, including its units
and both complete generator families.

No symmetry or commutativity is required of the index. The monoidal structure
is the previously constructed `ColimitMonoidal.monoidalCategory d`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.Closed

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)

/-- The full target on the original two index factors. -/
abbrev tensorRestriction (Y : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V (I × I) :=
  restrictionObject d.tensorEnrichedFunctor Y

/-- Insert the parameter through its full enriched identity, then tensor on the right. -/
def rightTranslationIndex (c : I) : EnrichedFunctor V I I :=
  (ExternalTensorMappingEndAdjunction.fixedRightPair (V := V) c).comp V
    d.tensorEnrichedFunctor

/-- The literal right translation `j ↦ Y(j ⊗ c)` with its complete enriched action. -/
abbrev translatedTarget (Y : EnrichedFunctorCat V I) (c : I) :
    EnrichedFunctorCat V I :=
  ExternalTensorMappingEndAdjunction.slice (tensorRestriction d Y) c

/-- Right translation retains the original target value at the original ordered index. -/
theorem translatedTarget_obj (Y : EnrichedFunctorCat V I) (c j : I) :
    (translatedTarget d Y c).toEnrichedFunctor.obj j =
      Y.toEnrichedFunctor.obj (j ⊗ c) := rfl

/-- The translated target is genuine restriction along the right tensor index functor. -/
theorem translatedTarget_eq_restriction (Y : EnrichedFunctorCat V I) (c : I) :
    translatedTarget d Y c = restrictionObject (rightTranslationIndex d c) Y := by
  have h : (translatedTarget d Y c).toEnrichedFunctor =
      (restrictionObject (rightTranslationIndex d c) Y).toEnrichedFunctor := by
    apply EnrichedFunctor.ext V
      (F := (translatedTarget d Y c).toEnrichedFunctor)
      (G := (restrictionObject (rightTranslationIndex d c) Y).toEnrichedFunctor)
      (fun _ => rfl)
    intro j k
    simp only [translatedTarget, tensorRestriction, rightTranslationIndex,
      ExternalTensorMappingEndAdjunction.slice, restrictionObject, EnrichedFunctor.comp,
      eqToHom_refl, Category.comp_id, Category.assoc]
  exact congrArg (fun F => (⟨F⟩ : EnrichedFunctorCat V I)) h

/-- Every original source-index Hom acts through its identity-weighted right translation. -/
theorem translatedTarget_map (Y : EnrichedFunctorCat V I) (c j k : I) :
    (translatedTarget d Y c).toEnrichedFunctor.map j k =
      (ExternalTensorMappingEndAdjunction.fixedRightPair (V := V) c).map j k ≫
        d.tensorEnrichedFunctor.map (j, c) (k, c) ≫
        Y.toEnrichedFunctor.map (j ⊗ c) (k ⊗ c) := rfl

variable [HasProducts.{uI} V] [HasEqualizers V]

/-- The actual Day internal-Hom value is the complete weighted end of the translated target. -/
abbrev object (F Y : EnrichedFunctorCat V I) (c : I) : V :=
  ExternalTensorMappingEndAdjunction.mappingObject F (tensorRestriction d Y) c

/-- The actual object is the complete weighted end of the literal translated target. -/
theorem object_eq (F Y : EnrichedFunctorCat V I) (c : I) :
    object d F Y c = WeightedEndVariance.object F (translatedTarget d Y c) := rfl

/-- Every original source-index object has its full internal-Hom projection. -/
abbrev π (F Y : EnrichedFunctorCat V I) (c j : I) :
    object d F Y c ⟶
      (ihom (F.toEnrichedFunctor.obj j)).obj (Y.toEnrichedFunctor.obj (j ⊗ c)) :=
  ExternalTensorMappingEndAdjunction.projection F (tensorRestriction d Y) c j

/-- The full parameterized end, including its entire enriched parameter action. -/
abbrev rightObject (F Y : EnrichedFunctorCat V I) : EnrichedFunctorCat V I :=
  ExternalTensorMappingEndAdjunction.rightObject F (tensorRestriction d Y)

/-- The constructed diagram uses the original full weighted end at every parameter. -/
@[simp]
theorem rightObject_obj (F Y : EnrichedFunctorCat V I) (c : I) :
    (rightObject d F Y).toEnrichedFunctor.obj c = object d F Y c := rfl

/-- The target variance consists of genuine tensor restriction followed by the end functor. -/
abbrev rightFunctor (F : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I :=
  restriction d.tensorEnrichedFunctor ⋙
    ExternalTensorMappingEndAdjunction.rightFunctor F

/-- Each parameter Hom acts on the translated target by its complete tensor Hom action. -/
abbrev parameterComponent (Y : EnrichedFunctorCat V I) (c c' j : I) :
    (c ⟶[V] c') ⟶
      (ihom (Y.toEnrichedFunctor.obj (j ⊗ c))).obj
        (Y.toEnrichedFunctor.obj (j ⊗ c')) :=
  (ExternalTensorMappingEndAdjunction.fixedLeftPair (V := V) j).map c c' ≫
    d.tensorEnrichedFunctor.map (j, c) (j, c') ≫
      Y.toEnrichedFunctor.map (j ⊗ c) (j ⊗ c')

/-- The full parameter action projects to composition with the original translated Hom map. -/
@[reassoc]
theorem rightObject_map_π (F Y : EnrichedFunctorCat V I) (c c' j : I) :
    MonoidalClosed.uncurry ((rightObject d F Y).toEnrichedFunctor.map c c') ≫
        π d F Y c' j =
      (π d F Y c j ⊗ₘ parameterComponent d Y c c' j) ≫
        eComp V (F.toEnrichedFunctor.obj j) (Y.toEnrichedFunctor.obj (j ⊗ c))
          (Y.toEnrichedFunctor.obj (j ⊗ c')) :=
  ExternalTensorMappingEndAdjunction.rightObject_map_π F (tensorRestriction d Y) c c' j

/-- Maps into an end value are determined by all original full component projections. -/
@[ext]
theorem hom_ext (F Y : EnrichedFunctorCat V I) (c : I) {P : V}
    {f g : P ⟶ object d F Y c}
    (h : ∀ j, f ≫ π d F Y c j = g ≫ π d F Y c j) : f = g :=
  Enriched.weightedEnd.hom_ext F.toEnrichedFunctor
    (translatedTarget d Y c).toEnrichedFunctor h

variable [HasColimitsOfSize.{uI, uI} V]

/-- The original fixed-source Day tensor functor retains both input coend maps. -/
abbrev leftFunctor (F : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V I ⥤ EnrichedFunctorCat V I :=
  (Functor.curry.obj (Input.bifunctor d.tensorEnrichedFunctor)).obj F

/-- The literal selected Day tensor object, without installing a second monoidal structure. -/
abbrev tensorObject (F G : EnrichedFunctorCat V I) : EnrichedFunctorCat V I :=
  (leftFunctor d F).obj G

/-- The original Day tensor and the composite external-tensor/Kan functor are naturally
isomorphic through their actual complete universal-property maps. -/
def tensorLanIso (F : EnrichedFunctorCat V I) :
    leftFunctor d F ≅
      ExternalTensorMappingEndAdjunction.leftFunctor F ⋙ leftKan d.tensorEnrichedFunctor :=
  NatIso.ofComponents
    (fun G => LeftKanComparison.iso d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor)
    (by
      intro G G' q
      exact LeftKanComparison.input_toKan d.tensorEnrichedFunctor (𝟙 F) q)

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Its forward map sends every full original Day generator to the original Kan generator. -/
@[reassoc]
theorem tensorLanIso_hom_gen (F G : EnrichedFunctorCat V I) (k : I) (p : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor k p ≫
        component ((tensorLanIso d F).hom.app G) k =
      Enriched.weightedCoend.ι (leftKanWeight d.tensorEnrichedFunctor k)
        (F.toEnrichedFunctor.externalTensor G.toEnrichedFunctor) p :=
  LeftKanComparison.gen_toKan d.tensorEnrichedFunctor
    F.toEnrichedFunctor G.toEnrichedFunctor k p

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Its inverse sends every full original Kan generator to the original Day generator. -/
@[reassoc]
theorem tensorLanIso_inv_ι (F G : EnrichedFunctorCat V I) (k : I) (p : I × I) :
    Enriched.weightedCoend.ι (leftKanWeight d.tensorEnrichedFunctor k)
        (F.toEnrichedFunctor.externalTensor G.toEnrichedFunctor) p ≫
        component ((tensorLanIso d F).inv.app G) k =
      EnrichedDayKernel.gen d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor k p :=
  LeftKanComparison.ι_fromKan d.tensorEnrichedFunctor
    F.toEnrichedFunctor G.toEnrichedFunctor k p

/-- The entire original Day tensor is left adjoint to the right-translation weighted end. -/
def adjunction (F : EnrichedFunctorCat V I) : leftFunctor d F ⊣ rightFunctor d F :=
  ((ExternalTensorMappingEndAdjunction.adjunction F).comp
    (leftKanRestrictionAdjunction d.tensorEnrichedFunctor)).ofNatIsoLeft
      (tensorLanIso d F).symm

/-- The constructed Day monoidal category has the actual parameterized ends as its closed
right adjoints. -/
@[instance_reducible]
def monoidalClosed :
    @MonoidalClosed (EnrichedFunctorCat V I) _ (ColimitMonoidal.monoidalCategory d) := by
  letI : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  exact {
    closed F := {
      rightAdj := rightFunctor d F
      adj := by
        change leftFunctor d F ⊣ rightFunctor d F
        exact adjunction d F } }

/-- The forward transpose retains both entire original Day and external-tensor maps. -/
def transpose (F G Y : EnrichedFunctorCat V I) (f : tensorObject d F G ⟶ Y) :
    G ⟶ rightObject d F Y :=
  ExternalTensorMappingEndAdjunction.transpose F G (tensorRestriction d Y)
    (ActionFromTransformation.extract d.tensorEnrichedFunctor F.toEnrichedFunctor
      G.toEnrichedFunctor Y.toEnrichedFunctor f)

/-- Each source component is exactly the curry of its original Day generator evaluation. -/
@[reassoc]
theorem transpose_component_π (F G Y : EnrichedFunctorCat V I)
    (f : tensorObject d F G ⟶ Y)
    (c j : I) :
    component (transpose d F G Y f) c ≫ π d F Y c j =
      MonoidalClosed.curry
        (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor
          G.toEnrichedFunctor (j, c) ≫ component f (j ⊗ c)) := by
  rw [transpose, ExternalTensorMappingEndAdjunction.transpose_component_π]
  exact congrArg MonoidalClosed.curry
    (ActionFromTransformation.extract_component d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor Y.toEnrichedFunctor f (j, c))

/-- The inverse transpose descends the entire original external evaluation through Day. -/
def untranspose (F G Y : EnrichedFunctorCat V I) (f : G ⟶ rightObject d F Y) :
    tensorObject d F G ⟶ Y :=
  ActionFromTransformation.transformation d.tensorEnrichedFunctor F.toEnrichedFunctor
    G.toEnrichedFunctor Y.toEnrichedFunctor
    (ExternalTensorMappingEndAdjunction.untranspose F G (tensorRestriction d Y) f)

/-- The inverse transpose keeps the complete output weight and the original closed evaluation. -/
@[reassoc]
theorem untranspose_gen (F G Y : EnrichedFunctorCat V I) (f : G ⟶ rightObject d F Y)
    (k : I) (p : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor k p ≫
        component (untranspose d F G Y f) k =
      (𝟙 ((p.1 ⊗ p.2) ⟶[V] k) ⊗ₘ
        MonoidalClosed.uncurry (component f p.2 ≫ π d F Y p.2 p.1)) ≫
        (β_ ((p.1 ⊗ p.2) ⟶[V] k) (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k) := by
  change EnrichedDayKernel.gen d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor k p ≫
    (eHomEquiv V).symm
      ((ActionFromTransformation.transformation d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor Y.toEnrichedFunctor
        (ExternalTensorMappingEndAdjunction.untranspose F G (tensorRestriction d Y) f)).app k)
      = _
  rw [ActionFromTransformation.gen_transformation]
  change (𝟙 ((p.1 ⊗ p.2) ⟶[V] k) ⊗ₘ
      component (ExternalTensorMappingEndAdjunction.untranspose F G (tensorRestriction d Y) f) p)
      ≫ ((β_ ((p.1 ⊗ p.2) ⟶[V] k)
        (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k)) = _
  rw [ExternalTensorMappingEndAdjunction.untranspose_component]

/-- Evaluation is the full inverse transpose of the identity on the constructed weighted end. -/
def evaluation (F Y : EnrichedFunctorCat V I) :
    tensorObject d F (rightObject d F Y) ⟶ Y :=
  untranspose d F (rightObject d F Y) Y (𝟙 (rightObject d F Y))

/-- Every full original output weight is retained by the evaluation generator formula. -/
@[reassoc]
theorem evaluation_gen (F Y : EnrichedFunctorCat V I) (k : I) (p : I × I) :
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F.toEnrichedFunctor
        (rightObject d F Y).toEnrichedFunctor k p ≫ component (evaluation d F Y) k =
      (𝟙 ((p.1 ⊗ p.2) ⟶[V] k) ⊗ₘ MonoidalClosed.uncurry (π d F Y p.2 p.1)) ≫
        (β_ ((p.1 ⊗ p.2) ⟶[V] k) (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k) := by
  rw [evaluation, untranspose_gen, component_id, Category.id_comp]

/-- Source variance is the full original weighted-end weight map at all right translations. -/
def pre {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (Y : EnrichedFunctorCat V I) : rightObject d F Y ⟶ rightObject d F' Y :=
  ExternalTensorMappingEndAdjunction.sourceMap f (tensorRestriction d Y)

omit [HasColimitsOfSize.{uI, uI} V] in
/-- Every source-variance projection is literal internal-Hom precomposition. -/
@[reassoc]
theorem pre_π {F F' : EnrichedFunctorCat V I} (f : F' ⟶ F)
    (Y : EnrichedFunctorCat V I) (c j : I) :
    component (pre d f Y) c ≫ π d F' Y c j =
      π d F Y c j ≫ (MonoidalClosed.pre (component f j)).app
        (Y.toEnrichedFunctor.obj (j ⊗ c)) :=
  ExternalTensorMappingEndAdjunction.sourceMap_component_π f (tensorRestriction d Y) c j

omit [HasColimitsOfSize.{uI, uI} V] in
/-- Every target-variance projection is literal postcomposition at the same right tensor index. -/
@[reassoc]
theorem rightMap_π (F : EnrichedFunctorCat V I) {Y Y' : EnrichedFunctorCat V I}
    (f : Y ⟶ Y') (c j : I) :
    component ((rightFunctor d F).map f) c ≫ π d F Y' c j =
      π d F Y c j ≫ (ihom (F.toEnrichedFunctor.obj j)).map (component f (j ⊗ c)) := by
  change component (ExternalTensorMappingEndAdjunction.rightMap F
      (restrictionMap d.tensorEnrichedFunctor f)) c ≫ π d F Y' c j = _
  rw [ExternalTensorMappingEndAdjunction.rightMap_component_π, restrictionMap_component]
  rfl

omit [HasColimitsOfSize.{uI, uI} V] in
/-- Source variance retains the whole source identity. -/
@[simp]
theorem pre_id (F Y : EnrichedFunctorCat V I) : pre d (𝟙 F) Y = 𝟙 (rightObject d F Y) :=
  ExternalTensorMappingEndAdjunction.sourceMap_id F (tensorRestriction d Y)

omit [HasColimitsOfSize.{uI, uI} V] in
/-- Source variance retains the full contravariant composition order. -/
theorem pre_comp {F F' F'' : EnrichedFunctorCat V I} (f : F' ⟶ F) (g : F'' ⟶ F')
    (Y : EnrichedFunctorCat V I) : pre d (g ≫ f) Y = pre d f Y ≫ pre d g Y :=
  ExternalTensorMappingEndAdjunction.sourceMap_comp f g (tensorRestriction d Y)

omit [HasColimitsOfSize.{uI, uI} V] in
/-- The entire source and target maps commute on the actual parameterized end. -/
theorem pre_naturality {F F' Y Y' : EnrichedFunctorCat V I} (f : F' ⟶ F) (g : Y ⟶ Y') :
    (rightFunctor d F).map g ≫ pre d f Y' = pre d f Y ≫ (rightFunctor d F').map g :=
  ExternalTensorMappingEndAdjunction.sourceMap_naturality f
    (restrictionMap d.tensorEnrichedFunctor g)

end CategoryTheory.EnrichedDayKernel.Closed
