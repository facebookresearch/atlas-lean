/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.ExternalTensorMappingEndAdjunction
import Batteries.Tactic.Lint

/-!
# Public clients of the full external tensor/end adjunction

The two index types are plain enriched types with independent universes.
The clients retain whole parameter Homs, both transpose directions, actual
source and target maps, every ambient coefficient and its regrading, the
original tensor specialization, and the complete unit and counit triangles.
-/

public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB vI

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.ExternalTensorMappingEndAdjunctionTests

open EnrichedFunctorCat EnrichedFunctorCat.ExternalTensorMappingEndAdjunction

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

-- This equality acts on both entire original Hom objects.
omit [MonoidalClosed V] in
/-- The entire product Hom retains both original identity insertions. -/
theorem wholeProductFactorization (a a' : A) (b b' : B) :
    (((fixedRightPair (V := V) b).map a a') ⊗ₘ
      (fixedLeftPair (V := V) a').map b b') ≫
      eComp V (a, b) (a', b) (a', b') =
        𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b')) :=
  product_factorization a a' b b'

-- Neither index requires an ordinary category dictionary.
/-- The fixed-first slice retains the whole original scalar action. -/
theorem fixedFirstAction (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (a : A) (b b' : B) :
    MonoidalClosed.uncurry (((fixedLeftPair (V := V) a).comp V
      (F.toEnrichedFunctor.externalTensor X.toEnrichedFunctor)).map b b') =
      (α_ (F.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj b) (b ⟶[V] b')).hom ≫
        F.toEnrichedFunctor.obj a ◁ MonoidalClosed.uncurry (X.toEnrichedFunctor.map b b') :=
  external_leftSlice_action F X a b b'

variable [HasProducts.{uA} V] [HasEqualizers V]

/-- The actual parameter object is the original weighted end. -/
theorem originalEndObject (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    (rightObject F Y).toEnrichedFunctor.obj b =
      Enriched.weightedEnd F.toEnrichedFunctor (slice Y b).toEnrichedFunctor := rfl

-- The complete parameter map projects to the original product action.
/-- The entire parameter Hom acts through the original end projection. -/
theorem wholeParameterProjection (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B))
    (b b' : B) (a : A) :
    MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b') ≫ projection F Y b' a =
      (projection F Y b a ⊗ₘ
        ((fixedLeftPair (V := V) a).map b b' ≫ Y.toEnrichedFunctor.map (a, b) (a, b'))) ≫
        eComp V (F.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj (a, b))
          (Y.toEnrichedFunctor.obj (a, b')) :=
  rightObject_map_π F Y b b' a

/-- The forward transpose retains each complete original curry component. -/
theorem forwardBeta (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) (a : A) (b : B) :
    component (homEquiv F X Y g) b ≫ projection F Y b a =
      MonoidalClosed.curry (component g (a, b)) := transpose_component_π F X Y g b a

/-- The inverse transpose retains each complete original uncurry component. -/
theorem inverseBeta (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) (a : A) (b : B) :
    component ((homEquiv F X Y).symm h) (a, b) =
      MonoidalClosed.uncurry (component h b ≫ projection F Y b a) :=
  untranspose_component F X Y h a b

/-- The full product transformation survives the two transpose directions. -/
theorem productRoundTrip (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) :
    (homEquiv F X Y).symm (homEquiv F X Y g) = g := (homEquiv F X Y).symm_apply_apply g

/-- The full end-valued transformation survives the two transpose directions. -/
theorem endRoundTrip (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) :
    homEquiv F X Y ((homEquiv F X Y).symm h) = h := (homEquiv F X Y).apply_symm_apply h

-- Full output-Hom naturality, rather than an equality only on identity points.
/-- The forward transpose preserves the entire parameter Hom action. -/
theorem wholeForwardNaturality (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) (b b' : B) :
    MonoidalClosed.uncurry (X.toEnrichedFunctor.map b b') ≫ component (transpose F X Y g) b' =
      (component (transpose F X Y g) b ⊗ₘ 𝟙 (b ⟶[V] b')) ≫
        MonoidalClosed.uncurry ((rightObject F Y).toEnrichedFunctor.map b b') :=
  (transpose F X Y g).uncurriedNaturality b b'

/-- The inverse transpose preserves both entire product Hom actions. -/
theorem wholeInverseNaturality (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (h : X ⟶ rightObject F Y) (p p' : A × B) :
    MonoidalClosed.uncurry (((leftFunctor F).obj X).toEnrichedFunctor.map p p') ≫
      component (untranspose F X Y h) p' =
      (component (untranspose F X Y h) p ⊗ₘ 𝟙 (p ⟶[V] p')) ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map p p') :=
  (untranspose F X Y h).uncurriedNaturality p p'

-- Both actual variances use the original chosen end maps.
/-- Target variance uses the actual original weighted-end diagram map. -/
theorem originalTargetMap (F : EnrichedFunctorCat V A) {Y Z : EnrichedFunctorCat V (A × B)}
    (q : Y ⟶ Z) (b : B) :
    component ((rightFunctor F).map q) b =
      WeightedEndVariance.post F (restrictionMap (fixedRightPair (V := V) b) q) :=
  rightMap_component F q b

/-- Weight variance uses the actual original weighted-end weight map. -/
theorem originalWeightMap {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    component (sourceMap p Y) b = WeightedEndVariance.pre p (slice Y b) :=
  sourceMap_component p Y b

/-- The two complete original weighted-end variances commute. -/
theorem commutingSourceTargetMaps {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z) :
    (rightFunctor F).map q ≫ (sourceNatTrans p).app Z =
      (sourceNatTrans p).app Y ≫ (rightFunctor F').map q :=
  (sourceNatTrans p).naturality q

/-- The complete second input transformation is retained by transposition. -/
theorem inputNaturality (F : EnrichedFunctorCat V A) {X X' : EnrichedFunctorCat V B} (f : X' ⟶ X)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) :
    homEquiv F X' Y ((leftFunctor F).map f ≫ g) = f ≫ homEquiv F X Y g :=
  transpose_naturality_left F f Y g

/-- The complete weight transformation is retained contravariantly. -/
theorem weightNaturality {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (g : (leftFunctor F).obj X ⟶ Y) :
    homEquiv F' X Y (leftWeightMap p X ≫ g) = homEquiv F X Y g ≫ sourceMap p Y :=
  transpose_naturality_source p X Y g

/-- The complete original target transformation is retained covariantly. -/
theorem targetNaturality (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    {Y Z : EnrichedFunctorCat V (A × B)} (g : (leftFunctor F).obj X ⟶ Y) (q : Y ⟶ Z) :
    homEquiv F X Z (g ≫ q) = homEquiv F X Y g ≫ (rightFunctor F).map q :=
  transpose_naturality_right F X g q

-- Every ambient coefficient remains present in both complete component formulas.
/-- Every coefficient retains the complete original forward component. -/
theorem coefficientForwardBeta (M : V) (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) (a : A) (b : B) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
        (gradedHomEquiv M F X Y t) b ≫ projection F Y b a =
      MonoidalClosed.curry
        ((scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
          (X.toEnrichedFunctor.obj b)).hom ≫
            GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (a, b)) :=
  gradedHomEquiv_apply_π M F X Y t b a

/-- Every coefficient retains the complete original inverse component. -/
theorem coefficientInverseBeta (M : V) (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B))
    (h : GradedNatTrans ((Center.ofBraided V).obj M) X.toEnrichedFunctor
      (rightObject F Y).toEnrichedFunctor) (a : A) (b : B) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
        ((gradedHomEquiv M F X Y).symm h) (a, b) =
      (scalarExternalComponentIso M (F.toEnrichedFunctor.obj a)
        (X.toEnrichedFunctor.obj b)).inv ≫
          MonoidalClosed.uncurry
            (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) h b ≫
              projection F Y b a) := gradedHomEquiv_symm_gradeFirst M F X Y h a b

omit [MonoidalClosed V] [HasProducts.{uA} V] [HasEqualizers V] in
/-- The scalar crossing is the actual canonical braiding and associators. -/
theorem canonicalCoefficientCrossing (M : V) (U K : V) :
    (scalarExternalComponentIso M U K).hom =
      (α_ U M K).inv ≫ ((β_ U M).hom ▷ K) ≫ (α_ M U K).hom :=
  scalarExternalComponentIso_hom M U K

/-- Every actual coefficient arrow acts through genuine regrading. -/
theorem coefficientRegrading {M M' : V} (r : M' ⟶ M) (F : EnrichedFunctorCat V A)
    (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M' F X Y (GradedNatTrans.regrade ((Center.ofBraided V).map r) t) =
      GradedNatTrans.regrade ((Center.ofBraided V).map r) (gradedHomEquiv M F X Y t) :=
  gradedHomEquiv_regrade r F X Y t

/-- Every coefficient retains the complete original weight transformation. -/
theorem coefficientWeightNaturality (M : V) {F F' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (X : EnrichedFunctorCat V B) (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M F' X Y (gradedPrecomp ((Center.ofBraided V).obj M) (leftWeightMap p X) t) =
      gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv M F X Y t) (sourceMap p Y) :=
  gradedHomEquiv_naturality_source M p X Y t

/-- Every coefficient retains the complete original second input map. -/
theorem coefficientInputNaturality (M : V) (F : EnrichedFunctorCat V A) {X X' : EnrichedFunctorCat V B} (f : X' ⟶ X)
    (Y : EnrichedFunctorCat V (A × B))
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M F X' Y
        (gradedPrecomp ((Center.ofBraided V).obj M) ((leftFunctor F).map f) t) =
      gradedPrecomp ((Center.ofBraided V).obj M) f (gradedHomEquiv M F X Y t) :=
  gradedHomEquiv_naturality_left M F f Y t

/-- Every coefficient retains the complete original target map. -/
theorem coefficientTargetNaturality (M : V) (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    {Y Z : EnrichedFunctorCat V (A × B)} (q : Y ⟶ Z)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv M F X Z (gradedPostcomp ((Center.ofBraided V).obj M) t q) =
      gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv M F X Y t) (rightMap F q) :=
  gradedHomEquiv_naturality_right M F X q t

/-- The ordinary transpose is exactly the tensor-unit specialization. -/
theorem ordinaryIsUnitGrade (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (t : (leftFunctor F).obj X ⟶ Y) :
    gradedHomEquiv (𝟙_ V) F X Y t = homEquiv F X Y t := gradedHomEquiv_unit F X Y t

/-- The whole original external object satisfies the actual left triangle. -/
theorem leftTriangle (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B) :
    (leftFunctor F).map ((adjunction F).unit.app X) ≫
      (adjunction F).counit.app ((leftFunctor F).obj X) = 𝟙 ((leftFunctor F).obj X) :=
  adjunction_left_triangle F X

/-- The whole original parameterized end satisfies the actual right triangle. -/
theorem rightTriangle (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B)) :
    (adjunction F).unit.app ((rightFunctor F).obj Y) ≫
      (rightFunctor F).map ((adjunction F).counit.app Y) = 𝟙 ((rightFunctor F).obj Y) :=
  adjunction_right_triangle F Y

/-- The left triangle retains the full original unit and evaluation components. -/
theorem wholeLeftTriangle (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B) (a : A) (b : B) :
    (𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ component ((adjunction F).unit.app X) b) ≫
      MonoidalClosed.uncurry (projection F ((leftFunctor F).obj X) b a) =
        𝟙 (F.toEnrichedFunctor.obj a ⊗ X.toEnrichedFunctor.obj b) :=
  adjunction_left_triangle_component F X a b

/-- The right triangle retains the actual original weighted-end target map. -/
theorem wholeRightTriangle (F : EnrichedFunctorCat V A) (Y : EnrichedFunctorCat V (A × B)) (b : B) :
    component ((adjunction F).unit.app (rightObject F Y)) b ≫
      WeightedEndVariance.post F (restrictionMap (fixedRightPair (V := V) b) (counitMap F Y)) =
        𝟙 (mappingObject F Y b) := adjunction_right_triangle_component F Y b

/-- The complete ambient-presheaf forward component retains every coefficient. -/
theorem presheafForwardComponent (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (M : V)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      ((leftFunctor F).obj X).toEnrichedFunctor Y.toEnrichedFunctor) :
    (gradedPresheafIso F X Y).hom.app (Opposite.op M) (ULift.up t) =
      ULift.up (gradedHomEquiv M F X Y t) := gradedPresheafIso_hom_app F X Y M t

/-- The complete ambient-presheaf inverse component retains every coefficient. -/
theorem presheafInverseComponent (F : EnrichedFunctorCat V A) (X : EnrichedFunctorCat V B)
    (Y : EnrichedFunctorCat V (A × B)) (M : V)
    (h : GradedNatTrans ((Center.ofBraided V).obj M) X.toEnrichedFunctor
      (rightObject F Y).toEnrichedFunctor) :
    (gradedPresheafIso F X Y).inv.app (Opposite.op M) (ULift.up h) =
      ULift.up ((gradedHomEquiv M F X Y).symm h) := gradedPresheafIso_inv_app F X Y M h

section TensorSpecialization

variable {I : Type uA} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]

omit [HasProducts.{uA} V] [HasEqualizers V] in
/-- The actual tensor restriction has the original fixed-right-tensor slice. -/
theorem originalTensorSlice (d : EnrichedMonoidalCategoryData V I) (G : EnrichedFunctorCat V I) (b : I) :
    slice ((restriction d.tensorEnrichedFunctor).obj G) b =
      restrictionObject (Enriched.SphereOperator.fixedRightTensor d b) G :=
  slice_restriction_fixedRightTensor d G b

/-- The tensor specialization retains the actual original weighted end. -/
theorem originalTensorEnd (d : EnrichedMonoidalCategoryData V I) (F G : EnrichedFunctorCat V I) (b : I) :
    mappingObject F ((restriction d.tensorEnrichedFunctor).obj G) b =
      Enriched.weightedEnd F.toEnrichedFunctor
        ((Enriched.SphereOperator.fixedRightTensor d b).comp V G.toEnrichedFunctor) :=
  mappingObject_restriction_fixedRightTensor d F G b

end TensorSpecialization

section EmptyWeight

variable [EnrichedCategory V PEmpty.{uA + 1}]

-- The same actual construction admits an empty original weight carrier.
/-- The same genuine adjunction admits an empty original weight carrier. -/
def emptyWeightAdjunction (F : EnrichedFunctorCat V PEmpty.{uA + 1}) :
    leftFunctor (B := B) F ⊣ rightFunctor F := adjunction F

end EmptyWeight

end CategoryTheory.ExternalTensorMappingEndAdjunctionTests

open CategoryTheory.EnrichedFunctorCat.ExternalTensorMappingEndAdjunction

#check adjunction
#check gradedHomEquiv
#check gradedPresheafIso
#check sourceNatTrans

#print axioms fixedRightPair
#print axioms product_factorization
#print axioms EndEnrichment.enrichment
#print axioms rightObject
#print axioms homEquiv
#print axioms adjunction
#print axioms sourceNatTrans
#print axioms gradedHomEquiv
#print axioms gradedPresheafIso
#print axioms slice_restriction_fixedRightTensor

#lint only unusedArguments in
  MathlibExt.CategoryTheory.Enriched.ExternalTensorMappingEndAdjunction
