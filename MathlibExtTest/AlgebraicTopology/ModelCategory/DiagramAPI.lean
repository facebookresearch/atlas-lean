/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceKanExtensions
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.SourceKanExtensions
import MathlibExt.AlgebraicTopology.ModelCategory.ReedyEvaluationQuillen

/-!
# Diagram model API integration

The diagram model instances below are returned by the source constructors.
The tests retain the input generating families, whole natural transformations,
native Kan adjunctions, and original Reedy degree and boundary shapes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w uD vD uE vE uC vC uR

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.DiagramAPI

section FixedProjective

variable {D : Type uD} [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

-- The diagram generators are the free images of both original coefficient families.
example :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    (FunctorProjective.generationData (D := D) d).I =
        FunctorProjective.freeGenerators d d.I ∧
      (FunctorProjective.generationData (D := D) d).J =
        FunctorProjective.freeGenerators d d.J :=
  ⟨FunctorProjective.generationData_I d, FunctorProjective.generationData_J d⟩

example (x : D) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    (FunctorProjective.freeEvaluationAdjunction d x).IsQuillenAdjunction := by
  letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
  letI : ∀ a b : D, HasCoproductsOfShape (a ⟶ b) C := FunctorProjective.homCoproducts d
  exact FunctorProjective.evaluation_isQuillenAdjunction d x

-- A genuine original J-generator gives an actual trivial cofibration at every index.
example (x y : D) {A B : C} (f : A ⟶ B) (hf : d.J f) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    trivialCofibrations C (((FunctorProjective.freeFunctor d x).map f).app y) := by
  letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
  have h : trivialCofibrations (D ⥤ C) ((FunctorProjective.freeFunctor d x).map f) := by
    rw [← FunctorProjective.freeJ_left_eq d]
    exact (FunctorProjective.freeGenerators d d.J).le_llp_rlp _
      (FunctorProjective.freeGenerator_mem d d.J x f hf)
  exact FunctorProjective.trivialCofibrations_le_objectwise d _ h y

-- The full factor record factors every component of the original natural transformation.
example (f : Arrow (D ⥤ C)) (x : D) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    ((FunctorProjective.cofibrantFactorizationData d).i.app f).app x ≫
        ((FunctorProjective.cofibrantFactorizationData d).p.app f).app x = f.hom.app x :=
  FunctorProjective.cofibrantFactorizationData_fac_app d f x

-- Its middle map is the same fixed-rank small-object map on the complete square.
example {f g : Arrow (D ⥤ C)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ C) := FunctorProjective.modelCategory (J := D) d
    letI : (FunctorProjective.freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ :=
      FunctorProjective.freeI_eligible d
    (FunctorProjective.cofibrantFactorizationData d).Z.map φ =
      SmallObject.objMap (FunctorProjective.freeGenerators d d.I) κ φ :=
  FunctorProjective.cofibrantFactorizationData_map d φ

end FixedProjective

section FixedInjective

variable {D : Type uD} [Category.{vD} D]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (c : FunctorInjective.SourceConstruction.CoefficientData.{w} C)
  (s : Functor.EssentialIndexData.{w} D C)

local instance coefficientRegular : Fact c.cardinal.IsRegular := c.regular
local instance coefficientBottom : OrderBot c.cardinal.ord.ToType := c.bottom
local instance coefficientPresentable : IsCardinalLocallyPresentable C c.cardinal :=
  c.locallyPresentable
-- Uniformization retains the actual compact family and the internally produced Smith family.
example :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    let g := c.generationAndFactors s
    letI : Fact g.cardinal.IsRegular := g.regular
    letI : OrderBot g.cardinal.ord.ToType := g.bottom
    g.generationData.I =
        (FunctorInjective.boundedConstruction c.generation c.cardinal s).family.generators ∧
      g.generationData.J = (FunctorInjective.originalSmithData c.generation c.cardinal s).J := by
  letI : ModelCategory (D ⥤ C) := c.modelCategory s
  let g := c.generationAndFactors s
  letI : Fact g.cardinal.IsRegular := g.regular
  letI : OrderBot g.cardinal.ord.ToType := g.bottom
  exact ⟨g.generationData_I, g.generationData_J⟩

-- Each returned first factor is objectwise a cofibration and satisfies the whole right class.
example (f : Arrow (D ⥤ C)) (x : D) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    cofibrations C (((c.cofibrantFactorizationData s).i.app f).app x) ∧
      ((cofibrations C).functorCategory D).rlp ((c.cofibrantFactorizationData s).p.app f) :=
  ⟨(c.cofibrantFactorizationData s).hi f x, (c.cofibrantFactorizationData s).hp f⟩

example (f : Arrow (D ⥤ C)) (x : D) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    ((c.cofibrantFactorizationData s).i.app f).app x ≫
        ((c.cofibrantFactorizationData s).p.app f).app x = f.hom.app x :=
  NatTrans.congr_app (c.cofibrantFactorizationData s).fac_app x

-- The evaluation/cofree adjunction is left Quillen for the returned objectwise left classes.
example [∀ a b : D, HasProductsOfShape (a ⟶ b) C] (x : D) :
    letI : ModelCategory (D ⥤ C) := c.modelCategory s
    (evaluationAdjunctionLeft C x).IsQuillenAdjunction := by
  letI : ModelCategory (D ⥤ C) := c.modelCategory s
  constructor
  · intro F G f hf
    rw [(c.fiveClasses s).2.1] at hf
    exact hf x
  · intro F G f hf
    rw [(c.fiveClasses s).2.2.1] at hf
    exact hf x

end FixedInjective

section ProjectiveKan

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C] (u : D ⥤ E)

local instance projectiveSourceModel : ModelCategory (D ⥤ C) :=
  FunctorProjective.SourceConstruction.modelCategory (D := D) (C := C)
local instance projectiveTargetModel : ModelCategory (E ⥤ C) :=
  FunctorProjective.SourceConstruction.modelCategory (D := E) (C := C)

-- Kan existence and the Quillen result are constructed from coefficient/index sources.
example (F : D ⥤ C) : u.HasLeftKanExtension F :=
  FunctorProjective.SourceKanExtensions.hasLeftKanExtension u F

example : (FunctorProjective.SourceKanExtensions.adjunction (C := C) u).IsQuillenAdjunction :=
  FunctorProjective.SourceKanExtensions.isQuillen u

example {F G : D ⥤ C} (f : F ⟶ G) (hf : trivialCofibrations (D ⥤ C) f) :
    trivialCofibrations (E ⥤ C) ((FunctorProjective.SourceKanExtensions.lan u).map f) := by
  letI : (FunctorProjective.SourceKanExtensions.adjunction (C := C) u).IsQuillenAdjunction :=
    FunctorProjective.SourceKanExtensions.isQuillen u
  exact (inferInstance :
    (FunctorProjective.SourceKanExtensions.adjunction (C := C) u).IsQuillenAdjunction
  ).preservesTrivialCofibrations f hf

-- Equality of the native adjunction retains the unit, counit, and complete adjunct functions.
example :
    letI (F : D ⥤ C) : u.HasLeftKanExtension F :=
      FunctorProjective.SourceKanExtensions.hasLeftKanExtension u F
    FunctorProjective.SourceKanExtensions.adjunction (C := C) u = u.lanAdjunction C :=
  FunctorProjective.SourceKanExtensions.adjunction_eq_native u

end ProjectiveKan

section InjectiveKan

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [IsCombinatorialModelCategory.{w} C] (u : D ⥤ E)

local instance injectiveSourceModel : ModelCategory (D ⥤ C) :=
  FunctorInjective.SourceConstruction.modelCategory (D := D) (C := C)
local instance injectiveTargetModel : ModelCategory (E ⥤ C) :=
  FunctorInjective.SourceConstruction.modelCategory (D := E) (C := C)

example (F : D ⥤ C) : u.HasRightKanExtension F :=
  FunctorInjective.SourceKanExtensions.hasRightKanExtension u F

example : (FunctorInjective.SourceKanExtensions.adjunction (C := C) u).IsQuillenAdjunction :=
  FunctorInjective.SourceKanExtensions.isQuillen u

-- Restriction is the left adjoint here; the original map is evaluated at the original u.obj x.
example {F G : E ⥤ C} (f : F ⟶ G) (hf : trivialCofibrations (E ⥤ C) f) (x : D) :
    trivialCofibrations C (f.app (u.obj x)) := by
  have h := (FunctorInjective.SourceConstruction.fiveClasses (D := E) (C := C)).2.2.1
  rw [h] at hf
  exact hf (u.obj x)

example :
    letI (F : D ⥤ C) : u.HasRightKanExtension F :=
      FunctorInjective.SourceKanExtensions.hasRightKanExtension u F
    FunctorInjective.SourceKanExtensions.adjunction (C := C) u = u.ranAdjunction C :=
  FunctorInjective.SourceKanExtensions.adjunction_eq_native u

end InjectiveKan

section Reedy

variable {D : Type uD} [Category.{vD} D]
  {R : Type uR} [LinearOrder R] [WellFoundedLT R] (r : CategoryTheory.ReedyStructure D R)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ x, HasLimitsOfShape (r.Matching x) C]
  [∀ x, HasColimitsOfShape (r.Latching x) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

-- Original relative latching maps, rather than an assumed diagram cofibration, are the inputs.
example {F G : D ⥤ C} (f : F ⟶ G)
    (hf : ∀ x : D, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f x)) (x : D) :
    letI : ModelCategory (D ⥤ C) := ReedyModel.modelCategory r Fc Ff
    cofibrations C (f.app x) :=
  (ReedyModel.evaluation_preserves_classes r Fc Ff x).1 f hf

example {F G : D ⥤ C} (f : F ⟶ G)
    (hf : ∀ x : D, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f x)) (x : D) :
    letI : ModelCategory (D ⥤ C) := ReedyModel.modelCategory r Fc Ff
    fibrations C (f.app x) :=
  (ReedyModel.evaluation_preserves_classes r Fc Ff x).2.2.1 f hf

example (f : Arrow (D ⥤ C)) (x : D) :
    letI : ModelCategory (D ⥤ C) := ReedyModel.modelCategory r Fc Ff
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app f).app x ≫
        ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app f).app x = f.hom.app x :=
  NatTrans.congr_app (ReedyModel.cofibrantFactorizationData r Fc Ff).fac_app x

example [∀ a b : D, HasProductsOfShape (a ⟶ b) C] (x : D) :
    letI : ModelCategory (D ⥤ C) := ReedyModel.modelCategory r Fc Ff
    (evaluationAdjunctionLeft C x).IsQuillenAdjunction :=
  ReedyModel.evaluationAdjunctionLeft_isQuillen r Fc Ff x

example [∀ a b : D, HasCoproductsOfShape (a ⟶ b) C] (x : D) :
    letI : ModelCategory (D ⥤ C) := ReedyModel.modelCategory r Fc Ff
    (evaluationAdjunctionRight C x).IsQuillenAdjunction :=
  ReedyModel.evaluationAdjunctionRight_isQuillen r Fc Ff x

end Reedy

section GeneratedReedy

variable {D : Type uD} [Category.{vD} D]
  {R : Type uR} [LinearOrder R] [WellFoundedLT R] (r : CategoryTheory.ReedyStructure D R)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ x, HasLimitsOfShape (r.Matching x) C]
  [∀ x, HasColimitsOfShape (r.Latching x) C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

-- The input base generating families supply the factors used by the returned Reedy model.
example [∀ a b : D, HasCoproductsOfShape (a ⟶ b) C] (x : D) :
    letI : ModelCategory (D ⥤ C) := ReedyModel.generatedModelCategory r d
    (evaluationAdjunctionRight C x).IsQuillenAdjunction :=
  ReedyModel.generatedEvaluationAdjunctionRight_isQuillen r d x

end GeneratedReedy

end MathlibExtTest.AlgebraicTopology.ModelCategory.DiagramAPI
