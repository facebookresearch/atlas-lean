/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.SimplexCategory.ReedyComparison
public import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped Simplicial

namespace ReedyCanonicalClients

section ImportScope

/-- Importing the Reedy API retains Mathlib's existing natural-number successor dictionary. -/
theorem nat_succ_dictionary :
    (inferInstance : SuccOrder ℕ) = Nat.instSuccOrder := rfl

/-- Importing the Reedy API retains Mathlib's existing successor dictionary
after adjoining bottom. -/
theorem withBot_nat_succ_dictionary :
    (inferInstance : SuccOrder (WithBot ℕ)) = WithBot.instSuccOrder := rfl

/-- Importing the Reedy API retains the computable natural-number successor. -/
theorem nat_succ_zero : Order.succ (0 : ℕ) = 1 := rfl

/-- Importing the Reedy API retains the computable successor of the original zero in `WithBot ℕ`. -/
theorem withBot_nat_succ_zero : Order.succ (0 : WithBot ℕ) = (1 : WithBot ℕ) := rfl

/-- Importing the Reedy API retains the successor of the adjoined bottom. -/
theorem withBot_nat_succ_bot : Order.succ (⊥ : WithBot ℕ) = (0 : WithBot ℕ) := rfl

end ImportScope

section General

open scoped CategoryTheory.ReedyStructure


/-- The public core extensionality rule reconstructs the whole original Reedy record
from its data. -/
theorem core_ext {J : Type uJ} [Category.{vJ} J]
    {D : Type uD} [LinearOrder D] [WellFoundedLT D]
    (r s : CategoryTheory.ReedyStructure J D)
    (hdegree : r.degree = s.degree) (hdirect : r.direct = s.direct)
    (hinverse : r.inverse = s.inverse) : r = s := by
  ext1
  · exact hdegree
  · exact hdirect
  · exact hinverse


variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D]
  (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- Native degrees reflect the complete original order, with no original bottom or successor assumption. -/
theorem native_degree_order {i j : J} :
    r.toCanonical.deg i < r.toCanonical.deg j ↔ r.degree i < r.degree j :=
  r.toCanonical_degree_lt

/-- The complete native source factor record retains its original object and both maps. -/
theorem native_source_factor {i j : J} (f : i ⟶ j) :
    r.toCanonical.mapFactorizationData f = r.factor f :=
  r.toCanonical_mapFactorizationData f

/-- The native construction and original construction have the same entire model dictionary. -/
theorem native_model :
    r.toCanonical.modelCategoryWithOriginalDegree r.degree r.native_degree r.factor Fc Ff =
      ReedyModel.modelCategory r Fc Ff :=
  ReedyModel.modelCategory_eq_native r Fc Ff

/-- The native construction retains the whole original cofibration factory record. -/
theorem native_cofibrant_factory :
    r.toCanonical.cofibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff = ReedyModel.cofibrantFactorizationData r Fc Ff :=
  ReedyModel.cofibrantFactorizationData_eq_native r Fc Ff

/-- The native construction retains the whole original fibration factory record. -/
theorem native_fibrant_factory :
    r.toCanonical.fibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff = ReedyModel.fibrantFactorizationData r Fc Ff :=
  ReedyModel.fibrantFactorizationData_eq_native r Fc Ff

/-- Every original Arrow square acts by the same whole native cofibration middle-functor map. -/
theorem native_cofibrant_map {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (r.toCanonical.cofibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff).Z.map s =
      (CategoryTheory.ReedyStructure.FunctorialConstruction.middle r Fc).map s := rfl

/-- Every original Arrow square acts by the same whole native fibration middle-functor map. -/
theorem native_fibrant_map {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (r.toCanonical.fibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff).Z.map s =
      (CategoryTheory.ReedyStructure.FunctorialConstruction.middle r Ff).map s := rfl

/-- The native cofibration factory retains the original complete left natural transformation. -/
theorem native_cofibrant_left :
    (r.toCanonical.cofibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff).i =
      CategoryTheory.ReedyStructure.FunctorialConstruction.left r Fc := rfl

/-- The native fibration factory retains the original complete right natural transformation. -/
theorem native_fibrant_right :
    (r.toCanonical.fibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff).p =
      CategoryTheory.ReedyStructure.FunctorialConstruction.right r Ff := rfl

end General

section Simplex

open SimplexCategory.ReedyCanonicalComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]

/-- The original simplicial latching source is the actual established proper-epi index. -/
def canonical_latching_index (n : ℕ) :
    SimplexCategory.reedyOp.Latching (Opposite.op ⦋n⦌) ≌ SimplicialObject.latchingIndex n :=
  SimplicialObject.latchingEquivalence n

/-- The original simplicial matching source is the actual established proper-mono index. -/
def canonical_matching_index (n : ℕ) :
    SimplexCategory.reedyOp.Matching (Opposite.op ⦋n⦌) ≌ SimplicialObject.matchingIndex n :=
  SimplicialObject.matchingEquivalence n

/-- Both complete latching Arrow endpoints and the entire relative map agree. -/
def canonical_latching_arrow {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedyOp f (Opposite.op ⦋n⦌)) ≅
      Arrow.mk (SimplicialObject.relativeLatchingMap f n) :=
  SimplicialObject.latchingCornerArrowIso f n

/-- Both complete matching Arrow endpoints and the entire relative map agree. -/
def canonical_matching_arrow {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ) :
    Arrow.mk (CategoryTheory.ReedyStructure.matchingCorner SimplexCategory.reedyOp f (Opposite.op ⦋n⦌)) ≅
      Arrow.mk (SimplicialObject.relativeMatchingMap f n) :=
  SimplicialObject.matchingCornerArrowIso f n

/-- The cofibration source predicate is exactly the established full relative-latching predicate. -/
theorem canonical_cofibration_class :
    CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C) =
      SimplicialObject.reedyLeft (cofibrations C) :=
  (SimplicialObject.reedyLeft_eq_latchingClass (cofibrations C)).symm

/-- The fibration source predicate is exactly the established full relative-matching predicate. -/
theorem canonical_fibration_class :
    CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedyOp (fibrations C) =
      SimplicialObject.reedyRight (fibrations C) :=
  (SimplicialObject.reedyRight_eq_matchingClass (fibrations C)).symm

end Simplex

section CompleteModel

open SimplexCategory.ReedyCanonicalComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The entire original general simplex dictionary is the existing canonical dictionary. -/
theorem full_model_dictionary :
    ReedyModel.modelCategory SimplexCategory.reedyOp Fc Ff = SimplicialObject.reedyModelCategory :=
  modelCategory_eq_canonical Fc Ff

/-- All five existing canonical classes are the full original source classes. -/
theorem full_five_classes :
    letI := SimplicialObject.reedyModelCategory (C := C)
    weakEquivalences (SimplicialObject C) = (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ ∧
    cofibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (cofibrations C) ∧
    fibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedyOp (fibrations C) ∧
    trivialCofibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.latchingClass SimplexCategory.reedyOp (trivialCofibrations C) ∧
    trivialFibrations (SimplicialObject C) =
      CategoryTheory.ReedyStructure.matchingClass SimplexCategory.reedyOp (trivialFibrations C) :=
  ⟨canonical_weakEquivalences_eq, canonical_cofibrations_eq, canonical_fibrations_eq,
    canonical_trivialCofibrations_eq, canonical_trivialFibrations_eq⟩

/-- Every Arrow square keeps the whole originally supplied canonical cofibration middle map. -/
theorem full_cofibrant_square {a b : Arrow (SimplicialObject C)} (t : a ⟶ b) :
    (canonicalCofibrantFactorizationData Fc Ff).Z.map t =
      (ReedyModel.cofibrantFactorizationData SimplexCategory.reedyOp Fc Ff).Z.map t := rfl

/-- Every Arrow square keeps the whole originally supplied canonical fibration middle map. -/
theorem full_fibrant_square {a b : Arrow (SimplicialObject C)} (t : a ⟶ b) :
    (canonicalFibrantFactorizationData Fc Ff).Z.map t =
      (ReedyModel.fibrantFactorizationData SimplexCategory.reedyOp Fc Ff).Z.map t := rfl

/-- The actual chosen canonical cofibration factor retains both entire original natural transformations. -/
theorem full_cofibrant_natural_maps :
    (canonicalCofibrantFactorizationData Fc Ff).i =
      (ReedyModel.cofibrantFactorizationData SimplexCategory.reedyOp Fc Ff).i ∧
    (canonicalCofibrantFactorizationData Fc Ff).p =
      (ReedyModel.cofibrantFactorizationData SimplexCategory.reedyOp Fc Ff).p := ⟨rfl, rfl⟩

/-- The actual chosen canonical fibration factor retains both entire original natural transformations. -/
theorem full_fibrant_natural_maps :
    (canonicalFibrantFactorizationData Fc Ff).i =
      (ReedyModel.fibrantFactorizationData SimplexCategory.reedyOp Fc Ff).i ∧
    (canonicalFibrantFactorizationData Fc Ff).p =
      (ReedyModel.fibrantFactorizationData SimplexCategory.reedyOp Fc Ff).p := ⟨rfl, rfl⟩

end CompleteModel

section Generated

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The actual generated framing model uses the established canonical simplicial model. -/
theorem generated_selected_dictionary :
    GeneratedFramingModels.simplicialModel d = SimplicialObject.reedyModelCategory :=
  GeneratedFramingModels.simplicialModel_eq_canonical d

/-- The selected generated cofibration factory retains the entire original middle functor. -/
theorem generated_cofibrant_middle :
    (GeneratedFramingModels.simplicialCofibrantFactorizationData d).Z =
      (ReedyModel.generatedCofibrantFactorizationData SimplexCategory.reedyOp d).Z := rfl

/-- The selected generated fibration factory retains the entire original middle functor. -/
theorem generated_fibrant_middle :
    (GeneratedFramingModels.simplicialFibrantFactorizationData d).Z =
      (ReedyModel.generatedFibrantFactorizationData SimplexCategory.reedyOp d).Z := rfl

/-- The selected generated factories retain all four entire original natural factor maps. -/
theorem generated_natural_maps :
    (GeneratedFramingModels.simplicialCofibrantFactorizationData d).i =
      (ReedyModel.generatedCofibrantFactorizationData SimplexCategory.reedyOp d).i ∧
    (GeneratedFramingModels.simplicialCofibrantFactorizationData d).p =
      (ReedyModel.generatedCofibrantFactorizationData SimplexCategory.reedyOp d).p ∧
    (GeneratedFramingModels.simplicialFibrantFactorizationData d).i =
      (ReedyModel.generatedFibrantFactorizationData SimplexCategory.reedyOp d).i ∧
    (GeneratedFramingModels.simplicialFibrantFactorizationData d).p =
      (ReedyModel.generatedFibrantFactorizationData SimplexCategory.reedyOp d).p := ⟨rfl, rfl, rfl, rfl⟩

end Generated

end ReedyCanonicalClients

#print axioms ReedyCanonicalClients.native_model
#print axioms ReedyCanonicalClients.native_cofibrant_factory
#print axioms ReedyCanonicalClients.native_fibrant_factory
#print axioms ReedyCanonicalClients.native_cofibrant_map
#print axioms ReedyCanonicalClients.native_fibrant_map
#print axioms ReedyCanonicalClients.canonical_latching_arrow
#print axioms ReedyCanonicalClients.canonical_matching_arrow
#print axioms ReedyCanonicalClients.canonical_cofibration_class
#print axioms ReedyCanonicalClients.canonical_fibration_class

#print axioms ReedyCanonicalClients.full_model_dictionary
#print axioms ReedyCanonicalClients.full_five_classes
#print axioms ReedyCanonicalClients.full_cofibrant_square
#print axioms ReedyCanonicalClients.full_fibrant_square
#print axioms ReedyCanonicalClients.generated_selected_dictionary
#print axioms ReedyCanonicalClients.generated_cofibrant_middle
#print axioms ReedyCanonicalClients.generated_fibrant_middle
#print axioms ReedyCanonicalClients.generated_natural_maps

#lint only unusedArguments in ReedyCanonicalClients
