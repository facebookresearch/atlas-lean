/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedDiagramConstructions
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Original projective colimits and their full derived adjunction

The actual ordinary projective model is constructed from the supplied
coefficient generation data. Its free I/J families and original cardinal
are retained. The ordinary colimit/constant adjunction is Quillen because
both original right classes are objectwise.

The generic derived-diagram constructions are specialized to that same
original generation datum, with its complete Q/R functors and maps.

The whole original projective Q diagram, followed by the actual colimit,
is homotopical on every objectwise weak arrow. Its comparison to the
ordinary colimit is weak at genuinely projectively cofibrant diagrams.
The same comparison gives its natural Ho isomorphism on those diagrams.

The full chosen derived adjunction retains the original diagram Q and
coefficient R, both universal comparison transformations, all four
derived conditions and the actual Hom/unit/counit data. No diagram model
or colimit weakness is supplied as an input. Identifying an arbitrary
ordinal cofibration chain as projectively cofibrant, cofinality and
simplicial diagonal/realization equivalences remain separate source work.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w uJ vJ uC vC
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopicalAlgebra.OriginalProjectiveDerivedColimits

variable {J : Type uJ} [Category.{vJ} J] [Small.{w} J] [LocallySmall.{w} J]
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

include d in
private theorem indexHasColimits : HasColimitsOfShape J C := by
  let : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact hasColimitsOfShape_of_essentiallySmall J C

/-- The actual ordinary colimit/constant adjunction is Quillen for the SAME original projective model. -/
theorem colimit_isQuillen :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.colimit_isQuillen
    (FunctorProjective.fibrations_eq d) (FunctorProjective.trivialFibrations_eq d)

/-- The actual original projective Q diagram at the supplied cardinal is followed by its ordinary colimit. -/
def homotopyColimit : (J ⥤ C) ⥤ C := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.homotopyColimit
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d))

/-- Every original diagram object is kept as a whole before its actual original Q colimit is taken. -/
theorem homotopyColimit_obj (F : J ⥤ C) :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    (homotopyColimit (J := J) d).obj F =
      colimit ((GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := J) d)).obj F) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.homotopyColimit_obj
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d)) F

/-- Every full original diagram map retains the SAME projective Q map and its actual colimit map. -/
theorem homotopyColimit_map {F G : J ⥤ C} (f : F ⟶ G) :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    (homotopyColimit (J := J) d).map f =
      colim.map ((GeneratedFunctorialReplacements.Q (FunctorProjective.generationData (D := J) d)).map f) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.homotopyColimit_map
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d)) f

/-- The complete original projective Q counit gives the whole canonical homotopy-colimit comparison. -/
def comparison :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    homotopyColimit (J := J) d ⟶ (colim : (J ⥤ C) ⥤ C) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.colimitComparison
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d))

/-- Each full comparison component is the actual colimit map of the SAME original projective Q counit. -/
theorem comparison_app (F : J ⥤ C) :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    (comparison (J := J) d).app F =
      colim.map ((GeneratedFunctorialReplacements.counit
        (FunctorProjective.generationData (D := J) d)).app F) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.colimitComparison_app
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d)) F

/-- Every objectwise original weak map gives a weak homotopy-colimit map through the actual projective Q and Quillen
colimit. -/
theorem homotopyColimit_map_weak {F G : J ⥤ C} (f : F ⟶ G)
    (hf : (weakEquivalences C).functorCategory J f) :
    weakEquivalences C ((homotopyColimit (J := J) d).map f) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  exact DerivedDiagramConstructions.homotopyColimit_map_objectwise_weak
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d))
    (FunctorProjective.fibrations_eq d) (FunctorProjective.trivialFibrations_eq d)
    (FunctorProjective.weakEquivalences_eq d) f hf

/-- At an ACTUALLY projectively cofibrant original diagram, the original comparison to its colimit is weak. -/
theorem comparison_weak_of_cofibrant (F : J ⥤ C)
    (hF : letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
      IsCofibrant F) :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    weakEquivalences C ((comparison (J := J) d).app F) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : IsCofibrant F := hF
  exact DerivedDiagramConstructions.colimitComparison_weak
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d))
    (FunctorProjective.fibrations_eq d) (FunctorProjective.trivialFibrations_eq d) F

/-- The entire actual original comparison is a Ho isomorphism on that SAME projectively cofibrant diagram. -/
def comparisonHoIso (F : J ⥤ C)
    (hF : letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
      IsCofibrant F) :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    (toHomotopyCategory C).obj ((homotopyColimit (J := J) d).obj F) ≅
      (toHomotopyCategory C).obj (colimit F) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : IsIso ((toHomotopyCategory C).map ((comparison (J := J) d).app F)) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp (comparison_weak_of_cofibrant d F hF)
  exact asIso ((toHomotopyCategory C).map ((comparison (J := J) d).app F))

/-- The complete original comparison Iso keeps every full map between projectively cofibrant diagrams. -/
theorem comparisonHoIso_naturality {F G : J ⥤ C} (f : F ⟶ G)
    (hF : letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
      IsCofibrant F)
    (hG : letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
      IsCofibrant G) :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    (toHomotopyCategory C).map ((homotopyColimit (J := J) d).map f) ≫
        (comparisonHoIso d G hG).hom =
      (comparisonHoIso d F hF).hom ≫ (toHomotopyCategory C).map (colim.map f) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  change (toHomotopyCategory C).map ((homotopyColimit (J := J) d).map f) ≫
      (toHomotopyCategory C).map ((comparison (J := J) d).app G) =
    (toHomotopyCategory C).map ((comparison (J := J) d).app F) ≫ (toHomotopyCategory C).map (colim.map f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (toHomotopyCategory C).congr_map ((comparison (J := J) d).naturality f)

/-- The actual chosen derived colimit/constant adjunction retains ALL four derived properties and the original diagram
Q/coefficient R. -/
def derivedAdjunctionData :
    letI : HasColimitsOfShape J C := indexHasColimits (J := J) d
    letI : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
    QuillenDerivedAdjunctionData (colimConstAdj (J := J) (C := C)) := by
  let : HasColimitsOfShape J C := indexHasColimits (J := J) d
  let : ModelCategory (J ⥤ C) := FunctorProjective.modelCategory (J := J) d
  let : (colimConstAdj (J := J) (C := C)).IsQuillenAdjunction := colimit_isQuillen (J := J) d
  exact DerivedAdjunctionCoherence.chosenDerivedAdjunctionData (colimConstAdj (J := J) (C := C))
    (GeneratedFunctorialReplacements.fromGeneration (FunctorProjective.generationData (D := J) d))
    (GeneratedFunctorialReplacements.fromGeneration d)

end HomotopicalAlgebra.OriginalProjectiveDerivedColimits
