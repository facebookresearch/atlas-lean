/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningOriginalWeakMaps
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# The original native St/Un adjunction is Quillen in both actual models

The same native straightening preserves all original marked cofibrations
and every full original Cartesian weak map. These independently proved
properties construct the Quillen record for the ordinary original native
adjunction between the genuine Cartesian marked source model and genuine
coherent projective target model. Its original right adjoint consequently
preserves the full original model fibration and trivial-fibration classes.
No Quillen, filler, weak-image or auxiliary-class equality is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Actual preservation of original marked cofibrations and original full Cartesian weak maps proves preservation of
all trivial cofibrations by the same native straightening in BOTH actual models. -/
theorem nativeStraightening_original_preservesTrivialCofibrations (B : SSet.{u}) [Quasicategory B] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    PreservesTrivialCofibrations (nativeStraightening B) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro X Y f hf
  exact ⟨(cofibration_iff _).mp
      (nativeStraightening_preservesCofibrations B f ((cofibration_iff f).mpr hf.1)),
    (weakEquivalence_iff _).mp
      (nativeStraightening_original_weakEquivalence B f ((weakEquivalence_iff f).mpr hf.2))⟩

/-- The same ordinary original native St/Un adjunction is genuinely Quillen between BOTH actual original models over
every original quasicategory B, with no Kan-base or returned-outcome premise. -/
theorem nativeStraighteningOriginalQuillenAdjunction (B : SSet.{u}) [Quasicategory B] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    Adjunction.IsQuillenAdjunction (nativeStraighteningAdjunction B) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  refine
    { preservesCofibrations := ?_
      preservesTrivialCofibrations := nativeStraightening_original_preservesTrivialCofibrations B }
  intro X Y f hf
  exact (cofibration_iff _).mp
    (nativeStraightening_preservesCofibrations B f ((cofibration_iff f).mpr hf))

/-- The constructed original native Quillen adjunction preserves the FULL original model fibration class; it assumes
no equality with an auxiliary completed cell class and no diagram fibrancy. -/
theorem nativeUnstraightening_original_preservesFibrations (B : SSet.{u}) [Quasicategory B] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    PreservesFibrations (nativeUnstraightening B) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  let _ : Adjunction.IsQuillenAdjunction (nativeStraighteningAdjunction B) :=
    nativeStraighteningOriginalQuillenAdjunction B
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := nativeStraighteningAdjunction B)

/-- The same original native map of any actual coherent-model fibration is a fibration in the FULL genuine Cartesian
marked source model, without fibrancy of either endpoint diagram. -/
theorem nativeUnstraightening_original_modelFibration (B : SSet.{u}) [Quasicategory B]
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    Fibration q → Fibration ((nativeUnstraightening B).map q) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  exact (fibration_iff _).mpr
    (nativeUnstraightening_original_preservesFibrations B q ((fibration_iff q).mp hq))

/-- The internally constructed original Quillen record preserves all original full model trivial fibrations under
the same native Un functor in BOTH original model choices. -/
theorem nativeUnstraightening_original_preservesTrivialFibrations_quillen (B : SSet.{u}) [Quasicategory B] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    PreservesTrivialFibrations (nativeUnstraightening B) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  let _ : Adjunction.IsQuillenAdjunction (nativeStraighteningAdjunction B) :=
    nativeStraighteningOriginalQuillenAdjunction B
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := nativeStraighteningAdjunction B)

end SSet.Marked
