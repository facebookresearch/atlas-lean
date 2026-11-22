/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ModelCategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningOriginalQuillen
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Marked models and the native straightening Quillen adjunction

The named Cartesian and cocartesian models retain their intrinsic classes and
quasicategory base hypothesis. The coherent diagram model and native categorical
adjunction use the actual opposite coherent realization of any simplicial base.
Quillen preservation uses the constructed models, with no supplied model or
Quillen certificate. Negative inference guards retain the base hypothesis and
the boundary between a Quillen adjunction and a Quillen equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open SSet.Marked CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory
  coefficientMarkedModelCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.MarkedModelAdjunctionAPI

section ArbitraryBase

variable (B : SSet.{u})

example : ModelCategory (EnrichedDiagram (realization B)ᵒᵖ) :=
  coherentDiagramModelCategory B

example :
    let _ := coherentDiagramModelCategory B
    weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ) = coherentDiagramWeakEquivalences B :=
  coherentDiagramModel_weakEquivalences B

example :
    let _ := coherentDiagramModelCategory B
    cofibrations (EnrichedDiagram (realization B)ᵒᵖ) = (coherentDiagramGeneratingMonos B).rlp.llp :=
  coherentDiagramModel_cofibrations B

example :
    let _ := coherentDiagramModelCategory B
    fibrations (EnrichedDiagram (realization B)ᵒᵖ) =
      EvaluationTransfer.evaluationProperty
        (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c) (fibrations SSet.Marked.{u}) :=
  coherentDiagramModel_fibrations B

example : nativeStraightening B ⊣ nativeUnstraightening B :=
  nativeStraighteningAdjunction B

example (X : Over (max B)) :
    (nativeStraightening B).map ((nativeStraighteningAdjunction B).unit.app X) ≫
      (nativeStraighteningAdjunction B).counit.app ((nativeStraightening B).obj X) = 𝟙 _ :=
  nativeStraightening_left_triangle B X

example (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeStraighteningAdjunction B).unit.app ((nativeUnstraightening B).obj F) ≫
      (nativeUnstraightening B).map ((nativeStraighteningAdjunction B).counit.app F) = 𝟙 _ :=
  nativeStraightening_right_triangle B F

end ArbitraryBase

example (Z : SSet.Marked.{u}) (X : Over Z) :
    let _ := markedCofibrationStructure Z
    IsCofibrant X :=
  markedCofibrationStructure_all_cofibrant Z X

section QuasicategoryBase

variable (B : SSet.{u}) [SSet.Quasicategory B]

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    ModelCategory (Over (max B)) :=
  cartesianMarkedModelCategory B

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cocartesianMarkedFibrationStructure B
    let _ := cocartesianMarkedWeakStructure B
    ModelCategory (Over (max B)) :=
  cocartesianMarkedModelCategory B

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    cofibrations (Over (max B)) = monomorphisms (Over (max B)) ∧
      fibrations (Over (max B)) = cartesianTestingFibrations B ∧
      weakEquivalences (Over (max B)) = cartesianWeakEquivalences B :=
  cartesianMarkedModel_classes B

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cocartesianMarkedFibrationStructure B
    let _ := cocartesianMarkedWeakStructure B
    cofibrations (Over (max B)) = monomorphisms (Over (max B)) ∧
      fibrations (Over (max B)) = cocartesianTestingFibrations B ∧
      weakEquivalences (Over (max B)) = cocartesianWeakEquivalences B :=
  cocartesianMarkedModel_classes B

example (Y : Over (max B)) :
    let _ := cartesianMarkedFibrationStructure B
    IsFibrant Y ↔ cartesianObjects B Y :=
  cartesianMarkedModel_fibrant_iff B Y

example (Y : Over (max B)) :
    let _ := cocartesianMarkedFibrationStructure B
    IsFibrant Y ↔ cocartesianObjects B Y :=
  cocartesianMarkedModel_fibrant_iff B Y

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    Adjunction.IsQuillenAdjunction (nativeStraighteningAdjunction B) :=
  nativeStraighteningOriginalQuillenAdjunction B

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    PreservesCofibrations (nativeStraightening B) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  exact (nativeStraighteningOriginalQuillenAdjunction B).preservesCofibrations

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    PreservesTrivialCofibrations (nativeStraightening B) :=
  nativeStraightening_original_preservesTrivialCofibrations B

example {X Y : Over (max B)} (f : X ⟶ Y) (hf : cartesianWeakEquivalences B f) :
    let _ := coherentDiagramModelCategory B
    WeakEquivalence ((nativeStraightening B).map f) :=
  nativeStraightening_original_cartesianWeak B f hf

example {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    Fibration q → Fibration ((nativeUnstraightening B).map q) :=
  nativeUnstraightening_original_modelFibration B q

example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    PreservesTrivialFibrations (nativeUnstraightening B) :=
  nativeUnstraightening_original_preservesTrivialFibrations_quillen B

-- The constructed Quillen record does not supply a general Quillen-equivalence instance.
example :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    True := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  let _ : Adjunction.IsQuillenAdjunction (nativeStraighteningAdjunction B) :=
    nativeStraighteningOriginalQuillenAdjunction B
  fail_if_success
    have h : Adjunction.IsQuillenEquivalence (nativeStraighteningAdjunction B) := by
      infer_instance
  trivial

end QuasicategoryBase

-- The two fixed-base models and the Quillen theorem retain their base condition.
example (B : SSet.{u}) : True := by
  fail_if_success
    have h := cartesianMarkedModelCategory B
  fail_if_success
    have h := cocartesianMarkedModelCategory B
  fail_if_success
    have h := nativeStraighteningOriginalQuillenAdjunction B
  trivial

end MathlibExtTest.AlgebraicTopology.ModelCategory.MarkedModelAdjunctionAPI
