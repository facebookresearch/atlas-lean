/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Topology.Category.CGWH.Products
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison

/-!
# Tests for the CGWH model structure

These tests cover generated recognition, selected class formulas, the sole
model scope for CGWH and pointed CGWH, fixed-cardinal generation data, mixed
universes, and all-object fibrancy.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra

#check CGWH.generatedTrivialFibrationEq
#check CGWH.generatedHornAcyclic
#check CGWH.modelCategory
#check CGWH.cofibrantGenerationData
#check CGWH.modelCategory.instModelCategory
#check CGWH.modelCategory.cofibration_iff
#check CGWH.modelCategory.fibration_iff
#check CGWH.modelCategory.weakEquivalence_iff
#check CGWH.modelCategory.allObjectsFibrant
#check PointedCGWH.modelCategory.allObjectsFibrant

#check @CGWH.modelCategory.cofibration_iff.{0, 0}
#check @CGWH.modelCategory.cofibration_iff.{1, 1}
#check @CGWH.modelCategory.cofibration_iff.{0, 1}
#check @CGWH.modelCategory.cofibration_iff.{1, 0}
#check @CGWH.modelCategory.fibration_iff.{0, 0}
#check @CGWH.modelCategory.fibration_iff.{1, 1}
#check @CGWH.modelCategory.fibration_iff.{0, 1}
#check @CGWH.modelCategory.fibration_iff.{1, 0}
#check @CGWH.modelCategory.weakEquivalence_iff.{0, 0}
#check @CGWH.modelCategory.weakEquivalence_iff.{1, 1}
#check @CGWH.modelCategory.weakEquivalence_iff.{0, 1}
#check @CGWH.modelCategory.weakEquivalence_iff.{1, 0}
#check @CGWH.modelCategory.allObjectsFibrant.{0, 0}
#check @CGWH.modelCategory.allObjectsFibrant.{1, 1}
#check @CGWH.modelCategory.allObjectsFibrant.{0, 1}
#check @CGWH.modelCategory.allObjectsFibrant.{1, 0}

example : True := by
  fail_if_success
    have := (inferInstance : HomotopicalAlgebra.ModelCategory CGWH.{0, 0})
  fail_if_success
    have := (inferInstance :
      HomotopicalAlgebra.ModelCategory PointedCGWH.{0, 0})
  fail_if_success
    have := (inferInstance : HasLimitsOfSize.{0, 0} CGWH.{0, 0})
  trivial

namespace CGWH

example : realizedBoundaryInclusions.{u, v}.rlp =
    realizedHornInclusions.{u, v}.rlp ⊓
      weakHomotopyEquivalences.{u, v} :=
  generatedTrivialFibrationEq

example {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : realizedBoundaryInclusions.{u, v}.rlp f) :
    realizedHornInclusions.{u, v}.rlp f ∧
      weakHomotopyEquivalences.{u, v} f := by
  rw [generatedTrivialFibrationEq] at hf
  exact hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : realizedHornInclusions.{u, v}.rlp f ∧
      weakHomotopyEquivalences.{u, v} f) :
    realizedBoundaryInclusions.{u, v}.rlp f := by
  rw [generatedTrivialFibrationEq]
  exact hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : realizedHornInclusions.{u, v}.rlp.llp f) :
    weakHomotopyEquivalences.{u, v} f :=
  generatedHornAcyclic _ hf

example : MorphismProperty.HasSmallObjectArgument.{v}
    realizedBoundaryInclusions.{u, v} := inferInstance

example : MorphismProperty.HasSmallObjectArgument.{v}
    realizedHornInclusions.{u, v} := inferInstance

example : MorphismProperty.IsCardinalForSmallObjectArgument.{v}
    realizedBoundaryInclusions.{u, v} realizedGeneratorCardinal.{v} :=
  inferInstance

example : MorphismProperty.IsCardinalForSmallObjectArgument.{v}
    realizedHornInclusions.{u, v} realizedGeneratorCardinal.{v} :=
  inferInstance

section Selected

open scoped SSet.modelCategoryQuillen CGWH.modelCategory

#synth HomotopicalAlgebra.ModelCategory CGWH.{0, 0}
#synth HomotopicalAlgebra.ModelCategory CGWH.{1, 1}
#synth HomotopicalAlgebra.ModelCategory CGWH.{0, 1}
#synth HomotopicalAlgebra.ModelCategory CGWH.{1, 0}
#synth HomotopicalAlgebra.ModelCategory PointedCGWH.{0, 0}
#synth HomotopicalAlgebra.ModelCategory PointedCGWH.{1, 1}
#synth HomotopicalAlgebra.ModelCategory PointedCGWH.{0, 1}
#synth HomotopicalAlgebra.ModelCategory PointedCGWH.{1, 0}

example : (inferInstance : ModelCategory CGWH.{u, v}) =
    CGWH.modelCategory := rfl

example : (inferInstance : ModelCategory PointedCGWH.{u, v}) =
    PointedCGWH.modelCategory := rfl

example : weakEquivalences CGWH.{u, v} =
    weakHomotopyEquivalences.{u, v} := rfl

example : cofibrations CGWH.{u, v} = modelCofibrations.{u, v} := rfl

example : fibrations CGWH.{u, v} = modelFibrations.{u, v} := rfl

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    Cofibration f ↔ modelCofibrations.{u, v} f :=
  CGWH.modelCategory.cofibration_iff f

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    Fibration f ↔ modelFibrations.{u, v} f :=
  CGWH.modelCategory.fibration_iff f

example {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ weakHomotopyEquivalences.{u, v} f :=
  CGWH.modelCategory.weakEquivalence_iff f

example {X Y : CGWH.{u, v}} {f : X ⟶ Y} (hf : Cofibration f) :
    modelCofibrations.{u, v} f :=
  (CGWH.modelCategory.cofibration_iff f).mp hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : modelCofibrations.{u, v} f) : Cofibration f :=
  (CGWH.modelCategory.cofibration_iff f).mpr hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y} (hf : Fibration f) :
    modelFibrations.{u, v} f :=
  (CGWH.modelCategory.fibration_iff f).mp hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : modelFibrations.{u, v} f) : Fibration f :=
  (CGWH.modelCategory.fibration_iff f).mpr hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y} (hf : WeakEquivalence f) :
    weakHomotopyEquivalences.{u, v} f :=
  (CGWH.modelCategory.weakEquivalence_iff f).mp hf

example {X Y : CGWH.{u, v}} {f : X ⟶ Y}
    (hf : weakHomotopyEquivalences.{u, v} f) : WeakEquivalence f :=
  (CGWH.modelCategory.weakEquivalence_iff f).mpr hf

example : cofibrantGenerationData.{u, v}.I =
    realizedBoundaryInclusions.{u, v} := rfl

example : cofibrantGenerationData.{u, v}.J =
    realizedHornInclusions.{u, v} := rfl

example : MorphismProperty.IsCardinalForSmallObjectArgument.{v}
    cofibrantGenerationData.{u, v}.I realizedGeneratorCardinal.{v} :=
  cofibrantGenerationData.{u, v}.I_smallObject

example : MorphismProperty.IsCardinalForSmallObjectArgument.{v}
    cofibrantGenerationData.{u, v}.J realizedGeneratorCardinal.{v} :=
  cofibrantGenerationData.{u, v}.J_smallObject

example : cofibrantGenerationData.{u, v}.I.rlp =
    trivialFibrations CGWH.{u, v} :=
  cofibrantGenerationData.{u, v}.I_rlp

example : cofibrantGenerationData.{u, v}.J.rlp =
    fibrations CGWH.{u, v} :=
  cofibrantGenerationData.{u, v}.J_rlp

example (X : CGWH.{u, v}) : IsFibrant X :=
  CGWH.modelCategory.allObjectsFibrant X

example (X : CGWH.{0, 0}) : IsFibrant X :=
  CGWH.modelCategory.allObjectsFibrant X

example (X : CGWH.{1, 1}) : IsFibrant X :=
  CGWH.modelCategory.allObjectsFibrant X

example (X : CGWH.{0, 1}) : IsFibrant X :=
  CGWH.modelCategory.allObjectsFibrant X

example (X : CGWH.{1, 0}) : IsFibrant X :=
  CGWH.modelCategory.allObjectsFibrant X

end Selected

section CombinedScopes

open scoped CGWH.limits CGWH.modelCategory

#synth HasLimitsOfSize.{v, v} CGWH.{u, v}
#synth HasFiniteLimits CGWH.{u, v}
#synth HomotopicalAlgebra.ModelCategory CGWH.{u, v}

example : (inferInstance : HasProducts.{v} CGWH.{u, v}) =
    CGWH.instHasProducts := rfl

example : (inferInstance : HasFiniteProducts CGWH.{u, v}) =
    CGWH.instHasFiniteProducts := rfl

attribute [-instance] HomotopicalAlgebra.ModelCategory.cm1a in
example : HasFiniteLimits CGWH.{u, v} := inferInstance

end CombinedScopes

end CGWH

section ModelSelectionDeletion

open scoped CGWH.modelCategory

attribute [-instance] CGWH.modelCategory.instModelCategory in
example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  trivial

end ModelSelectionDeletion

example : True := by
  fail_if_success
    have := (inferInstance : HomotopicalAlgebra.ModelCategory CGWH.{0, 0})
  fail_if_success
    have := (inferInstance : HasLimitsOfSize.{0, 0} CGWH.{0, 0})
  trivial

/-- error: Unknown constant `CGWH.smithModelStructureData` -/
#guard_msgs (error) in
#check CGWH.smithModelStructureData

#guard_msgs (error, substring := true) in
#check CGWH.adj_isQuillenEquivalence

#guard_msgs (error, substring := true) in
#check CGWH.instIsClosedSymmetricMonoidalModelCategory

#print axioms CGWH.generatedTrivialFibrationEq
#print axioms CGWH.generatedHornAcyclic
#print axioms CGWH.modelCategory
#print axioms CGWH.cofibrantGenerationData
#print axioms CGWH.modelCategory.instModelCategory
#print axioms CGWH.modelCategory.cofibration_iff
#print axioms CGWH.modelCategory.fibration_iff
#print axioms CGWH.modelCategory.weakEquivalence_iff
#print axioms CGWH.modelCategory.allObjectsFibrant
#print axioms PointedCGWH.modelCategory.allObjectsFibrant
