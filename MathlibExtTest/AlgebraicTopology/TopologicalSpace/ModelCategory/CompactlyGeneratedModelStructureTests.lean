/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedModelStructure
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Tests for the compactly generated model structure

These tests cover recognition, the selected model scope, fixed-cardinal
generation data, mixed universes, and fibrancy of every object.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra

#check CompactlyGenerated.generatedTrivialFibrationEq
#check CompactlyGenerated.generatedHornAcyclic
#check CompactlyGenerated.modelCategory
#check CompactlyGenerated.cofibrantGenerationData
#check CompactlyGenerated.modelCategory.instModelCategory

example : True := by
  fail_if_success
    have := (inferInstance :
      HomotopicalAlgebra.ModelCategory CompactlyGenerated.{0, 0})
  trivial

namespace CompactlyGenerated

example : realizedBoundaryInclusions.{u, v}.rlp =
    realizedHornInclusions.{u, v}.rlp ⊓
      weakHomotopyEquivalences.{u, v} :=
  generatedTrivialFibrationEq

example {X Y : CompactlyGenerated.{u, v}} {f : X ⟶ Y}
    (hf : realizedBoundaryInclusions.{u, v}.rlp f) :
    realizedHornInclusions.{u, v}.rlp f ∧
      weakHomotopyEquivalences.{u, v} f := by
  rw [generatedTrivialFibrationEq] at hf
  exact hf

example {X Y : CompactlyGenerated.{u, v}} {f : X ⟶ Y}
    (hf : realizedHornInclusions.{u, v}.rlp f ∧
      weakHomotopyEquivalences.{u, v} f) :
    realizedBoundaryInclusions.{u, v}.rlp f := by
  rw [generatedTrivialFibrationEq]
  exact hf

example {X Y : CompactlyGenerated.{u, v}} {f : X ⟶ Y}
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

open scoped SSet.modelCategoryQuillen CompactlyGenerated.modelCategory

#synth HomotopicalAlgebra.ModelCategory CompactlyGenerated.{0, 0}
#synth HomotopicalAlgebra.ModelCategory CompactlyGenerated.{1, 1}
#synth HomotopicalAlgebra.ModelCategory CompactlyGenerated.{0, 1}
#synth HomotopicalAlgebra.ModelCategory CompactlyGenerated.{1, 0}

example : weakEquivalences CompactlyGenerated.{u, v} =
    weakHomotopyEquivalences.{u, v} := rfl

example : cofibrations CompactlyGenerated.{u, v} =
    modelCofibrations.{u, v} := rfl

example : fibrations CompactlyGenerated.{u, v} =
    modelFibrations.{u, v} := rfl

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
    trivialFibrations CompactlyGenerated.{u, v} :=
  cofibrantGenerationData.{u, v}.I_rlp

example : cofibrantGenerationData.{u, v}.J.rlp =
    fibrations CompactlyGenerated.{u, v} :=
  cofibrantGenerationData.{u, v}.J_rlp

private theorem allObjectsFibrant
    (X : CompactlyGenerated.{u, v}) : IsFibrant X := by
  let P : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of PUnit.{v + 1}
  let hP : IsTerminal P :=
    IsTerminal.ofUniqueHom
      (fun Z => ConcreteCategory.ofHom
        (show C(Z, P) from
          ⟨fun _ => PUnit.unit, continuous_const⟩))
      (fun _ _ => by
        ext)
  let hTopP : IsTerminal
      (compactlyGeneratedToTop.{u, v}.obj P) :=
    TopCat.isTerminalPUnit
  let hTopTerminal : IsTerminal
      (compactlyGeneratedToTop.{u, v}.obj
        (⊤_ CompactlyGenerated.{u, v})) :=
    IsTerminal.ofIso hTopP
      (compactlyGeneratedToTop.{u, v}.mapIso
        (hP.uniqueUpToIso terminalIsTerminal))
  rw [HomotopicalAlgebra.isFibrant_iff]
  rw [HomotopicalAlgebra.fibration_iff]
  change TopCat.realizedHornInclusions.{v}.rlp
    (compactlyGeneratedToTop.{u, v}.map (terminal.from X))
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  rw [← SSet.modelCategoryQuillen.fibration_iff]
  rw [← HomotopicalAlgebra.isFibrant_iff_of_isTerminal _
    (hTopTerminal.isTerminalObj TopCat.toSSet _)]
  exact TopCat.toSSet_obj_kanComplex
    (compactlyGeneratedToTop.{u, v}.obj X)

example (X : CompactlyGenerated.{0, 0}) : IsFibrant X :=
  allObjectsFibrant X

example (X : CompactlyGenerated.{1, 1}) : IsFibrant X :=
  allObjectsFibrant X

example (X : CompactlyGenerated.{0, 1}) : IsFibrant X :=
  allObjectsFibrant X

example (X : CompactlyGenerated.{1, 0}) : IsFibrant X :=
  allObjectsFibrant X

end Selected

end CompactlyGenerated

example : True := by
  fail_if_success
    have := (inferInstance :
      HomotopicalAlgebra.ModelCategory CompactlyGenerated.{0, 0})
  trivial

/-! The rejected top-level implementation datum does not escape. -/

/-- error: Unknown constant `CompactlyGenerated.smithModelStructureData` -/
#guard_msgs (error) in
#check CompactlyGenerated.smithModelStructureData

#print axioms CompactlyGenerated.generatedTrivialFibrationEq
#print axioms CompactlyGenerated.generatedHornAcyclic
#print axioms CompactlyGenerated.modelCategory
#print axioms CompactlyGenerated.cofibrantGenerationData
#print axioms CompactlyGenerated.modelCategory.instModelCategory
