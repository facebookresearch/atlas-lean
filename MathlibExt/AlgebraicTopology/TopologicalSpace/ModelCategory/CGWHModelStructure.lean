/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClasses
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellSmallness
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedModelStructure
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import MathlibExt.Topology.Category.CGWH.Limits

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Model structure on compactly generated weak Hausdorff spaces

This file constructs the boundary-generated weak-homotopy model structure
on `CGWH`.  The model instance is opt-in through `CGWH.modelCategory`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra
open scoped CGWH.limits

namespace CGWH

/-- Boundary RLP maps are exactly horn RLP weak homotopy equivalences. -/
theorem generatedTrivialFibrationEq :
    realizedBoundaryInclusions.{u, v}.rlp =
      realizedHornInclusions.{u, v}.rlp ⊓
        weakHomotopyEquivalences.{u, v} := by
  rw [realizedBoundaryInclusions_rlp, realizedHornInclusions_rlp]
  change
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp.inverseImage
        cgwhToCompactlyGenerated.{u, v} =
      CompactlyGenerated.realizedHornInclusions.{u, v}.rlp.inverseImage
          cgwhToCompactlyGenerated.{u, v} ⊓
        CompactlyGenerated.weakHomotopyEquivalences.{u, v}.inverseImage
          cgwhToCompactlyGenerated.{u, v}
  rw [← MorphismProperty.inverseImage_inf]
  exact congrArg
    (fun P : MorphismProperty CompactlyGenerated.{u, v} ↦
      P.inverseImage cgwhToCompactlyGenerated.{u, v})
    CompactlyGenerated.generatedTrivialFibrationEq

/-- The generated horn left class consists of weak homotopy equivalences. -/
theorem generatedHornAcyclic :
    realizedHornInclusions.{u, v}.rlp.llp ≤
      weakHomotopyEquivalences.{u, v} := by
  rw [realizedHornInclusions_rlp_llp]
  intro X Y f hf
  exact CompactlyGenerated.generatedHornAcyclic _ hf

/-- The selected boundary-generated weak-homotopy model structure on CGWH. -/
@[instance_reducible]
noncomputable def modelCategory :
    HomotopicalAlgebra.ModelCategory CGWH.{u, v} := by
  letI : CategoryWithCofibrations CGWH.{u, v} :=
    ⟨modelCofibrations.{u, v}⟩
  letI : CategoryWithFibrations CGWH.{u, v} :=
    ⟨modelFibrations.{u, v}⟩
  letI : CategoryWithWeakEquivalences CGWH.{u, v} :=
    ⟨weakHomotopyEquivalences.{u, v}⟩
  let d : HomotopicalAlgebra.SmithModelStructureData.{v}
      (C := CGWH.{u, v})
      realizedBoundaryInclusions.{u, v}
      weakHomotopyEquivalences.{u, v} :=
    HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      realizedBoundaryInclusions.{u, v}
      realizedHornInclusions.{u, v}
      weakHomotopyEquivalences.{u, v}
      (by
        unfold weakHomotopyEquivalences
        unfold CompactlyGenerated.weakHomotopyEquivalences
        infer_instance)
      generatedTrivialFibrationEq
      generatedHornAcyclic
  exact d.modelCategory
    (by
      unfold weakHomotopyEquivalences
      unfold CompactlyGenerated.weakHomotopyEquivalences
      infer_instance)
    (by
      change modelCofibrations.{u, v} =
        realizedBoundaryInclusions.{u, v}.rlp.llp
      rw [realizedBoundaryInclusions_rlp_llp,
        CompactlyGenerated.realizedBoundaryInclusions_rlp_llp]
      rfl)
    (by
      change modelFibrations.{u, v} =
        realizedHornInclusions.{u, v}.rlp
      rw [realizedHornInclusions_rlp,
        CompactlyGenerated.realizedHornInclusions_rlp]
      rfl)
    rfl

namespace modelCategory

noncomputable scoped instance instModelCategory :
    HomotopicalAlgebra.ModelCategory CGWH.{u, v} :=
  CGWH.modelCategory

open scoped SSet.modelCategoryQuillen CGWH.modelCategory

/-- Every object is fibrant in the selected native CGWH model structure. -/
theorem allObjectsFibrant (X : CGWH.{u, v}) : IsFibrant X := by
  let P : CGWH.{u, v} := CGWH.of PUnit.{v + 1}
  let hP : IsTerminal P :=
    IsTerminal.ofUniqueHom
      (fun Z ↦ ConcreteCategory.ofHom
        (show C(Z, P) from
          ⟨fun _ ↦ PUnit.unit, continuous_const⟩))
      (fun _ _ ↦ by ext)
  let hTopP : IsTerminal (CGWH.cgwhToTop.{u, v}.obj P) :=
    TopCat.isTerminalPUnit
  let hTopTerminal : IsTerminal
      (CGWH.cgwhToTop.{u, v}.obj (⊤_ CGWH.{u, v})) :=
    IsTerminal.ofIso hTopP
      (CGWH.cgwhToTop.{u, v}.mapIso
        (hP.uniqueUpToIso terminalIsTerminal))
  rw [isFibrant_iff]
  rw [fibration_iff]
  change TopCat.realizedHornInclusions.{v}.rlp
    (CGWH.cgwhToTop.{u, v}.map (terminal.from X))
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  rw [← SSet.modelCategoryQuillen.fibration_iff]
  rw [← isFibrant_iff_of_isTerminal _
    (hTopTerminal.isTerminalObj TopCat.toSSet _)]
  exact TopCat.toSSet_obj_kanComplex (CGWH.cgwhToTop.{u, v}.obj X)

/-- A selected CGWH cofibration is exactly a native model cofibration. -/
theorem cofibration_iff {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    Cofibration f ↔ CGWH.modelCofibrations.{u, v} f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

/-- A selected CGWH fibration is exactly a native model fibration. -/
theorem fibration_iff {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    Fibration f ↔ CGWH.modelFibrations.{u, v} f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

/-- A selected CGWH weak equivalence is exactly a native weak homotopy
equivalence. -/
theorem weakEquivalence_iff {X Y : CGWH.{u, v}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ CGWH.weakHomotopyEquivalences.{u, v} f := by
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

end modelCategory

section

open scoped CGWH.modelCategory

/-- Fixed-cardinal cofibrant-generation data for the selected CGWH model. -/
noncomputable def cofibrantGenerationData :
    HomotopicalAlgebra.CofibrantGenerationData
      CGWH.{u, v} realizedGeneratorCardinal.{v} where
  I := realizedBoundaryInclusions.{u, v}
  J := realizedHornInclusions.{u, v}
  I_smallObject := inferInstance
  J_smallObject := inferInstance
  I_rlp := by
    calc
      realizedBoundaryInclusions.{u, v}.rlp =
          realizedHornInclusions.{u, v}.rlp ⊓
            weakHomotopyEquivalences.{u, v} :=
        generatedTrivialFibrationEq
      _ = modelFibrations.{u, v} ⊓
          weakHomotopyEquivalences.{u, v} := by
        rw [realizedHornInclusions_rlp,
          CompactlyGenerated.realizedHornInclusions_rlp]
        rfl
      _ = trivialFibrations CGWH.{u, v} := rfl
  J_rlp := by
    calc
      realizedHornInclusions.{u, v}.rlp = modelFibrations.{u, v} := by
        rw [realizedHornInclusions_rlp,
          CompactlyGenerated.realizedHornInclusions_rlp]
        rfl
      _ = fibrations CGWH.{u, v} := rfl

end

end CGWH
