/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedModelClasses
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedSmallObject
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCellWeakHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityFromSSet

/-!
# Model structure on compactly generated spaces

This file constructs the boundary-generated model structure on compactly
generated spaces and packages its fixed-cardinal generators. The model
instance is opt-in through `CompactlyGenerated.modelCategory`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra

namespace CompactlyGenerated

/-- Boundary RLP maps are exactly horn RLP weak homotopy equivalences. -/
theorem generatedTrivialFibrationEq :
    realizedBoundaryInclusions.{u, v}.rlp =
      realizedHornInclusions.{u, v}.rlp ⊓
        weakHomotopyEquivalences.{u, v} := by
  rw [realizedBoundaryInclusions_rlp, realizedHornInclusions_rlp]
  change
    TopCat.realizedBoundaryInclusions.{v}.rlp.inverseImage
        compactlyGeneratedToTop.{u, v} =
      TopCat.realizedHornInclusions.{v}.rlp.inverseImage
          compactlyGeneratedToTop.{u, v} ⊓
        TopCat.weakHomotopyEquivalences.{v}.inverseImage
          compactlyGeneratedToTop.{u, v}
  rw [← MorphismProperty.inverseImage_inf]
  exact congrArg
    (fun P : MorphismProperty TopCat.{v} =>
      P.inverseImage compactlyGeneratedToTop.{u, v})
    (TopCat.hornRLP_inf_W_eq_boundaryRLP_of_sSet
      TopCat.horn_llp_le_weakHomotopyEquivalences
      SSet.KanComplex.I_rlp_to_W_kanRestricted
      SSet.modelCategoryQuillen.J_rlp_inf_W_le_I_rlp).symm

/-- The generated horn left class consists of weak homotopy equivalences. -/
theorem generatedHornAcyclic :
    realizedHornInclusions.{u, v}.rlp.llp ≤
      weakHomotopyEquivalences.{u, v} := by
  rw [realizedHornInclusions_rlp_llp]
  intro X Y f hf
  exact TopCat.horn_llp_le_weakHomotopyEquivalences _ hf

/-- The selected boundary-generated model structure on compactly generated
spaces. -/
@[instance_reducible]
noncomputable def modelCategory :
    HomotopicalAlgebra.ModelCategory CompactlyGenerated.{u, v} := by
  letI : CategoryWithCofibrations CompactlyGenerated.{u, v} :=
    ⟨modelCofibrations.{u, v}⟩
  letI : CategoryWithFibrations CompactlyGenerated.{u, v} :=
    ⟨modelFibrations.{u, v}⟩
  letI : CategoryWithWeakEquivalences CompactlyGenerated.{u, v} :=
    ⟨weakHomotopyEquivalences.{u, v}⟩
  letI : CategoryTheory.Limits.HasLimitsOfSize.{v, v}
      CompactlyGenerated.{u, v} :=
    CategoryTheory.hasLimits_of_coreflective
      compactlyGeneratedToTop.{u, v}
  let d : HomotopicalAlgebra.SmithModelStructureData.{v}
      (C := CompactlyGenerated.{u, v})
      realizedBoundaryInclusions.{u, v}
      weakHomotopyEquivalences.{u, v} :=
    HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      realizedBoundaryInclusions.{u, v}
      realizedHornInclusions.{u, v}
      weakHomotopyEquivalences.{u, v}
      (by
        unfold weakHomotopyEquivalences
        infer_instance)
      generatedTrivialFibrationEq
      generatedHornAcyclic
  exact d.modelCategory
    (by
      unfold weakHomotopyEquivalences
      infer_instance)
    (by
      change modelCofibrations.{u, v} =
        realizedBoundaryInclusions.{u, v}.rlp.llp
      exact realizedBoundaryInclusions_rlp_llp.symm)
    (by
      change modelFibrations.{u, v} =
        realizedHornInclusions.{u, v}.rlp
      exact realizedHornInclusions_rlp.symm)
    rfl

namespace modelCategory

/-- Opt-in instance for the model structure `CompactlyGenerated.modelCategory`. -/
noncomputable scoped instance instModelCategory :
    HomotopicalAlgebra.ModelCategory CompactlyGenerated.{u, v} :=
  CompactlyGenerated.modelCategory

end modelCategory

section

open scoped CompactlyGenerated.modelCategory

/-- Fixed-cardinal cofibrant-generation data for the selected model. -/
noncomputable def cofibrantGenerationData :
    HomotopicalAlgebra.CofibrantGenerationData
      CompactlyGenerated.{u, v} realizedGeneratorCardinal.{v} where
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
        rw [realizedHornInclusions_rlp]
        rfl
      _ = trivialFibrations CompactlyGenerated.{u, v} := rfl
  J_rlp := by
    calc
      realizedHornInclusions.{u, v}.rlp = modelFibrations.{u, v} := by
        rw [realizedHornInclusions_rlp]
        rfl
      _ = fibrations CompactlyGenerated.{u, v} := rfl

end

end CompactlyGenerated
