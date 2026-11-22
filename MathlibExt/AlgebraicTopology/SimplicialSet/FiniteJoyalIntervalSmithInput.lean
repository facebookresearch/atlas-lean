/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalBoundarySolutionSet
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingSaturation
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingRetracts

/-!
# FiniteJoyalIntervalSmithInput

The six concrete generatorwise Smith hypotheses for finite-J testing.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory
universe u
namespace SSet.joyalInterval

/-- The actual boundary and finite-J testing classes satisfy all six
Smith hypotheses, before any genuine model structure is constructed. -/
theorem smithRecognitionInput :
    HomotopicalAlgebra.SmithRecognitionInput.{u} (C := SSet.{u})
      modelCategoryQuillen.I
      (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions) := by
  let W : MorphismProperty SSet.{u} :=
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
  let : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions
      auxiliaryAnodyneExtensions.rlp := by
    change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions auxiliaryNaiveFibrations
    infer_instance
  have hT : modelCategoryQuillen.I.rlp.llp ⊓ W =
      productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions := by
    rw [modelCategoryQuillen.llp_rlp_I]
    rfl
  refine {
    weak_two_out_of_three := inferInstance
    weak_retracts := inferInstance
    trivial_fibrations_weak := ?_
    trivial_cofibrations_cobase := ?_
    trivial_cofibrations_transfinite := ?_
    solution_set := testingEquivalences_boundary_solution_set }
  · rw [← rlp_monomorphisms]
    exact productPrecylinder.{u}.rlp_monomorphisms_le_testingEquivalences
      auxiliaryAnodyneExtensions.{u}
  · rw [hT]
    infer_instance
  · rw [hT]
    infer_instance

end SSet.joyalInterval
