/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornSequentialSmallObject

@[expose] public section

/-!
# Horn sequential small-object shape client

Thin public client for `TopCat.horn_rlp_llp_eq_cardinalOrd`,
`TopCat.horn_rlp_llp_eq_sequential`, and
`TopCat.horn_sequentialRetracts_le_rlp_llp` by term application only.
Restates the exact cardinal-ordinal equality, the universe-zero `ℕ`-shaped
equality, and forwards the unconditional sequential reverse inclusion unchanged.
Also forwards the aleph0 coyoneda-preservation signature unchanged. Supplies
no premise, adds no instance, and claims no weak-equivalence or model structure.
-/

set_option autoImplicit false

open CategoryTheory MorphismProperty

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornSequentialSmallObjectTests

universe u

/-- Exact cardinal-ordinal shape client, by direct term application. -/
theorem horn_rlp_llp_eq_cardinalOrd_client :
    TopCat.realizedHornInclusions.{u}.rlp.llp =
      (transfiniteCompositionsOfShape
        (coproducts.{u} TopCat.realizedHornInclusions.{u}).pushouts
        realizedGeneratorCardinal.{u}.ord.ToType).retracts :=
  TopCat.horn_rlp_llp_eq_cardinalOrd

/-- Unconditional sequential reverse-inclusion client, by direct application. -/
theorem horn_sequentialRetracts_le_rlp_llp_client :
    ((coproducts.{u} TopCat.realizedHornInclusions.{u}).pushouts.transfiniteCompositionsOfShape
      ℕ).retracts ≤ TopCat.realizedHornInclusions.{u}.rlp.llp :=
  TopCat.horn_sequentialRetracts_le_rlp_llp

/-- Direct preservation client for aleph0 coyoneda preservation, by exact application.
Tests the separate public preservation signature, not an `rlp.llp` equality. -/
theorem preservesColimit_coyoneda_of_relativeCellComplex_horn_aleph0_client
    {A B : TopCat.{0}} (i : A ⟶ B)
    (hi : TopCat.realizedHornInclusions.{0} i)
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : HomotopicalAlgebra.RelativeCellComplex.{0}
      (fun (_ : Cardinal.aleph0.{0}.ord.ToType) ↦
        TopCat.realizedHornInclusions.{0}.homFamily) f) :
    CategoryTheory.Limits.PreservesColimit hf.F
      (CategoryTheory.coyoneda.obj (Opposite.op A)) :=
  TopCat.preservesColimit_coyoneda_of_relativeCellComplex_horn_aleph0 i hi f hf

#synth MorphismProperty.IsCardinalForSmallObjectArgument
  TopCat.realizedHornInclusions.{0} Cardinal.aleph0.{0}

/-- Sequential equality client at universe zero, by direct term application. -/
theorem horn_rlp_llp_eq_sequential_client :
    TopCat.realizedHornInclusions.{0}.rlp.llp =
      ((coproducts.{0} TopCat.realizedHornInclusions.{0}).pushouts.transfiniteCompositionsOfShape
        ℕ).retracts :=
  TopCat.horn_rlp_llp_eq_sequential

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHornSequentialSmallObjectTests
