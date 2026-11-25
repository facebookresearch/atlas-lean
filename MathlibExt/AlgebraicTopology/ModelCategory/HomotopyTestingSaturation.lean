/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingLeftClass
public import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Native closure of monic testing equivalences

The actual testing left class equals left lifting against naive fibrations
with naive fibrant codomain. Native left-lifting closure therefore supplies
composition, cobase change, retracts, coproducts and continuous transfinite
composition. The closure index universe is independent of the cylinder size.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Corollary 2.4.31 (printed p.62 / PDF p.78), with the explicit generic
inputs for the proved unrestricted class equality. Colimit conclusions use
supplied colimit data; no existence of all colimits or model factorization
is asserted.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe t w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- Cobase change acts on the actual testing left class. -/
instance testingTrivialCofibrations_isStableUnderCobaseChange :
    (P.testingTrivialCofibrations An).IsStableUnderCobaseChange := by
  rw [testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An]
  infer_instance

/-- The actual testing left class is stable under arrow retracts. -/
instance testingTrivialCofibrations_isStableUnderRetracts :
    (P.testingTrivialCofibrations An).IsStableUnderRetracts := by
  rw [testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An]
  infer_instance

/-- Identities and compositions belong to the same testing left class. -/
instance testingTrivialCofibrations_isMultiplicative :
    (P.testingTrivialCofibrations An).IsMultiplicative := by
  rw [testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An]
  infer_instance

/-- Coproduct closure at an independent index universe, for supplied colimits. -/
instance testingTrivialCofibrations_isStableUnderCoproducts :
    (P.testingTrivialCofibrations An).IsStableUnderCoproducts.{t} :=
  MorphismProperty.IsStableUnderCoproducts.of_llp_eq
    (P.testingTrivialCofibrations An)
    (An.naiveFibrations ⊓ MorphismProperty.ofObjectProperty ⊤ An.naiveFibrantObjects)
    (testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An).symm

/-- Continuous transfinite closure at an independent index universe. -/
instance testingTrivialCofibrations_isStableUnderTransfiniteComposition :
    (P.testingTrivialCofibrations An).IsStableUnderTransfiniteComposition.{t} :=
  MorphismProperty.IsStableUnderTransfiniteComposition.of_llp_eq
    (P.testingTrivialCofibrations An)
    (An.naiveFibrations ⊓ MorphismProperty.ofObjectProperty ⊤ An.naiveFibrantObjects)
    (testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An).symm

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
