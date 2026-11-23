/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorRLPComparison

@[expose] public section

/-!
# Boundary/horn right-class comparison client test

Minimal public client for `TopCat.realizedBoundaryRLP_le_realizedHornRLP`
in every universe: realized boundary right class lies below the realized horn
right class. Restates exact `≤` type by term application only; no reproof.
No weak-equivalence, fibration, filling, product, colimit, or model-category claim.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatGeneratorRLPComparisonTests

theorem realizedBoundaryRLP_le_realizedHornRLP_client :
    (TopCat.realizedBoundaryInclusions.{u} : MorphismProperty TopCat.{u}).rlp ≤
      (TopCat.realizedHornInclusions.{u} : MorphismProperty TopCat.{u}).rlp :=
  TopCat.realizedBoundaryRLP_le_realizedHornRLP

example :
    (TopCat.realizedBoundaryInclusions.{1} : MorphismProperty TopCat.{1}).rlp ≤
      (TopCat.realizedHornInclusions.{1} : MorphismProperty TopCat.{1}).rlp :=
  TopCat.realizedBoundaryRLP_le_realizedHornRLP

example :
    (TopCat.realizedBoundaryInclusions.{0} : MorphismProperty TopCat.{0}).rlp ≤
      (TopCat.realizedHornInclusions.{0} : MorphismProperty TopCat.{0}).rlp :=
  TopCat.realizedBoundaryRLP_le_realizedHornRLP

#print axioms TopCat.realizedBoundaryRLP_le_realizedHornRLP
#print axioms realizedBoundaryRLP_le_realizedHornRLP_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatGeneratorRLPComparisonTests
