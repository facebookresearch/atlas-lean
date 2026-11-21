/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues

@[expose] public noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.SmallEtaleCoefficients

open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
open MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues

/-- The actual lifted-integer coefficient reduction retains the nonzero Z/2 unit. -/
example : (scalarReduction 2).hom (1 : Scalar) = (1 : FiniteCoefficient 2) := rfl

example : (scalarReduction 2).hom (1 : Scalar) ≠ 0 := by decide

end MathlibExtTest.AlgebraicGeometry.SmallEtaleCoefficients

