/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.EqualCharacteristicFFAnalyticModels

/-!
# Equal-characteristic source coefficient and axiom probes

The source q-Frobenius preserves the original t variable, while acting
on its actual perfectoid coefficient ring. These probes inspect native
ring, annulus, coefficient, invariant-sheaf and quotient maps separately
from every Wanted construction provider.
-/

set_option autoImplicit false

open MathlibExt.AlgebraicGeometry

open MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
open MathlibExt.AlgebraicGeometry.EqualCharacteristicFFRingModels

private theorem first_uniformizer_coefficient (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [CharP k p] [Fintype k]
    (C : ResidueData p k) (S : Base p k C) :
    PowerSeries.coeff 1 (frobenius p k C S (prime p k C S)) = 1 := by
  rw [frobenius_prime]
  exact PowerSeries.coeff_one_X

#print axioms first_uniformizer_coefficient
#print axioms integerEquiv_normalized
#print axioms coefficientFrobenius_scalar
#print axioms frobenius_integralCoefficients
#print axioms chartPunctures_unit
#print axioms fieldCoefficients_integral
#print axioms restrict_comp
#print axioms EqualCharacteristicFFSheafModels.invariant_frobenius
#print axioms EqualCharacteristicFFAnalyticModels.quotient_point_square
#print axioms EqualCharacteristicFFAnalyticModels.quotientPresheafTransport
#print axioms EqualCharacteristicFFAnalyticModels.quotientStructureMap
