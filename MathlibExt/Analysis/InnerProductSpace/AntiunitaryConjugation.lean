/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Complex.Basic

/-!
# Actual bounded operators conjugated by an antiunitary

A given conjugate-linear complex linear-isometry equivalence J transports
an original bounded complex-linear operator A to J A J^(-1). The two
conjugate scalar changes compose to the identity, so the result is an
actual complex-linear bounded operator on the target normed space.
The source and target have independent carrier universes. On complex
Hilbert spaces J is the usual antiunitary isometry equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LinearIsometryEquiv

noncomputable section

universe uH uK

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- The actual bounded complex-linear operator J A J^(-1) for the given conjugate-linear isometry. -/
def conjugateComplexOperator (J : H ≃ₗᵢ⋆[ℂ] K) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp J.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The transported bounded operator has its literal original J(A(J^(-1)x)) value. -/
@[simp]
theorem conjugateComplexOperator_apply (J : H ≃ₗᵢ⋆[ℂ] K) (A : H →L[ℂ] H) (x : K) :
    J.conjugateComplexOperator A x = J (A (J.symm x)) :=
  rfl

end

end LinearIsometryEquiv
