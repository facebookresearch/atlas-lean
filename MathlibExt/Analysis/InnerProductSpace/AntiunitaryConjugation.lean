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
# Conjugate-linear isometric transport of bounded operators

Let `H,K` be complex normed spaces and `J : H ≃ₗᵢ⋆[ℂ] K` a conjugate-linear isometric
equivalence. For `A : H →L[ℂ] H`, the conjugated operator on `K` is `J A J⁻¹`, with value `x ↦
J(A(J⁻¹x))`.

The two conjugate-linear factors make this a bounded complex-linear operator. Inner products and
completeness are not required; when the spaces are Hilbert spaces, `J` is an antiunitary.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LinearIsometryEquiv

noncomputable section

universe uH uK

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- **Bounded complex operator transported by a conjugate isometry.** Let `H,K` be complex
normed spaces in independent universes and `J : H ≃ₗᵢ⋆[ℂ] K` a conjugate-linear isometric
equivalence. for `A : H →L[ℂ] H`, `conjugateComplexOperator J A : K →L[ℂ] K` is `J A J⁻¹`;
the two conjugate scalar actions cancel. -/
def conjugateComplexOperator (J : H ≃ₗᵢ⋆[ℂ] K) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp J.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- **Value of a conjugate-isometry operator transport.** Let `H,K` be complex normed spaces
in independent universes and `J : H ≃ₗᵢ⋆[ℂ] K` a conjugate-linear isometric equivalence.
for bounded `A : H →L[ℂ] H` and `x ∈ K`, `J.conjugateComplexOperator A x=J(A(J.symm x))`. -/
@[simp]
theorem conjugateComplexOperator_apply (J : H ≃ₗᵢ⋆[ℂ] K) (A : H →L[ℂ] H) (x : K) :
    J.conjugateComplexOperator A x = J (A (J.symm x)) :=
  rfl

end

end LinearIsometryEquiv
