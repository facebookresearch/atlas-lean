/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ControlTheory.StateSpace.SISO
public import MathlibExt.ControlTheory.StateSpace.Coefficients

/-!
# SISO bridge for state-space coefficients

`ControlTheory.StateSpaceCoeffs.ofSISO` adapts the real
single-input single-output `LinearSystem` to the generic coefficient
record. The field and output agreement theorems identify the adapted
dynamics and output with the SISO system's `field` and `output`.
-/

open Matrix

@[expose] public section

namespace ControlTheory

namespace StateSpaceCoeffs

/-- The coefficient record of the real single-input single-output
`LinearSystem`: state matrix by matrix-vector multiplication, input map
`u ↦ u • b`, output map `x ↦ c ⬝ᵥ x`, and feedthrough `u ↦ d * u`. -/
noncomputable def ofSISO {n : Type*} [Fintype n]
    (S : MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem n) :
    StateSpaceCoeffs ℝ (n → ℝ) ℝ ℝ where
  A := (Matrix.mulVecLin S.A).toContinuousLinearMap
  B := (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) S.b).toContinuousLinearMap
  C := ∑ i, (S.c i) • (ContinuousLinearMap.proj i : (n → ℝ) →L[ℝ] ℝ)
  D := S.d • ContinuousLinearMap.id ℝ ℝ

/-- The dynamics of `ofSISO S` are the SISO vector field:
`A x + B u = S.field x u`. -/
theorem ofSISO_field {n : Type*} [Fintype n]
    (S : MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem n)
    (x : n → ℝ) (u : ℝ) :
    (ofSISO S).A x + (ofSISO S).B u
      = MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem.field S x u := by
  simp [ofSISO, MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem.field,
    LinearMap.smulRight_apply]

/-- The output of `ofSISO S` is the SISO output:
`C x + D u = S.output x u`. -/
theorem ofSISO_output {n : Type*} [Fintype n]
    (S : MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem n)
    (x : n → ℝ) (u : ℝ) :
    (ofSISO S).C x + (ofSISO S).D u
      = MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem.output S x u := by
  simp [ofSISO, MathlibExt.Biology.Dynamics.IntegralFeedback.LinearSystem.output,
    dotProduct, smul_eq_mul]

end StateSpaceCoeffs

end ControlTheory
