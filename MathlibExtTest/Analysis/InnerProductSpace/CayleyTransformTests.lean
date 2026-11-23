/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import MathlibExt.Analysis.InnerProductSpace.CayleyTransform

@[expose] public section

/-!
# Tests for the Cayley transform

Concrete checks of `MathlibExt.Analysis.InnerProductSpace.CayleyTransform`:
scalar operators (where the transform is the Möbius scalar
`(c - i) / (c + i)`), the zero operator (Cayley transform `-1`, spectrum
`{-1}`, eigenvalue `-1`), and the operator norm on a scalar operator.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.CayleyTransformTest

open MathlibExt.Analysis.InnerProductSpace.CayleyTransform

/-- A real scalar operator is self-adjoint. -/
private theorem isSelfAdjoint_ofReal_smul_one (c : ℝ) :
    IsSelfAdjoint ((c : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  show star ((c : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = (c : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  simp [star_smul, Complex.conj_ofReal]

/-- The Cayley transform of a real scalar operator is the scalar operator of
the Möbius image. -/
private theorem cayleyTransform_ofReal_smul_one (c : ℝ) :
    ContinuousLinearMap.cayleyTransform (((c : ℂ)) • (1 : ℂ →L[ℂ] ℂ))
      = ((c - Complex.I) / (c + Complex.I)) • (1 : ℂ →L[ℂ] ℂ) := by
  rw [ContinuousLinearMap.cayleyTransform, ← sub_smul, ← add_smul,
    ContinuousLinearMap.ringInverse_smul_one, smul_mul_smul, mul_one, div_eq_mul_inv]

/-- The Cayley transform of the zero operator is `-1`. -/
private theorem cayleyTransform_zero :
    ContinuousLinearMap.cayleyTransform (0 : ℂ →L[ℂ] ℂ) = -(1 : ℂ →L[ℂ] ℂ) := by
  rw [ContinuousLinearMap.cayleyTransform]
  simp only [zero_sub, zero_add, ← neg_smul]
  rw [ContinuousLinearMap.ringInverse_smul_one, smul_mul_smul, mul_one, Complex.inv_I,
    neg_mul_neg, Complex.I_mul_I, neg_one_smul]

/-- The scalar formula at `c = 0` agrees with the direct computation. -/
example : ContinuousLinearMap.cayleyTransform ((((0 : ℝ)) : ℂ) • (1 : ℂ →L[ℂ] ℂ))
    = -(1 : ℂ →L[ℂ] ℂ) := by
  rw [cayleyTransform_ofReal_smul_one]
  rw [Complex.ofReal_zero, zero_sub, zero_add, neg_div, div_self Complex.I_ne_zero]
  exact neg_one_smul ℂ _

/-- The spectrum of the Cayley transform of the zero operator is `{-1}`. -/
example : spectrum ℂ (ContinuousLinearMap.cayleyTransform (0 : ℂ →L[ℂ] ℂ)) = {-1} := by
  have h0 : spectrum ℂ (0 : ℂ →L[ℂ] ℂ) = {0} := by
    ext z
    rw [spectrum.mem_iff, Set.mem_singleton_iff, Algebra.algebraMap_eq_smul_one, sub_zero]
    constructor
    · intro h
      by_contra hz
      exact h (ContinuousLinearMap.isUnit_smul_one _ hz)
    · intro hz
      rw [hz, zero_smul]
      exact not_isUnit_zero
  rw [ContinuousLinearMap.spectrum_cayleyTransform _ (IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)), h0,
    Set.image_singleton]
  congr 1
  rw [zero_sub, zero_add, neg_div, div_self Complex.I_ne_zero]

/-- `1 - U = 2 • 1` for the Cayley transform of the zero operator. -/
example : (1 : ℂ →L[ℂ] ℂ) - ContinuousLinearMap.cayleyTransform (0 : ℂ →L[ℂ] ℂ)
    = (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  rw [cayleyTransform_zero, sub_neg_eq_add]
  module

/-- The Cayley transform of a nonzero real scalar operator has norm `1`. -/
example : ‖ContinuousLinearMap.cayleyTransform (((2 : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖ = 1 :=
  ContinuousLinearMap.norm_cayleyTransform _ (isSelfAdjoint_ofReal_smul_one 2)

/-- `-1` is an eigenvalue of the Cayley transform of the zero operator,
corresponding to the eigenvalue `0` of the zero operator. -/
example : Module.End.HasEigenvalue
    ((ContinuousLinearMap.cayleyTransform (0 : ℂ →L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) :
      Module.End ℂ ℂ) (-1) := by
  have h0 : Module.End.HasEigenvalue ((0 : ℂ →L[ℂ] ℂ) : Module.End ℂ ℂ) 0 := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, one_ne_zero⟩
    rw [Module.End.mem_eigenspace_iff]
    simp
  have h := (ContinuousLinearMap.hasEigenvalue_cayleyTransform_iff (0 : ℂ →L[ℂ] ℂ)
    (IsSelfAdjoint.zero (ℂ →L[ℂ] ℂ)) (by norm_num : (-1 : ℂ) ≠ 1)).mpr ?_
  · exact h
  · have hval : Complex.I * (1 + (-1 : ℂ)) / (1 - (-1 : ℂ)) = 0 := by simp
    rw [hval]
    exact h0

end MathlibExtTest.Analysis.InnerProductSpace.CayleyTransformTest
