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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSCompletion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The original bounded left operator on the actual weight GNS carrier

The literal finite-square left action is transported to the computed
weight pre-GNS norm. The original positive-square weight estimate gives
its genuine norm bound; this constructs the continuous linear left map.
The stock completion of that map acts on the actual weight GNS carrier
and preserves the original dense-domain multiplication values.

No supplied norm/model certificate or source existence output is used.
This module constructs bounded operators only. The kernel adjoint identity,
star representation, faithful normal range and Tomita/modular/polar objects
remain separate constructor obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Transport the literal original left action through the exact finite-square type-copy identity. -/
def Weight.preGNSLeftMulLinear (φ : Weight A) (a : A) : φ.PreGNS →ₗ[ℂ] φ.PreGNS :=
  φ.preGNSLinearEquiv.symm.toLinearMap.comp
    ((φ.finiteSquareLeftMul a).comp φ.preGNSLinearEquiv.toLinearMap)

/-- The transported linear action retains the original finite-square left multiplication. -/
theorem Weight.preGNSLeftMulLinear_apply (φ : Weight A) (a : A) (x : φ.PreGNS) :
    φ.preGNSLinearEquiv (φ.preGNSLeftMulLinear a x) = φ.finiteSquareLeftMul a (φ.preGNSLinearEquiv x) := by
  change φ.preGNSLinearEquiv
    (φ.preGNSLinearEquiv.symm (φ.finiteSquareLeftMul a (φ.preGNSLinearEquiv x))) = _
  exact φ.preGNSLinearEquiv.apply_symm_apply _

/-- The original positive-square weight inequality gives the actual pre-GNS norm bound. -/
theorem Weight.preGNSLeftMulLinear_norm_le (φ : Weight A) (a : A) (x : φ.PreGNS) :
    ‖φ.preGNSLeftMulLinear a x‖ ≤ ‖a‖ * ‖x‖ := by
  let y : φ.finiteSquareSubmodule := φ.preGNSLinearEquiv x
  have hbound := φ.value_leftSquare_mul_le a (y : A)
  have hfinite : ENNReal.ofNNReal (NNReal.mk (‖a‖ ^ 2) (sq_nonneg ‖a‖)) *
      φ.value (leftSquare (y : A)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top y.property
  have hreal := ENNReal.toReal_mono hfinite.ne hbound
  rw [ENNReal.toReal_mul] at hreal
  have hcoefficient :
      (ENNReal.ofNNReal (NNReal.mk (‖a‖ ^ 2) (sq_nonneg ‖a‖))).toReal = ‖a‖ ^ 2 := rfl
  rw [hcoefficient] at hreal
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg a) (norm_nonneg x)), mul_pow,
    φ.preGNS_norm_sq, φ.preGNS_norm_sq, φ.preGNSLeftMulLinear_apply]
  change (φ.value (leftSquare (a * (y : A)))).toReal ≤
    ‖a‖ ^ 2 * (φ.value (leftSquare (y : A))).toReal
  exact hreal

/-- The genuine weight-norm bound constructs the original continuous linear left map. -/
def Weight.preGNSLeftMul (φ : Weight A) (a : A) : φ.PreGNS →L[ℂ] φ.PreGNS :=
  (φ.preGNSLeftMulLinear a).mkContinuous ‖a‖ (φ.preGNSLeftMulLinear_norm_le a)

/-- The bounded pre-GNS operator is the same actual transported linear map. -/
theorem Weight.preGNSLeftMul_apply (φ : Weight A) (a : A) (x : φ.PreGNS) :
    φ.preGNSLeftMul a x = φ.preGNSLeftMulLinear a x :=
  rfl

/-- Forgetting the weight type copy gives exactly the original ambient left product. -/
theorem Weight.preGNSLeftMul_originalValue (φ : Weight A) (a : A) (x : φ.PreGNS) :
    (φ.preGNSLinearEquiv (φ.preGNSLeftMul a x) : A) = a * (φ.preGNSLinearEquiv x : A) := by
  rw [φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply, φ.finiteSquareLeftMul_apply]

/-- The original bounded left action extends to the literal completed weight GNS carrier. -/
def Weight.gnsLeftMul (φ : Weight A) (a : A) : φ.GNS →L[ℂ] φ.GNS :=
  (φ.preGNSLeftMul a).completion

/-- The completed left operator preserves the actual canonical dense-domain values. -/
theorem Weight.gnsLeftMul_toGNS (φ : Weight A) (a : A) (x : φ.PreGNS) :
    φ.gnsLeftMul a (φ.toGNS x) = φ.toGNS (φ.preGNSLeftMul a x) := by
  change (φ.preGNSLeftMul a).completion (x : UniformSpace.Completion φ.PreGNS) =
    (φ.preGNSLeftMul a x : UniformSpace.Completion φ.PreGNS)
  exact ContinuousLinearMap.completion_apply_coe _ _

/-- The completed original-domain left action has exactly the original finite-square product. -/
theorem Weight.gnsLeftMul_gnsMap (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    φ.gnsLeftMul a (φ.gnsMap x) = φ.gnsMap (φ.finiteSquareLeftMul a x) := by
  rw [φ.gnsMap_apply, φ.gnsLeftMul_toGNS, φ.gnsMap_apply]
  apply congrArg φ.toGNS
  apply φ.preGNSLinearEquiv.injective
  rw [φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end

end CStarAlgebra.ScalarWeight
