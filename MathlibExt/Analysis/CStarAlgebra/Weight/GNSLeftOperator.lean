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
# Bounded left multiplication on the weight Hilbert space

For a nonunital complex C-star algebra and extended positive weight `φ`, left multiplication by
`a` preserves `n_φ = {x : φ(x* x) < ∞}`. In the weight seminorm `‖x‖_φ=√((φ(x* x)).toReal)`, it
obeys `‖a*x‖_φ ≤ ‖a‖ ‖x‖_φ`.

This gives a bounded complex-linear operator on the seminormed domain and its extension `π(a)`
to the Hilbert completion. For the dense GNS map `Λ`, `π(a)Λ(x)=Λ(a*x)`. No faithfulness,
ambient-domain density or boundedness of the weight is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Linear left action on the weight type copy.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. let `e : PreGNS φ ≃ₗ[ℂ] n_φ` be `preGNSLinearEquiv φ`. The linear operator is `L_a=e⁻¹ ∘
(x ↦ a*x) ∘ e` for `a : A`. -/
def Weight.preGNSLeftMulLinear (φ : Weight A) (a : A) : φ.PreGNS →ₗ[ℂ] φ.PreGNS :=
  φ.preGNSLinearEquiv.symm.toLinearMap.comp
    ((φ.finiteSquareLeftMul a).comp φ.preGNSLinearEquiv.toLinearMap)

/-- **Left multiplication under the domain identification.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. for `e=preGNSLinearEquiv φ`, `e(preGNSLeftMulLinear φ a x)=a*e(x)` as an
element of `n_φ`, where `a*e(x)` denotes multiplication in `A`. -/
theorem Weight.preGNSLeftMulLinear_apply (φ : Weight A) (a : A) (x : φ.PreGNS) :
    φ.preGNSLinearEquiv (φ.preGNSLeftMulLinear a x) = φ.finiteSquareLeftMul a (φ.preGNSLinearEquiv x) := by
  change φ.preGNSLinearEquiv
    (φ.preGNSLinearEquiv.symm (φ.finiteSquareLeftMul a (φ.preGNSLinearEquiv x))) = _
  exact φ.preGNSLinearEquiv.apply_symm_apply _

/-- **Weight seminorm bound for left multiplication.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. for `a : A` and `x : PreGNS φ`, `‖preGNSLeftMulLinear φ a x‖_φ ≤ ‖a‖*‖x‖_φ`;
the coefficient norm is the C-star norm of `A`. -/
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

/-- **Bounded pre-GNS left operator.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`.
`preGNSLeftMul φ a` is the continuous complex-linear map `x ↦ a*x` in the weight-seminormed
type copy, with bound `‖L_a x‖_φ ≤ ‖a‖*‖x‖_φ`. -/
def Weight.preGNSLeftMul (φ : Weight A) (a : A) : φ.PreGNS →L[ℂ] φ.PreGNS :=
  (φ.preGNSLeftMulLinear a).mkContinuous ‖a‖ (φ.preGNSLeftMulLinear_norm_le a)

/-- **Value of the bounded pre-GNS left operator.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `preGNSLeftMul φ a x = preGNSLeftMulLinear φ a x` for `a : A` and `x : PreGNS φ`. -/
theorem Weight.preGNSLeftMul_apply (φ : Weight A) (a : A) (x : φ.PreGNS) :
    φ.preGNSLeftMul a x = φ.preGNSLeftMulLinear a x :=
  rfl

/-- **Algebra value of pre-GNS left multiplication.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. if `e=preGNSLinearEquiv φ`, then the element of `A` underlying `e(preGNSLeftMul
φ a x)` is `a * (e(x) : A)` for `a : A` and `x : PreGNS φ`. -/
theorem Weight.preGNSLeftMul_originalValue (φ : Weight A) (a : A) (x : φ.PreGNS) :
    (φ.preGNSLinearEquiv (φ.preGNSLeftMul a x) : A) = a * (φ.preGNSLinearEquiv x : A) := by
  rw [φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply, φ.finiteSquareLeftMul_apply]

/-- **Completed GNS left operator.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. `gnsLeftMul φ a : H_φ →L[ℂ] H_φ` is the completion of the bounded pre-GNS operator
`L_a`, so `π(a)Λ(x)=Λ(a*x)`. -/
def Weight.gnsLeftMul (φ : Weight A) (a : A) : φ.GNS →L[ℂ] φ.GNS :=
  (φ.preGNSLeftMul a).completion

/-- **Completed left action on pre-GNS vectors.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. for `a : A` and `x : PreGNS φ`, `gnsLeftMul φ a (toGNS φ x)=toGNS φ
(preGNSLeftMul φ a x)`. -/
theorem Weight.gnsLeftMul_toGNS (φ : Weight A) (a : A) (x : φ.PreGNS) :
    φ.gnsLeftMul a (φ.toGNS x) = φ.toGNS (φ.preGNSLeftMul a x) := by
  change (φ.preGNSLeftMul a).completion (x : UniformSpace.Completion φ.PreGNS) =
    (φ.preGNSLeftMul a x : UniformSpace.Completion φ.PreGNS)
  exact ContinuousLinearMap.completion_apply_coe _ _

/-- **Completed action on finite square elements.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. for `a : A` and `x ∈ n_φ`, `gnsLeftMul φ a (Λ x)=Λ(a*x)`. -/
theorem Weight.gnsLeftMul_gnsMap (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    φ.gnsLeftMul a (φ.gnsMap x) = φ.gnsMap (φ.finiteSquareLeftMul a x) := by
  rw [φ.gnsMap_apply, φ.gnsLeftMul_toGNS, φ.gnsMap_apply]
  apply congrArg φ.toGNS
  apply φ.preGNSLinearEquiv.injective
  rw [φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end

end CStarAlgebra.ScalarWeight
