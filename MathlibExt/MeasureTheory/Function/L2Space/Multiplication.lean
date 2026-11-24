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

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Tactic.Ring

/-!
# Actual bounded continuous multiplication on the canonical L2 space

A bounded continuous complex function multiplies the original Lp ℂ2 μ
classes pointwise. Its actual L∞ membership and Hölder product prove L2
membership; the original pointwise bound gives the actual operator norm
bound. The original algebra and inner-product integral identities construct
the literal multiplication star representation.

This DATA is required by the original pointwise commutative representation
and normal multiplication-sum statements. The original measure is arbitrary:
no finite/probability, chosen L2 model, norm, measurability or operator
certificate is added. Empty spaces and zero measures retain their actual
canonical carriers and operators.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace BoundedContinuousFunction

universe uX

variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
variable (μ : Measure X)

/-- The original bounded function acts through the stock Hölder multiplication operator. -/
def l2MultiplicationOperator (f : X →ᵇ ℂ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ ∞ 2 2
    ((f.memLp_top (μ := μ)).toLp f)

/-- Literal multiplication of the original L2 coefficient class by the given bounded function. -/
def mulOnL2 (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  l2MultiplicationOperator μ f u

/-- The actual result has the original pointwise product representative almost everywhere. -/
theorem mulOnL2_ae_eq (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    mulOnL2 μ f u =ᵐ[μ] fun x => f x * u x := by
  have hop := (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2)
    ((f.memLp_top (μ := μ)).toLp f) u
  have hf := (MemLp.coeFn_toLp (f.memLp_top (μ := μ)))
  filter_upwards [hop, hf] with x hx hfx
  change mulOnL2 μ f u x = f x * u x
  change mulOnL2 μ f u x = _ at hx
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hfx] using hx

/-- The actual pointwise multiplication map inherits the stock operator's complex linearity. -/
def mulOnL2LinearMap (f : X →ᵇ ℂ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
  (l2MultiplicationOperator μ f).toLinearMap

/-- The actual L2product is bounded by the original coefficient supremum norm and vector norm. -/
theorem mulOnL2_norm_le (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    ‖mulOnL2 μ f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulOnL2_ae_eq μ f u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg (u x))

/-- The bounded multiplication operator retains the original pointwise product values almost everywhere. -/
theorem l2MultiplicationOperator_ae_eq (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    l2MultiplicationOperator μ f u =ᵐ[μ] fun x => f x * u x := mulOnL2_ae_eq μ f u

/-- The actual pointwise operator norm is bounded by the original given function's sup norm. -/
theorem norm_l2MultiplicationOperator_le (f : X →ᵇ ℂ) :
    ‖l2MultiplicationOperator μ f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (mulOnL2_norm_le μ f)

/-- The literal pointwise multiplication representation on the original canonical L2 carrier. -/
def l2MultiplicationRepresentation : (X →ᵇ ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := l2MultiplicationOperator μ
  map_one' := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ 1 u = u
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ 1 u] with x hx
    simpa using hx
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ (f * g) u = mulOnL2 μ f (mulOnL2 μ g u)
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ (f * g) u, mulOnL2_ae_eq μ f (mulOnL2 μ g u),
      mulOnL2_ae_eq μ g u] with x hfg hf hg
    rw [hfg, hf, hg]
    exact mul_assoc _ _ _
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ 0 u = 0
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ 0 u, (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ))] with x hx hz
    rw [hx, hz]
    simp
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ (f + g) u = mulOnL2 μ f u + mulOnL2 μ g u
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ (f + g) u,
      Lp.coeFn_add (mulOnL2 μ f u) (mulOnL2 μ g u),
      mulOnL2_ae_eq μ f u, mulOnL2_ae_eq μ g u] with x hfg hsum hf hg
    rw [hfg, hsum]
    change (f x + g x) * u x = mulOnL2 μ f u x + mulOnL2 μ g u x
    rw [hf, hg]
    exact add_mul _ _ _
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ (algebraMap ℂ (X →ᵇ ℂ) c) u = c • u
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ (algebraMap ℂ (X →ᵇ ℂ) c) u,
      Lp.coeFn_smul c u] with x hc hu
    exact hc.trans hu.symm
  map_star' f := by
    show l2MultiplicationOperator μ (star f) = star (l2MultiplicationOperator μ f)
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
    intro u v
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [l2MultiplicationOperator_ae_eq μ (star f) u,
      l2MultiplicationOperator_ae_eq μ f v] with x hfu hfv
    rw [hfu, hfv]
    rw [RCLike.inner_apply', RCLike.inner_apply']
    simp only [← RCLike.star_def, BoundedContinuousFunction.star_apply,
      star_mul, star_star, mul_assoc]

/-- The multiplication representation keeps the literal original product representative. -/
theorem l2MultiplicationRepresentation_ae_eq (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    l2MultiplicationRepresentation μ f u =ᵐ[μ] fun x => f x * u x :=
  l2MultiplicationOperator_ae_eq μ f u

end BoundedContinuousFunction

namespace ContinuousMap

universe uX

section CompactToBounded

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

/-- Original compact-space continuous functions have their same canonical bounded star-algebra values. -/
def toBoundedStarAlgHom : C(X, ℂ) →⋆ₐ[ℂ] BoundedContinuousFunction X ℂ where
  toFun := BoundedContinuousFunction.mkOfCompact
  map_one' := rfl
  map_mul' _f _g := rfl
  map_zero' := rfl
  map_add' _f _g := rfl
  commutes' _c := rfl
  map_star' _f := rfl

end CompactToBounded

variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [CompactSpace X]

/-- The actual continuous-function multiplication representation on the original arbitrary-measure L2space. -/
def l2MultiplicationRepresentation (μ : Measure X) :
    C(X, ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  (BoundedContinuousFunction.l2MultiplicationRepresentation μ).comp toBoundedStarAlgHom

/-- Every original continuous coefficient keeps its literal original L2product values almost everywhere. -/
theorem l2MultiplicationRepresentation_ae_eq (μ : Measure X) (f : C(X, ℂ)) (u : Lp ℂ 2 μ) :
    l2MultiplicationRepresentation μ f u =ᵐ[μ] fun x => f x * u x :=
  BoundedContinuousFunction.l2MultiplicationRepresentation_ae_eq μ
    (BoundedContinuousFunction.mkOfCompact f) u

end ContinuousMap

end
