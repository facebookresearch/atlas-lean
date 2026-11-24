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

public import MathlibExt.MeasureTheory.Measure.RadonProduct
public import Mathlib.Analysis.Complex.Basic

/-!
# Compact-support pure products for the actual Borel Radon measure

The literal product of compact-support factor functions has compact support
on the topological product. For complex factors, its squared norm is the
literal product of the two real squared-norm functions. Coordinate integration
retains an actual compact-support function, and the original Radon-product
integral gives the exact pure-product square-integral identity.

The inputs remain arbitrary locally compact Hausdorff Borel factor spaces
and measures finite on compact sets. The completed L2 tensor identification
and its dense extension remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported

noncomputable section

universe uX uY uR

namespace CompactlySupportedContinuousMap

section Product

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]
variable {R : Type uR} [TopologicalSpace R] [MulZeroClass R] [ContinuousMul R]

/-- The literal pure product of compact-support functions on the original topological product. -/
def mulProd (f : C_c(X, R)) (g : C_c(Y, R)) : C_c(X × Y, R) where
  toFun z := f z.1 * g z.2
  continuous_toFun := (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (f.hasCompactSupport.prod g.hasCompactSupport)
    rintro ⟨x, y⟩ hxy
    by_cases hx : x ∈ tsupport f
    · have hy : y ∉ tsupport g := fun hy => hxy ⟨hx, hy⟩
      simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- The compact-support pure product has its exact original factor values. -/
@[simp]
theorem mulProd_apply (f : C_c(X, R)) (g : C_c(Y, R)) (x : X) (y : Y) :
    mulProd f g (x, y) = f x * g y := rfl

end Product

section NormSquare

variable {X : Type uX} [TopologicalSpace X]

/-- The actual real squared-norm function of a complex compact-support function. -/
def normSq (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := ‖f x‖ ^ 2
  continuous_toFun := f.continuous.norm.pow 2
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

/-- The compact-support squared norm has the literal real squared-norm values. -/
@[simp]
theorem normSq_apply (f : C_c(X, ℂ)) (x : X) : normSq f x = ‖f x‖ ^ 2 := rfl

variable [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- The pure complex product's squared norm is the actual product of the factor squared norms. -/
theorem normSq_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    normSq (mulProd f g) = mulProd (normSq f) (normSq g) := by
  ext z
  rcases z with ⟨x, y⟩
  simp only [normSq_apply, mulProd_apply, norm_mul, mul_pow]

end NormSquare

section CoordinateIntegral

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

/-- The real pure product's coordinate integral is the original factor times the actual scalar integral. -/
theorem integralRight_mulProd (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)) :
    integralRight ν (mulProd f g) = (∫ y : Y, g y ∂ν) • f := by
  ext x
  change (∫ y : Y, f x * g y ∂ν) = (∫ y : Y, g y ∂ν) * f x
  rw [integral_const_mul]
  exact mul_comm _ _

/-- Coordinate integration of the pure square retains the actual compact-support squared-norm factor. -/
theorem integralRight_normSq_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    integralRight ν (normSq (mulProd f g)) = (∫ y : Y, ‖g y‖ ^ 2 ∂ν) • normSq f := by
  rw [normSq_mulProd]
  exact integralRight_mulProd ν (normSq f) (normSq g)

end CoordinateIntegral

end CompactlySupportedContinuousMap

namespace MeasureTheory.Measure

open CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y)
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- The Borel measurable space of the literal product used for compact-support Radon integration. -/
local instance instCompactSupportProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instCompactSupportProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The actual Borel Radon integral of a real compact-support pure product factors exactly. -/
theorem integral_mulProd (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)) :
    ∫ z : X × Y, mulProd f g z ∂(radonProd μ ν) =
      (∫ x : X, f x ∂μ) * ∫ y : Y, g y ∂ν := by
  calc
    ∫ z : X × Y, mulProd f g z ∂(radonProd μ ν) =
        ∫ x : X, ∫ y : Y, f x * g y ∂ν ∂μ := integral_radonProd μ ν (mulProd f g)
    _ = ∫ x : X, f x * (∫ y : Y, g y ∂ν) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => integral_const_mul (f x) (g : Y → ℝ))
    _ = (∫ x : X, f x ∂μ) * ∫ y : Y, g y ∂ν :=
      integral_mul_const (∫ y : Y, g y ∂ν) (f : X → ℝ)

/-- The pure complex product has the exact original product of square integrals on the Borel Radon carrier. -/
theorem integral_norm_sq_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    ∫ z : X × Y, ‖mulProd f g z‖ ^ 2 ∂(radonProd μ ν) =
      (∫ x : X, ‖f x‖ ^ 2 ∂μ) * ∫ y : Y, ‖g y‖ ^ 2 ∂ν := by
  change (∫ z : X × Y, normSq (mulProd f g) z ∂(radonProd μ ν)) = _
  rw [normSq_mulProd]
  exact integral_mulProd μ ν (normSq f) (normSq g)

end MeasureTheory.Measure

end
