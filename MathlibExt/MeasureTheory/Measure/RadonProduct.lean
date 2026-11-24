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

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The Radon product on the Borel topological product

Integrating a compactly supported continuous function in one coordinate
gives a compactly supported continuous function in the other coordinate.
The resulting positive iterated integral functional has an actual regular
Riesz measure on the Borel sigma-algebra of the topological product.

Both measures need only be finite on compact sets. There is no countability
or s-finiteness assumption and no identification with the product of the
factor sigma-algebras. The construction retains the literal product carrier.
The reverse-order Fubini theorem and the completed L2 tensor comparison are
separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported

noncomputable section

universe uX uY

namespace CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- The literal section of a compact-support function in the second coordinate. -/
def sectionRight (f : C_c(X × Y, ℝ)) (x : X) : C_c(Y, ℝ) where
  toFun y := f (x, y)
  continuous_toFun := f.continuous.comp (continuous_const.prodMk continuous_id)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (f.hasCompactSupport.image continuous_snd)
    intro y hy
    exact image_eq_zero_of_notMem_tsupport
      (fun hxy => hy ⟨(x, y), hxy, rfl⟩)

/-- A section retains its exact original pointwise values. -/
@[simp]
theorem sectionRight_apply (f : C_c(X × Y, ℝ)) (x : X) (y : Y) :
    sectionRight f x y = f (x, y) := rfl

variable [T2Space X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

/-- Integrate the second coordinate, retaining the actual compact-support function. -/
def integralRight (f : C_c(X × Y, ℝ)) : C_c(X, ℝ) where
  toFun x := ∫ y : Y, f (x, y) ∂ν
  continuous_toFun := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support
      (f.hasCompactSupport.image continuous_snd)
    · have huncurry :
          (Function.uncurry (fun (x : X) (y : Y) => f (x, y)) : X × Y → ℝ) =
            (f.toContinuousMap : X × Y → ℝ) := by
        funext p
        rcases p with ⟨x, y⟩
        rfl
      rw [huncurry, univ_prod_univ]
      exact f.continuous.continuousOn
    · intro x y _ hy
      exact image_eq_zero_of_notMem_tsupport
        (fun hxy => hy ⟨(x, y), hxy, rfl⟩)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (f.hasCompactSupport.image continuous_fst)
    intro x hx
    have hzero (y : Y) : f (x, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hxy => hx ⟨(x, y), hxy, rfl⟩)
    simp only [hzero, integral_zero]

omit [T2Space Y] in
/-- Coordinate integration has the original integral as every pointwise value. -/
@[simp]
theorem integralRight_apply (f : C_c(X × Y, ℝ)) (x : X) :
    integralRight ν f x = ∫ y : Y, f (x, y) ∂ν := rfl

/-- Coordinate integration is an actual positive linear map on compact-support functions. -/
def integralRightPositiveLinearMap : C_c(X × Y, ℝ) →ₚ[ℝ] C_c(X, ℝ) where
  toFun := integralRight ν
  map_add' f g := by
    ext x
    change (∫ y : Y, f (x, y) + g (x, y) ∂ν) =
      (∫ y : Y, f (x, y) ∂ν) + ∫ y : Y, g (x, y) ∂ν
    exact integral_add (sectionRight f x).integrable (sectionRight g x).integrable
  map_smul' c f := by
    ext x
    change (∫ y : Y, c • f (x, y) ∂ν) = c • ∫ y : Y, f (x, y) ∂ν
    exact integral_smul c (fun y : Y => f (x, y))
  monotone' := by
    intro f g hfg x
    exact integral_mono (sectionRight f x).integrable (sectionRight g x).integrable
      (fun y => hfg (x, y))

/-- The positive coordinate map is the computed coordinate integral. -/
@[simp]
theorem integralRightPositiveLinearMap_apply (f : C_c(X × Y, ℝ)) :
    integralRightPositiveLinearMap ν f = integralRight ν f := rfl

end CompactlySupportedContinuousMap

namespace MeasureTheory.Measure

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y)
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- The Borel measurable space of the topological product used by the actual Radon product. -/
local instance instProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The actual Radon product, on the Borel sigma-algebra of the topological product. -/
def radonProd : @Measure (X × Y) (borel (X × Y)) :=
  RealRMK.rieszMeasure
    ((CompactlySupportedContinuousMap.integralPositiveLinearMap μ).comp
      (CompactlySupportedContinuousMap.integralRightPositiveLinearMap ν))

/-- The constructed product is an actual regular measure. -/
instance regular_radonProd : (radonProd μ ν).Regular := by
  unfold radonProd
  infer_instance

/-- Compact-support integration against the product is the literal iterated integral. -/
theorem integral_radonProd (f : C_c(X × Y, ℝ)) :
    ∫ z : X × Y, f z ∂(radonProd μ ν) =
      ∫ x : X, ∫ y : Y, f (x, y) ∂ν ∂μ :=
  RealRMK.integral_rieszMeasure
    ((CompactlySupportedContinuousMap.integralPositiveLinearMap μ).comp
      (CompactlySupportedContinuousMap.integralRightPositiveLinearMap ν)) f

end MeasureTheory.Measure

end
