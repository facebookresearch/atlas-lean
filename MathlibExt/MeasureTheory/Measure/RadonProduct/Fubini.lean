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
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Reverse compact-support integration for the actual Borel Radon product

The published compact-support Fubini theorem applies to the original
jointly continuous real function and the two factor measures finite on
compact sets. Together with the defining Radon-product integral, it gives
the original reverse-order formula on the topological product.

There is no global s-finiteness or countability assumption, and no equality
between the product Borel sigma-algebra and the factor product sigma-algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CompactlySupported

namespace MeasureTheory.Measure

universe uX uY

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y)
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- The actual Borel measurable space of the topological product. -/
local instance instFubiniProductMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instFubiniProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
/-- The original real compact-support coordinate integrals have equal values in both orders. -/
theorem integral_integral_radonProd_swap (f : C_c(X × Y, ℝ)) :
    (∫ x : X, ∫ y : Y, f (x, y) ∂ν ∂μ) =
      ∫ y : Y, ∫ x : X, f (x, y) ∂μ ∂ν := by
  have huncurry : Function.uncurry (fun (x : X) (y : Y) => f (x, y)) =
      (f : X × Y → ℝ) := by
    funext z
    rcases z with ⟨x, y⟩
    rfl
  exact integral_integral_swap_of_hasCompactSupport
    (huncurry.symm ▸ f.continuous) (huncurry.symm ▸ f.hasCompactSupport)

/-- The actual Borel Radon-product integral has the original reverse-coordinate formula. -/
theorem integral_radonProd_swap (f : C_c(X × Y, ℝ)) :
    (∫ z : X × Y, f z ∂(radonProd μ ν)) =
      ∫ y : Y, ∫ x : X, f (x, y) ∂μ ∂ν := by
  rw [integral_radonProd μ ν f]
  exact integral_integral_radonProd_swap μ ν f

end MeasureTheory.Measure
