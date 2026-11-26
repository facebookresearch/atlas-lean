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
# Reverse-order compact-support Radon integration

For locally compact Hausdorff Borel spaces and measures finite on compact sets, a real
compact-support continuous function has equal iterated integrals in both coordinate orders.

Thus `∫ f d(μ⊗_Rν)=∫ y, ∫ x, f(x,y) dμ dν`. No global s-finiteness or countability assumption is
imposed, and the measure is on the Borel structure of the topological product.
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

/-- **Borel product structure for reverse coordinate integration.** For topological spaces
`X,Y`, the product measurable space is `borel(X×Y)` from its product topology. -/
local instance instFubiniProductMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instFubiniProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
/-- **Equality of both iterated compact-support integral orders.** Let `X,Y` be locally
compact Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite
on compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`. for
`f∈C_c(X×Y,ℝ)`, `∫ x, ∫ y, f(x,y) dν dμ = ∫ y, ∫ x, f(x,y) dμ dν`. -/
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

/-- **Reverse coordinate formula for the Borel Radon integral.** Let `X,Y` be locally compact
Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite on
compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`. for
`f∈C_c(X×Y,ℝ)`, `∫ f d(μ⊗_Rν)=∫ y, ∫ x, f(x,y) dμ dν`. -/
theorem integral_radonProd_swap (f : C_c(X × Y, ℝ)) :
    (∫ z : X × Y, f z ∂(radonProd μ ν)) =
      ∫ y : Y, ∫ x : X, f (x, y) ∂μ ∂ν := by
  rw [integral_radonProd μ ν f]
  exact integral_integral_radonProd_swap μ ν f

end MeasureTheory.Measure
