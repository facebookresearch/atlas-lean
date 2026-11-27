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

public import MathlibExt.MeasureTheory.Measure.RadonProduct.Fubini

/-!
# Coordinate exchange of Borel Radon products

For locally compact Hausdorff Borel spaces and measures finite on compact sets, the coordinate
swap `(x,y) ↦ (y,x)` pushes `radonProd μ ν` to `radonProd ν μ`.

It is measure preserving between these two Borel topological products. The factors and their
universes are independent, and no countability or s-finiteness assumption is required.
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

/-- **Borel measurable structure of the first coordinate order.** For topological spaces
`X,Y`, the carrier `X×Y` uses `borel(X×Y)` from its product topology. -/
local instance instSwapXYMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instSwapXYBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Borel measurable structure of the reversed coordinate order.** For topological spaces
`X,Y`, the carrier `Y×X` uses `borel(Y×X)` from its product topology. -/
local instance instSwapYXMeasurableSpace : MeasurableSpace (Y × X) := borel (Y × X)
local instance instSwapYXBorelSpace : BorelSpace (Y × X) := ⟨rfl⟩

/-- **Swap pushforward reverses the Radon product factors.** Let `X,Y` be locally compact
Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite on
compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`.
`Measure.map Prod.swap (radonProd μ ν)=radonProd ν μ` on the reversed Borel topological
product `Y×X`. -/
theorem map_prodSwap_radonProd :
    Measure.map (Prod.swap : X × Y → Y × X) (radonProd μ ν) = radonProd ν μ := by
  let e := Homeomorph.prodComm X Y
  change Measure.map e (radonProd μ ν) = radonProd ν μ
  let _ : (Measure.map e (radonProd μ ν)).Regular := Measure.Regular.map e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [e.measurableEmbedding.integral_map]
  let F : C_c(X × Y, ℝ) :=
    ⟨⟨fun z => f (e z), f.continuous.comp e.continuous⟩,
      f.hasCompactSupport.comp_homeomorph e⟩
  change (∫ z : X × Y, F z ∂(radonProd μ ν)) = ∫ z : Y × X, f z ∂(radonProd ν μ)
  rw [integral_radonProd μ ν F, integral_radonProd_swap ν μ f]
  rfl

/-- **Measure-preserving coordinate swap of Radon products.** Let `X,Y` be locally compact
Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite on
compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`.
`Prod.swap : X×Y → Y×X` is measure preserving from `radonProd μ ν` to `radonProd ν μ`. -/
theorem measurePreserving_prodSwap_radonProd :
    MeasurePreserving (Prod.swap : X × Y → Y × X) (radonProd μ ν) (radonProd ν μ) :=
  ⟨(Homeomorph.prodComm X Y).measurable, map_prodSwap_radonProd μ ν⟩


end MeasureTheory.Measure
