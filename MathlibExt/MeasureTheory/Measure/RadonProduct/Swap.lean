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
# Coordinate exchange of the actual Borel Radon product

Compact-support integral uniqueness and the original reverse Fubini law
prove the literal exchange of two topological Borel Radon measures.
Independent factors and zero measures remain; no L2 or Haar model enters.
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

/-- The original Borel measurable structure of the X-first topological product. -/
local instance instSwapXYMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instSwapXYBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original Borel measurable structure of the Y-first topological product. -/
local instance instSwapYXMeasurableSpace : MeasurableSpace (Y × X) := borel (Y × X)
local instance instSwapYXBorelSpace : BorelSpace (Y × X) := ⟨rfl⟩

/-- Literal coordinate exchange maps the actual Borel Radon product to its reversed product. -/
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

/-- Coordinate exchange preserves the actual two Borel Radon measures in their original orders. -/
theorem measurePreserving_prodSwap_radonProd :
    MeasurePreserving (Prod.swap : X × Y → Y × X) (radonProd μ ν) (radonProd ν μ) :=
  ⟨(Homeomorph.prodComm X Y).measurable, map_prodSwap_radonProd μ ν⟩


end MeasureTheory.Measure
