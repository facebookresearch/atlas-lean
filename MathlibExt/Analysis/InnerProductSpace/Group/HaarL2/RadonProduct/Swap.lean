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

public import MathlibExt.MeasureTheory.Measure.RadonProduct.Swap
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Actual coordinate exchange of the original Borel Radon product

The generic measure owner proves the original coordinate exchange of the
Borel Radon products. Literal measure-preserving pullbacks give the full
normed-space-valued L2 equivalence, including zero fibers and independent
factor universes. No inner product or completeness of H is required.

This is the coordinate field needed to identify the original H-first
nested double tensor with its full Borel product L2 model before partial
Fourier transport. It selects no normalized dual Haar measure or Fourier
unitary from a Source existence statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open scoped CompactlySupported

namespace MeasureTheory

noncomputable section

universe uX uY uH

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

namespace HaarL2

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Actual inverse coordinate pullback exchanges the full H-valued Borel product L2 spaces. -/
def radonProductSwapIsometry :
    Lp H 2 (Measure.radonProd μ ν) ≃ₗᵢ[ℂ] Lp H 2 (Measure.radonProd ν μ) := by
  let hXY := Measure.measurePreserving_prodSwap_radonProd μ ν
  let hYX := Measure.measurePreserving_prodSwap_radonProd ν μ
  exact
    { toFun := Lp.compMeasurePreserving (Prod.swap : Y × X → X × Y) hYX
      invFun := Lp.compMeasurePreserving (Prod.swap : X × Y → Y × X) hXY
      left_inv ξ := by
        apply Lp.ext
        have hQ : QuasiMeasurePreserving (Prod.swap : X × Y → Y × X)
            (Measure.radonProd μ ν) (Measure.radonProd ν μ) :=
          hXY.quasiMeasurePreserving
        filter_upwards [Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreserving (Prod.swap : Y × X → X × Y) hYX ξ) hXY,
          hQ.ae_eq_comp (Lp.coeFn_compMeasurePreserving ξ hYX)] with z h₁ h₂
        exact h₁.trans (h₂.trans (congrArg (fun w : X × Y => ξ w) (Prod.swap_swap z)))
      right_inv ξ := by
        apply Lp.ext
        have hQ : QuasiMeasurePreserving (Prod.swap : Y × X → X × Y)
            (Measure.radonProd ν μ) (Measure.radonProd μ ν) :=
          hYX.quasiMeasurePreserving
        filter_upwards [Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreserving (Prod.swap : X × Y → Y × X) hXY ξ) hYX,
          hQ.ae_eq_comp (Lp.coeFn_compMeasurePreserving ξ hXY)] with z h₁ h₂
        exact h₁.trans (h₂.trans (congrArg (fun w : Y × X => ξ w) (Prod.swap_swap z)))
      map_add' ξ η := (Lp.compMeasurePreserving (Prod.swap : Y × X → X × Y) hYX).map_add ξ η
      map_smul' c ξ := (Lp.compMeasurePreservingₗ ℂ (Prod.swap : Y × X → X × Y) hYX).map_smul c ξ
      norm_map' ξ := Lp.norm_compMeasurePreserving ξ hYX }

/-- The actual coordinate L2 equivalence has its literal reversed-coordinate pullback DATA. -/
theorem radonProductSwapIsometry_apply (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    radonProductSwapIsometry (H := H) μ ν ξ =
      Lp.compMeasurePreserving (Prod.swap : Y × X → X × Y)
        (Measure.measurePreserving_prodSwap_radonProd ν μ) ξ := rfl

/-- The actual inverse coordinate equivalence has the literal original-coordinate pullback DATA. -/
theorem radonProductSwapIsometry_symm_apply (ξ : Lp H 2 (Measure.radonProd ν μ)) :
    (radonProductSwapIsometry (H := H) μ ν).symm ξ =
      Lp.compMeasurePreserving (Prod.swap : X × Y → Y × X)
        (Measure.measurePreserving_prodSwap_radonProd μ ν) ξ := rfl

/-- Every original product L2 vector retains its swapped coordinate values almost everywhere. -/
theorem radonProductSwapIsometry_ae_eq (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    radonProductSwapIsometry (H := H) μ ν ξ =ᵐ[Measure.radonProd ν μ]
      fun z : Y × X => ξ (z.2, z.1) := by
  rw [radonProductSwapIsometry_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_prodSwap_radonProd ν μ)] with z hz
  exact hz

/-- The actual inverse product L2 equivalence keeps the original swapped coordinate formula a.e. -/
theorem radonProductSwapIsometry_symm_ae_eq (ξ : Lp H 2 (Measure.radonProd ν μ)) :
    (radonProductSwapIsometry (H := H) μ ν).symm ξ =ᵐ[Measure.radonProd μ ν]
      fun z : X × Y => ξ (z.2, z.1) := by
  rw [radonProductSwapIsometry_symm_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_prodSwap_radonProd μ ν)] with z hz
  exact hz

end HaarL2

end

end MeasureTheory
