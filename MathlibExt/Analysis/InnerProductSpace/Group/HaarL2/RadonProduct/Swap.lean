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
# Coordinate-swap isometry of Hilbert-valued Radon L²

For locally compact Hausdorff Borel factors and measures finite on compact sets, coordinate
exchange gives `Lp H 2 (radonProd μ ν) ≃ Lp H 2 (radonProd ν μ)`.

The forward and inverse maps pull back by `(y,x) ↦ (x,y)`. They preserve the L² norm and have
the swapped coordinate values almost everywhere. The coefficient space `H` only needs a complex
normed-space structure, with no inner product or completeness.
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

/-- **Borel product structure before exchanging Radon L² coordinates.** For topological `X,Y`,
use `borel(X×Y)` from the product topology. -/
local instance instSwapXYMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instSwapXYBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Borel product structure after exchanging Radon L² coordinates.** For topological `X,Y`,
use `borel(Y×X)` from the reversed product topology. -/
local instance instSwapYXMeasurableSpace : MeasurableSpace (Y × X) := borel (Y × X)
local instance instSwapYXBorelSpace : BorelSpace (Y × X) := ⟨rfl⟩

namespace HaarL2

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **Linear isometric exchange of Radon L² coordinates.** Let `X,Y` be locally compact
Hausdorff Borel spaces, `μ,ν` measures finite on compact sets, and `H` a complex normed
space, possibly incomplete. Put `R=radonProd μ ν` and `R'=radonProd ν μ`.
`radonProductSwapIsometry μ ν : Lp H 2 R ≃ₗᵢ[ℂ] Lp H 2 R'` has almost-everywhere value
`ξ(x,y) ↦ ξ(x,y)` evaluated at the swapped point `(y,x)`. -/
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

/-- **Forward Radon-swap map as measure-preserving pullback.** Let `X,Y` be locally compact
Hausdorff Borel spaces, `μ,ν` measures finite on compact sets, and `H` a complex normed
space, possibly incomplete. Put `R=radonProd μ ν` and `R'=radonProd ν μ`. the forward map
pulls a class on `X×Y` back along `Prod.swap : Y×X → X×Y`, using its measure preservation
from `R'` to `R`. -/
theorem radonProductSwapIsometry_apply (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    radonProductSwapIsometry (H := H) μ ν ξ =
      Lp.compMeasurePreserving (Prod.swap : Y × X → X × Y)
        (Measure.measurePreserving_prodSwap_radonProd ν μ) ξ := rfl

/-- **Inverse Radon-swap map as measure-preserving pullback.** Let `X,Y` be locally compact
Hausdorff Borel spaces, `μ,ν` measures finite on compact sets, and `H` a complex normed
space, possibly incomplete. Put `R=radonProd μ ν` and `R'=radonProd ν μ`. the inverse map
pulls a class on `Y×X` back along `Prod.swap : X×Y → Y×X`, measure preserving from `R` to
`R'`. -/
theorem radonProductSwapIsometry_symm_apply (ξ : Lp H 2 (Measure.radonProd ν μ)) :
    (radonProductSwapIsometry (H := H) μ ν).symm ξ =
      Lp.compMeasurePreserving (Prod.swap : X × Y → Y × X)
        (Measure.measurePreserving_prodSwap_radonProd μ ν) ξ := rfl

/-- **Almost-everywhere forward coordinate exchange in Radon L².** Let `X,Y` be locally
compact Hausdorff Borel spaces, `μ,ν` measures finite on compact sets, and `H` a complex
normed space, possibly incomplete. Put `R=radonProd μ ν` and `R'=radonProd ν μ`. for `ξ∈Lp
H 2 R`, its forward image has value `(y,x) ↦ ξ(x,y)` for `R'`-almost every `(y,x)`. -/
theorem radonProductSwapIsometry_ae_eq (ξ : Lp H 2 (Measure.radonProd μ ν)) :
    radonProductSwapIsometry (H := H) μ ν ξ =ᵐ[Measure.radonProd ν μ]
      fun z : Y × X => ξ (z.2, z.1) := by
  rw [radonProductSwapIsometry_apply]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ
    (Measure.measurePreserving_prodSwap_radonProd ν μ)] with z hz
  exact hz

/-- **Almost-everywhere inverse coordinate exchange in Radon L².** Let `X,Y` be locally
compact Hausdorff Borel spaces, `μ,ν` measures finite on compact sets, and `H` a complex
normed space, possibly incomplete. Put `R=radonProd μ ν` and `R'=radonProd ν μ`. for `η∈Lp
H 2 R'`, its inverse image has value `(x,y) ↦ η(y,x)` for `R`-almost every `(x,y)`. -/
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
