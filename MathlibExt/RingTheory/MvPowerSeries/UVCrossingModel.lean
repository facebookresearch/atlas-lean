/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_UVCrossingModel.lean`,
`Theorems/Thm_ModularCurve_UVCrossingModel_U_ne_V.lean`
and
`P2M/Sol/S_ModularCurve_UVCrossingModel_U_ne_V.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

noncomputable section

namespace ModularCurve

/-- The ideal in two-variable power series cutting out the crossing
`X₀ * X₁ = π`. -/
def uvCrossingIdeal (W : Type*) [CommRing W] (π : W) :
    Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
    MvPowerSeries.C π}

/-- The quotient of two-variable power series by the crossing relation
`X₀ * X₁ = π`. -/
abbrev UVCrossingModel (W : Type*) [CommRing W] (π : W) : Type _ :=
  MvPowerSeries (Fin 2) W ⧸ uvCrossingIdeal W π

namespace UVCrossingModel

variable {W : Type*} [CommRing W]

/-- The quotient map from two-variable power series to the crossing model. -/
def mk (π : W) : MvPowerSeries (Fin 2) W →+* UVCrossingModel W π :=
  Ideal.Quotient.mk _

/-- The first branch coordinate, the image of `X₀`. -/
def U (π : W) : UVCrossingModel W π := mk π (MvPowerSeries.X 0)

/-- The second branch coordinate, the image of `X₁`. -/
def V (π : W) : UVCrossingModel W π := mk π (MvPowerSeries.X 1)

/-- The image of a constant power series. -/
def const (π : W) (w : W) : UVCrossingModel W π := mk π (MvPowerSeries.C w)

/-- The ring homomorphism sending a coefficient to its constant image. -/
def constHom (π : W) : W →+* UVCrossingModel W π :=
  (mk π).comp (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W)

theorem constHom_apply (π : W) (w : W) : constHom π w = const π w := rfl

theorem mk_surjective (π : W) : Function.Surjective (mk (W := W) π) :=
  Ideal.Quotient.mk_surjective

/-- The embedding of the single power-series variable as the first of the
two crossing variables. -/
private def branchEmb : Unit ↪ Fin 2 :=
  ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

private theorem branchEmb_apply (x : Unit) : branchEmb x = 0 := rfl

private theorem one_notMem_range_branchEmb : (1 : Fin 2) ∉ Set.range branchEmb := by
  rintro ⟨x, hx⟩
  rw [branchEmb_apply] at hx
  exact absurd hx (by decide)

/-- The branch map: kill the second variable and reduce coefficients
modulo `π`. Its value on the first branch coordinate is the power-series
variable, and on the second branch coordinate it is zero. -/
private def branchMap (π : W) :
    MvPowerSeries (Fin 2) W →+* PowerSeries (W ⧸ Ideal.span {π}) :=
  (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π}))).comp
    (MvPowerSeries.killCompl branchEmb).toRingHom

private theorem branchMap_X_zero (π : W) :
    branchMap π (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) W) =
      PowerSeries.X := by
  have h : branchEmb () = (0 : Fin 2) := rfl
  change PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π}))
    (MvPowerSeries.killCompl branchEmb (MvPowerSeries.X 0)) = _
  rw [← h, MvPowerSeries.killCompl_X]
  exact PowerSeries.map_X _

private theorem branchMap_X_one (π : W) :
    branchMap π (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) W) = 0 := by
  change PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π}))
    (MvPowerSeries.killCompl branchEmb (MvPowerSeries.X 1)) = _
  rw [MvPowerSeries.killCompl_X_eq_zero one_notMem_range_branchEmb, map_zero]

private theorem branchMap_C (π : W) (w : W) :
    branchMap π (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) =
      PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  change PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π}))
    (MvPowerSeries.killCompl branchEmb (MvPowerSeries.C w)) = _
  rw [MvPowerSeries.killCompl_C]
  exact PowerSeries.map_C _ _

private theorem branchMap_crossing (π : W) :
    branchMap π ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
      MvPowerSeries.C π) = 0 := by
  rw [map_sub, map_mul, branchMap_X_zero, branchMap_X_one, mul_zero, branchMap_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), map_zero,
    sub_zero]

/-- The branch map descended to the crossing model. -/
private def branchLift (π : W) :
    UVCrossingModel W π →+* PowerSeries (W ⧸ Ideal.span {π}) :=
  Ideal.Quotient.lift (uvCrossingIdeal W π) (branchMap π) (by
    intro a ha
    have hle : uvCrossingIdeal W π ≤ RingHom.ker (branchMap π) := by
      rw [uvCrossingIdeal, Ideal.span_le, Set.singleton_subset_iff]
      exact branchMap_crossing π
    exact hle ha)

private theorem branchLift_U (π : W) : branchLift π (U π) = PowerSeries.X :=
  branchMap_X_zero π

private theorem branchLift_V (π : W) : branchLift π (V π) = 0 :=
  branchMap_X_one π

/-- The two branch coordinates of the crossing model are distinct whenever
the coefficient quotient by `π` is nontrivial: the branch map sends the
first coordinate to the power-series variable and the second to zero. -/
public theorem U_ne_V (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ≠ V π := by
  intro h
  have hX : (PowerSeries.X : PowerSeries (W ⧸ Ideal.span {π})) = 0 := by
    rw [← branchLift_U π, h, branchLift_V π]
  exact PowerSeries.X_ne_zero hX

end UVCrossingModel

end ModularCurve

end
