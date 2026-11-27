/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Depth.QuotSMulTop
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Tests for `MathlibExt.RingTheory.Depth.QuotSMulTop`
-/

@[expose] public section

#check @IsLocalRing.nontrivial_quotSMulTop_of_mem_maximalIdeal
#check @IsLocalRing.one_le_depth_iff
#check @IsLocalRing.depth_quotSMulTop_add_one
#check @IsLocalRing.depth_quotSMulTop

open IsLocalRing

/-- A nonzero element of the maximal ideal of a Noetherian local domain lowers the depth of the
ring by one. -/
example {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0) :
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x R)) =
      IsLocalRing.depth (ModuleCat.of R R) - 1 :=
  depth_quotSMulTop hx (IsSMulRegular.of_ne_zero hx0)

private lemma X_mem_maximalIdeal :
    (PowerSeries.X : PowerSeries ℚ) ∈ maximalIdeal (PowerSeries ℚ) := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

/-- Concrete instance: in `ℚ⟦X⟧`, `depth (ℚ⟦X⟧ / X) + 1 = depth ℚ⟦X⟧`. -/
example : IsLocalRing.depth
      (ModuleCat.of (PowerSeries ℚ)
        (QuotSMulTop (PowerSeries.X : PowerSeries ℚ) (PowerSeries ℚ))) + 1 =
    IsLocalRing.depth (ModuleCat.of (PowerSeries ℚ) (PowerSeries ℚ)) :=
  depth_quotSMulTop_add_one X_mem_maximalIdeal
    (IsSMulRegular.of_ne_zero (PowerSeries.X_ne_zero (R := ℚ)))

/-- Concrete instance: `ℚ⟦X⟧` has depth at least one. -/
example : 1 ≤ IsLocalRing.depth (ModuleCat.of (PowerSeries ℚ) (PowerSeries ℚ)) :=
  one_le_depth_iff.mpr
    ⟨_, X_mem_maximalIdeal, IsSMulRegular.of_ne_zero (PowerSeries.X_ne_zero (R := ℚ))⟩
