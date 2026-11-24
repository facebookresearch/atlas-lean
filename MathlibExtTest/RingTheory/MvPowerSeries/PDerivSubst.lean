/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.PDerivSubst

@[expose] public section

open MvPowerSeries in
private theorem exactSource
    {σ : Type*} {R : Type*} [CommRing R] (i : σ) (a : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R) :
    MvPowerSeries.pderiv i (PowerSeries.subst a h) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) h) *
        MvPowerSeries.pderiv i a :=
  MvPowerSeries.pderiv_subst i a ha h

universe u v

/-- Higher-universe consumer: the statement is universe-polymorphic. -/
private theorem exactSourceUniverse
    {σ : Type u} {R : Type v} [CommRing R] (i : σ) (a : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R) :
    MvPowerSeries.pderiv i (PowerSeries.subst a h) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) h) *
        MvPowerSeries.pderiv i a :=
  MvPowerSeries.pderiv_subst i a ha h

/-- Boundary: without the zero-constant-term hypothesis the composite need not
even be defined by this substitution; with `a = X i` and `h = X` the chain rule
recovers `pderiv i (X i) = 1`. -/
example {R : Type*} [CommRing R] (i : Fin 1) :
    MvPowerSeries.pderiv i
        (PowerSeries.subst (MvPowerSeries.X i) (PowerSeries.X : PowerSeries R)) =
      (1 : MvPowerSeries (Fin 1) R) := by
  have ha : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 1) R) = 0 :=
    MvPowerSeries.constantCoeff_X i
  rw [MvPowerSeries.pderiv_subst i _ ha, PowerSeries.derivative_X,
    ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    map_one, MvPowerSeries.pderiv_X_self, mul_one]
