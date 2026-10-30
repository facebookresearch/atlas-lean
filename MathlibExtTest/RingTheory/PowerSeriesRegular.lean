/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.RegularLocalRing

@[expose] public section

open PowerSeries

example (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) 𝓞) :=
  IsRegularLocalRing.mvPowerSeries_fin 𝓞 n

example (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim R⟦X⟧ = ringKrullDim R + 1 :=
  PowerSeries.ringKrullDim_powerSeries R

example (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsRegularLocalRing R⟦X⟧ :=
  PowerSeries.isRegularLocalRing_powerSeries R
