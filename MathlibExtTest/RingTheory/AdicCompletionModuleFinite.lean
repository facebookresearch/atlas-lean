/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.ModuleFinite

/-- A finite local extension of an adically complete local ring is adically
complete at its maximal ideal. -/
example {𝒪 : Type*} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {T : Type*} [CommRing T] [Algebra 𝒪 T]
    [Module.Finite 𝒪 T] [IsLocalRing T] [IsLocalHom (algebraMap 𝒪 T)] :
    IsAdicComplete (IsLocalRing.maximalIdeal T) T :=
  IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)
