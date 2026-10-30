/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.AdicCompleteDomain
import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-- A finite domain algebra over `ℤ_[p]` is local; here the algebra is `ℤ_[p]` itself. -/
example (p : ℕ) [Fact p.Prime] : IsLocalRing ℤ_[p] :=
  IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete (R := ℤ_[p]) (S := ℤ_[p])

universe u

/-- The local-ring criterion is available for rings in an arbitrary common universe. -/
example {R S : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S :=
  IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete (R := R) (S := S)

/-- The local-ring criterion applies to a genuine higher-universe ring. -/
example (p : ℕ) [Fact p.Prime] : IsLocalRing (ULift.{1} ℤ_[p]) := by
  let hnoetherian : IsNoetherianRing (ULift.{1} ℤ_[p]) :=
    isNoetherianRing_of_ringEquiv ℤ_[p] ULift.ringEquiv.symm
  let hlocal : IsLocalRing (ULift.{1} ℤ_[p]) := ULift.ringEquiv.symm.isLocalRing
  let hcancel : IsCancelMulZero (ULift.{1} ℤ_[p]) :=
    Function.Injective.isCancelMulZero ULift.down ULift.down_injective rfl (fun _ _ => rfl)
  let hdomain : IsDomain (ULift.{1} ℤ_[p]) :=
    { toIsCancelMulZero := hcancel, toNontrivial := inferInstance }
  have hcomplete :
      IsAdicComplete ((IsLocalRing.maximalIdeal ℤ_[p]).map ULift.ringEquiv.symm)
        (ULift.{1} ℤ_[p]) :=
    (IsAdicComplete.congr_ringEquiv
      (IsLocalRing.maximalIdeal ℤ_[p]) ULift.ringEquiv.symm).mpr inferInstance
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at hcomplete
  exact
    IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete
      (R := ULift.{1} ℤ_[p]) (S := ULift.{1} ℤ_[p])
