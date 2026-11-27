/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.FlatTower

@[expose] public section

open CategoryTheory

universe u v

/-- `exactSource` consumer with the original binders. -/
example {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S' :=
  IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map

/-- Higher-universe consumer: the same statement in universe `v`. -/
example {R S S' : Type v} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S' :=
  IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map

/-- Consumer for the local Tor-one criterion with the original binders. -/
example {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : CategoryTheory.Limits.IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M :=
  Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero (S := S) hκ
