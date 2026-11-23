/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.KrullDimension
public import MathlibExt.RingTheory.IntegrallyClosed.FlatLocalHom

@[expose] public section

universe u v

example (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le R h

example {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] :
    IsDomain R ∧ IsIntegrallyClosed R :=
  IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom (R := R) (S := S)
