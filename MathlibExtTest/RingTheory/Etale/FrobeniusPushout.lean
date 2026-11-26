/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.FrobeniusPushout

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

private theorem exactSource
    {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    {φ : A →+* B} (hφ : φ.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) :=
  RingHom.Etale.isPushout_frobenius p hφ

-- Higher-universe consumer.
example
    {A B : Type v} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    {φ : A →+* B} (hφ : φ.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) :=
  RingHom.Etale.isPushout_frobenius p hφ

-- Boundary: the identity étale map gives the Frobenius pushout square.
example (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom (RingHom.id A))
      (CommRingCat.ofHom (RingHom.id A)) (CommRingCat.ofHom (frobenius A p)) :=
  RingHom.Etale.isPushout_frobenius p
    (RingHom.Etale.of_bijective Function.bijective_id)
