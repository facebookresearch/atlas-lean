/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Henselian.EtaleLift
public import MathlibExt.RingTheory.Valuation.Henselian

@[expose] public section

universe u

example {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ ψ : S →ₐ[R] R,
      ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s :=
  HenselianLocalRing.exists_algHom_lift_of_etale S φ

example {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    HenselianLocalRing A :=
  ValuationSubring.henselianLocalRing_of_isAlgClosed A
