/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Etale.Localization
public import MathlibExt.Algebra.Smooth.Localization
public import MathlibExt.Algebra.Etale.AlgHomCount

@[expose] public section

universe u

example (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type u) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type u) [CommRing A_q] [Algebra A A_q]
    [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q :=
  Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime P A q A_q

example (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ]
    [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ :=
  Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R S p Sₚ

example (k : Type*) [Field k] [IsAlgClosed k] (R : Type*) [CommRing R] [Algebra k R]
    [Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R :=
  Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed k R
