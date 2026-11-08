/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RegularLocalRing.QuotientSpanSingleton
public import MathlibExt.RingTheory.RegularLocalRing.IsDomain
public import MathlibExt.RingTheory.LocalRing.UFDQuotient

@[expose] public section

open IsLocalRing

universe u

example (R : Type u) [CommRing R] [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank :=
  IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    R hx hx2 hxmin

example (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧
      ∀ p ∈ minimalPrimes R, x ∉ p :=
  IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem R hdim

example (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

example {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    UniqueFactorizationMonoid A :=
  IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient t
