/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.IsInvariant

@[expose] public section

universe u v w

example {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
    [Algebra.IsInvariant A S G] :
    Function.Injective (AdicCompletion.map I (Algebra.linearMap A S)) ∧
    ∀ x : AdicCompletion I S,
      x ∈ LinearMap.range (AdicCompletion.map I (Algebra.linearMap A S)) ↔
        ∀ g : G, AdicCompletion.map I (DistribSMul.toLinearMap A S g) x = x :=
  AdicCompletion.map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant I

example {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Type v} [CommRing S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S]
    {G : Type w} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
    [Algebra.IsInvariant A S G] (x : AdicCompletion I S)
    (hx : ∀ g : G, AdicCompletion.map I (DistribSMul.toLinearMap A S g) x = x) :
    x ∈ LinearMap.range (AdicCompletion.map I (Algebra.linearMap A S)) :=
  (AdicCompletion.map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant I).2 x |>.mpr hx
