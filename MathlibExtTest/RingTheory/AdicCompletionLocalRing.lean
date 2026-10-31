/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.LocalRing

@[expose] public section

open AdicCompletion IsLocalRing

example (A : Type*) [CommRing A] (I : Ideal A) (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) :=
  AdicCompletion.ker_evalₐ_eq_map_pow I hI n

example (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n =
      RingHom.ker (evalₐ (maximalIdeal A) n) :=
  AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ n
