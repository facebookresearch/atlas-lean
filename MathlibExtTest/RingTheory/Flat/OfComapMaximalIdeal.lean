/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.OfComapMaximalIdeal

import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

open TensorProduct

example {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M :=
  Module.flat_of_comap_maximalIdeal_rTensor_injective p hp h

/-- The criterion applied to `S` itself as a module, with all types in `Type`. -/
example {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    (h : Function.Injective
      (((IsLocalRing.maximalIdeal S).comap (algebraMap R S)).subtype.rTensor S)) :
    Module.Flat R S :=
  Module.flat_of_comap_maximalIdeal_rTensor_injective (S := S) _ rfl h

/-- A concrete instance: `ℚ` is flat over `ℤ`. The maximal ideal `⊥` of `ℚ` contracts to `⊥`, and
`⊥ ⊗[ℤ] ℚ` is zero. -/
example : Module.Flat ℤ ℚ :=
  Module.flat_of_comap_maximalIdeal_rTensor_injective (S := ℚ) ⊥
    (by rw [IsLocalRing.maximalIdeal_eq_bot,
      Ideal.comap_bot_of_injective _ (algebraMap ℤ ℚ).injective_int])
    (Function.injective_of_subsingleton _)
