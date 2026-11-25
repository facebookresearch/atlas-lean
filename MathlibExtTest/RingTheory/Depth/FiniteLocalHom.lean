/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Depth.FiniteLocalHom

@[expose] public section

universe u v w

-- The original binders, with depth read in Mathlib style as
-- `IsLocalRing.depth`.
example (R : Type) (S : Type) [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (M : Type) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) :=
  IsLocalRing.depth_eq_depth_of_finite_of_isLocalHom

-- The same statement in higher universes.
example (R : Type 1) (S : Type 1) [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (M : Type 1) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M] :
    IsLocalRing.depth (ModuleCat.of R M) = IsLocalRing.depth (ModuleCat.of S M) :=
  IsLocalRing.depth_eq_depth_of_finite_of_isLocalHom

-- Boundary case: for the zero module both depths are `⊤`, in line with
-- the conclusion.
example (R : Type) (S : Type) [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] :
    IsLocalRing.depth (ModuleCat.of R (Fin 0 → S)) =
      IsLocalRing.depth (ModuleCat.of S (Fin 0 → S)) :=
  IsLocalRing.depth_eq_depth_of_finite_of_isLocalHom
