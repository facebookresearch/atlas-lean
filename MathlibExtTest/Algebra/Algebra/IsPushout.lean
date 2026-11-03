/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.IsPushout

@[expose] public section

universe u v w x

example {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' :=
  Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq h

-- The four carriers have independent universe parameters.
example {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (h : ∀ (T : Type max v w x) [CommRing T] [Algebra R' T] (g : S →+* T),
      g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
        ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
    Algebra.IsPushout R S R' S' :=
  Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq h

-- A non-vacuous client with the pushout carrier in a strictly larger universe.
example : Algebra.IsPushout ℤ ℤ ℤ (ULift.{1} ℤ) := by
  apply Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq
  intro T _ _ g _
  refine ⟨(Algebra.ofId ℤ T).comp ULift.algEquiv.toAlgHom, ?_, ?_⟩
  · exact Subsingleton.elim _ _
  · intro k _
    apply AlgHom.ext
    rintro ⟨z⟩
    exact k.commutes z
