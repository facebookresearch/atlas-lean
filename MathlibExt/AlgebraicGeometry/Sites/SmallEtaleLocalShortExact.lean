/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Original local short exact sequences on the small étale site

The coefficient universe is independent of the scheme universe. This definition
uses the original sheaf components and covering sieves. It requires neither
sheafification nor an abelian category of sheaves in the coefficient universe.
A covering sieve is the covering family of all its actual arrows.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

variable {X : Scheme.{u}}
  {F' F F'' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
  (a : F' ⟶ F) (b : F ⟶ F'')

/-- The original componentwise left exact condition and actual local lifts for
the last map, on the same small étale site and in the original universe. -/
def originalSmallEtaleLocalShortExact : Prop :=
  (∀ U : X.Etale, Function.Injective (a.hom.app (op U))) ∧
  (∀ U : X.Etale, Set.range (a.hom.app (op U)) =
    {x | b.hom.app (op U) x = 0}) ∧
  ∀ (U : X.Etale) (c : F''.obj.obj (op U)),
    ∃ R : Sieve U, R ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (p : V ⟶ U), R p →
        ∃ d : F.obj.obj (op V), b.hom.app (op V) d = F''.obj.map p.op c

variable {a b}

/-- The literal last map of an original locally short exact sequence is locally
surjective. The covering sieve and every preimage come from its defining data. -/
theorem originalSmallEtaleLocalShortExact_locallySurjective
    (h : originalSmallEtaleLocalShortExact a b) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom where
  imageSieve_mem {U} c := by
    obtain ⟨R, hR, hlift⟩ := h.2.2 U c
    exact X.smallEtaleTopology.superset_covering
      (fun V p hp => hlift V p hp) hR

/-- Conversely, the stock local-surjectivity condition supplies the actual
original covering family of arrows and their local section lifts. -/
theorem originalSmallEtaleLocalShortExact_iff :
    originalSmallEtaleLocalShortExact a b ↔
      (∀ U : X.Etale, Function.Injective (a.hom.app (op U))) ∧
      (∀ U : X.Etale, Set.range (a.hom.app (op U)) =
        {x | b.hom.app (op U) x = 0}) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology b.hom := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, originalSmallEtaleLocalShortExact_locallySurjective h⟩
  · rintro ⟨hinj, hexact, hsurj⟩
    let := hsurj
    refine ⟨hinj, hexact, ?_⟩
    intro U c
    exact ⟨Presheaf.imageSieve b.hom c,
      Presheaf.imageSieve_mem X.smallEtaleTopology b.hom c, fun V p hp => hp⟩

/-- The zero composite follows from the original image=kernel equality; it is
not an extra assumption on the smaller coefficient category. -/
theorem originalSmallEtaleLocalShortExact_comp_eq_zero
    (h : originalSmallEtaleLocalShortExact a b) : a ≫ b = 0 := by
  ext U x
  have hx : a.hom.app U x ∈ Set.range (a.hom.app U) := ⟨x, rfl⟩
  rw [h.2.1 U.unop] at hx
  exact hx

/-- The original arrows with their derived zero-composite, before any
common-universe coefficient lift or homology construction. -/
def originalSmallEtaleLocalShortComplex
    (h : originalSmallEtaleLocalShortExact a b) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :=
  ShortComplex.mk a b (originalSmallEtaleLocalShortExact_comp_eq_zero h)

/-- A morphism of original locally short exact sequences is precisely the
three original sheaf maps with the two original commuting squares. -/
abbrev OriginalSmallEtaleLocalShortExactHom
    (h : originalSmallEtaleLocalShortExact a b)
    {G' G G'' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    {a' : G' ⟶ G} {b' : G ⟶ G''}
    (h' : originalSmallEtaleLocalShortExact a' b') :=
  originalSmallEtaleLocalShortComplex h ⟶ originalSmallEtaleLocalShortComplex h'

end AlgebraicGeometry.Scheme.DerivedSections
