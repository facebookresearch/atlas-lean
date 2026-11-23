/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_QMIsogeny.lean`,
`Definitions/Def_CerednikDrinfeld_QMIsogenyPairRep.lean` and
`Definitions/Def_CerednikDrinfeld_QMLatticeAction.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import MathlibExt.AlgebraicGeometry.QMFakeEllipticCurve

/-!
# Isogenies, lattice actions and representability for fake elliptic curves

An isogeny pair between fake elliptic curves is a pair of morphisms over
the base, each respecting the group laws and the quaternion action, whose
composites are the action of a positive integer `d` from the order. A
single morphism is level-preserving if it sends level points to level
points. The family of such pairs over all base changes is representable
when a point of a scheme `X` over the base determines the pair, uniquely
and naturally. A lattice action is the action of the order alone, without
the rest of a fake elliptic curve; the final predicate says that a scheme
represents the functor of lattice actions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {S : Type u} [CommRing S]

/-- A pair of morphisms forming a `d`-isogeny between fake elliptic
curves. -/
def IsIsogenyPair (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) : Prop :=
  ∃ (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E.f), mapPt φ hφ (E.L.mul t P Q) =
        E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E'.f), mapPt ψ hψ (E'.L.mul t P Q) =
        E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
    (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hd : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ∧
        ψ ≫ φ = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩)

/-- Characterization of an isogeny pair with named over-base proofs. -/
def IsIsogenyPairVia (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
    (hψ : ψ ≫ E.f = E'.f) : Prop :=
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t E.f), mapPt φ hφ (E.L.mul t P Q) =
      E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t E'.f), mapPt ψ hψ (E'.L.mul t P Q) =
      E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
  (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
  (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
  (∀ hd : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
    φ ≫ ψ = E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ∧
      ψ ≫ φ = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩)

theorem isIsogenyPair_iff_exists_via (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) :
    IsIsogenyPair d E E' φ ψ ↔ ∃ (hφ : φ ≫ E'.f = E.f)
      (hψ : ψ ≫ E.f = E'.f), IsIsogenyPairVia d E E' φ hφ ψ hψ := Iff.rfl

theorem IsIsogenyPair.symm {d : ℕ} {E E' : FakeEllipticCurve Λ N S}
    {φ : E.A ⟶ E'.A} {ψ : E'.A ⟶ E.A}
    (h : IsIsogenyPair d E E' φ ψ) : IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hφ, hψ, hm, hm', ha, ha', hc⟩ := h
  exact ⟨hψ, hφ, hm', hm, ha', ha, fun hd => (hc hd).symm⟩

/-- Two fake elliptic curves are `d`-isogenous if an isogeny pair exists. -/
def IsIsogeny (d : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A), IsIsogenyPair d E E' φ ψ

theorem isIsogeny_iff (d : ℕ) (E E' : FakeEllipticCurve Λ N S) :
    IsIsogeny d E E' ↔ ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A),
      IsIsogenyPair d E E' φ ψ := Iff.rfl

theorem IsIsogeny.symm {d : ℕ} {E E' : FakeEllipticCurve Λ N S}
    (h : IsIsogeny d E E') : IsIsogeny d E' E := by
  obtain ⟨φ, ψ, hp⟩ := h
  exact ⟨ψ, φ, hp.symm⟩

/-- The identity pair is a `1`-isogeny of a fake elliptic curve with
itself. -/
theorem isIsogeny_one_refl (E : FakeEllipticCurve Λ N S) :
    IsIsogeny 1 E E := by
  refine ⟨𝟙 E.A, 𝟙 E.A, Category.comp_id E.f, Category.comp_id E.f,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_id, mapPt_id, mapPt_id]
  · intro T t P Q
    rw [mapPt_id, mapPt_id, mapPt_id]
  · intro x
    rw [Category.id_comp, Category.comp_id]
  · intro x
    rw [Category.id_comp, Category.comp_id]
  · intro hd
    have hd' : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hd
    have hact : E.act ⟨(((1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hd⟩ = 𝟙 E.A :=
      E.act_one hd'
    rw [hact]
    exact ⟨Category.comp_id _, Category.comp_id _⟩

/-- A morphism over the base preserves the level structure. -/
def PreservesLevel (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A)
    (hφ : φ ≫ E'.f = E.f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f), FactorsThrough E.lev P →
    FactorsThrough E'.lev (mapPt φ hφ P)

theorem preservesLevel_iff (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) :
    PreservesLevel E E' φ hφ ↔ ∀ {T : Scheme.{u}}
      (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P →
      FactorsThrough E'.lev (mapPt φ hφ P) := Iff.rfl

theorem preservesLevel_id (E : FakeEllipticCurve Λ N S) :
    PreservesLevel E E (𝟙 E.A) (Category.comp_id E.f) := by
  intro T t P hP
  rwa [mapPt_id]

end FakeEllipticCurve

variable {a b : ℚ}

/-- An action of the order `Λ` on a scheme with a relative group law. -/
structure LatticeAction (Λ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type u}
    [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) : Type u where
  /-- The endomorphism given by an element of the order. -/
  act : ↥Λ → (A ⟶ A)
  /-- Each endomorphism is over the base. -/
  act_over : ∀ x : ↥Λ, act x ≫ f = f
  /-- Each endomorphism is a group homomorphism on points. -/
  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)
  /-- The element `1` acts as the identity. -/
  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A
  /-- The action is multiplicative in the order. -/
  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x
  /-- The action is additive on points. -/
  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

namespace LatticeAction

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

@[ext]
theorem ext {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {X Y : LatticeAction Λ f L} (h : X.act = Y.act) : X = Y := by
  cases X; cases Y; cases h; rfl

theorem eq_iff_act {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    (X Y : LatticeAction Λ f L) : X = Y ↔ X.act = Y.act :=
  ⟨fun h => by rw [h], fun h => ext h⟩

/-- The lattice action underlying a fake elliptic curve. -/
def ofFakeEllipticCurve {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : LatticeAction Λ E.f E.L where
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add

theorem ofFakeEllipticCurve_act {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : (ofFakeEllipticCurve E).act = E.act :=
  rfl

theorem ofFakeEllipticCurve_eq_iff {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (X : LatticeAction Λ E.f E.L) :
    ofFakeEllipticCurve E = X ↔ E.act = X.act :=
  eq_iff_act _ _

end LatticeAction

theorem comap_left_comp {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')} (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' f') :
    (P.left ≫ g) ≫ f = t' ≫ Spec.map (CommRingCat.ofHom φ) := by
  have hwP : P.left ≫ f' = t' := Over.w P
  rw [Category.assoc, hg.w, ← Category.assoc, hwP]

/-- A group law is the pullback of another along `g`, compatibly with the
base map. -/
def IsGroupPullback {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f')
    (g : A' ⟶ A) : Prop :=
  ∃ hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)),
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).left ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          (Over.homMk (U := Over.mk (t' ≫ Spec.map (CommRingCat.ofHom φ)))
            (V := Over.mk f) (P.left ≫ g) (comap_left_comp φ g hg P))
          (Over.homMk (U := Over.mk (t' ≫ Spec.map (CommRingCat.ofHom φ)))
            (V := Over.mk f) (Q.left ≫ g) (comap_left_comp φ g hg Q))).left

theorem isGroupPullback_iff {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f')
    (g : A' ⟶ A) :
    IsGroupPullback φ L L' g ↔ ∃ hg : IsPullback g f' f
      (Spec.map (CommRingCat.ofHom φ)),
      ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
        (P Q : SchemeHomOver t' f'),
        (L'.mul t' P Q).left ≫ g =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            (Over.homMk (U := Over.mk (t' ≫ Spec.map
              (CommRingCat.ofHom φ))) (V := Over.mk f) (P.left ≫ g) (comap_left_comp φ g hg P))
            (Over.homMk (U := Over.mk (t' ≫ Spec.map
              (CommRingCat.ofHom φ))) (V := Over.mk f) (Q.left ≫ g) (comap_left_comp φ g hg Q))).left :=
  Iff.rfl

/-- A scheme `E` over `R` represents the functor of lattice actions: the
assignment `cl` is natural in the base ring and bijective. This is a
structure of properties of `cl`, characterized field by field below. -/
structure RepresentsLatticeActions (Λ : Submodule ℤ ℍ[ℚ, a, b])
    {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (E : Scheme.{u}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}}
      {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
      (g : A' ⟶ A), IsGroupPullback φ L L' g → LatticeAction Λ f' L' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE) : Prop where
  /-- The assignment is natural in the base ring. -/
  cl_comp : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R')
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L' : RelativeGroupLaw R' f') (g : A' ⟶ A)
    (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L')
    (R'' : Type u) [CommRing R''] (ψ : R' →+* R'') {A'' : Scheme.{u}}
    {f'' : A'' ⟶ Spec (CommRingCat.of R'')} (L'' : RelativeGroupLaw R'' f'')
    (g'' : A'' ⟶ A) (hg'' : IsGroupPullback (ψ.comp φ) L L'' g'')
    (X'' : LatticeAction Λ f'' L'') (h : A'' ⟶ A'),
    IsGroupPullback ψ L' L'' h → h ≫ g = g'' →
    (∀ x : ↥Λ, X''.act x ≫ h = h ≫ X'.act x) →
    (cl R'' (ψ.comp φ) L'' g'' hg'' X'').left =
      Spec.map (CommRingCat.ofHom ψ) ≫ (cl R' φ L' g hg X').left
  /-- Every point comes from a lattice action. -/
  cl_surjective : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R')
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L' : RelativeGroupLaw R' f') (g : A' ⟶ A)
    (hg : IsGroupPullback φ L L' g)
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE),
    ∃ X' : LatticeAction Λ f' L', cl R' φ L' g hg X' = s
  /-- Distinct lattice actions give distinct points. -/
  cl_injective : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R')
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L' : RelativeGroupLaw R' f') (g : A' ⟶ A)
    (hg : IsGroupPullback φ L L' g) (X₁ X₂ : LatticeAction Λ f' L'),
    cl R' φ L' g hg X₁ = cl R' φ L' g hg X₂ → X₁ = X₂

namespace RepresentsLatticeActions

variable {a b : ℚ}

theorem cl_bijective {Λ : Submodule ℤ ℍ[ℚ, a, b]} {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {E : Scheme.{u}}
    {πE : E ⟶ Spec (CommRingCat.of R)} {cl : ∀ (R' : Type u) [CommRing R']
      (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A), IsGroupPullback φ L L' g →
      LatticeAction Λ f' L' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}
    (h : RepresentsLatticeActions Λ L E πE cl) (R' : Type u) [CommRing R']
    (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L' : RelativeGroupLaw R' f') (g : A' ⟶ A)
    (hg : IsGroupPullback φ L L' g) :
    Function.Bijective (cl R' φ L' g hg) :=
  ⟨fun X₁ X₂ hX => h.cl_injective R' φ L' g hg X₁ X₂ hX,
    h.cl_surjective R' φ L' g hg⟩

end RepresentsLatticeActions

namespace FakeEllipticCurve.IsogenyPair

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

/-- The point-valued functor of isogeny pairs of exponent `r ^ d` between
two fixed fake elliptic curves, pointed by a morphism `ξ` to the base. -/
abbrev PtFamily (r d : ℕ) {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {X : Scheme.{0}}
    (ξ : X ⟶ Spec (CommRingCat.of S)) : Type 1 :=
  ∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
    (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A)
    (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
    FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' →
    FakeEllipticCurve.PreservesLevel E' A' φ hφ →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ

/-- A point family represents isogeny pairs: it is invariant under
isomorphism, natural in the base ring, surjective and faithful. -/
def RepresentsOn (r d : ℕ) {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {X : Scheme.{0}}
    (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : PtFamily r d E A ξ) : Prop :=
  (∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
    (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A)
    (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
    (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
    (gA'' : A''.A ⟶ A.A)
    (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
    (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
    (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
    (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
    (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f)
    (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
    FakeEllipticCurve.IsoVia E' E'' iE hiE →
    FakeEllipticCurve.IsoVia A' A'' iA hiA → iE.hom ≫ gE'' = gE →
    iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
    pt T E' A' gE hgE gA hgA φ φ' hφ hp hl =
      pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm) ∧
  (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T']
    [Algebra S T'] (f : T →ₐ[S] T')
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
    (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A)
    (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
    (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A)
    (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
    (hA : A''.A ⟶ A'.A)
    (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E''
      (hE ≫ gE))
    (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A''
      (hA ≫ gA))
    (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
    (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
    (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
    ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
    (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq hm).left =
      Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫
        (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).left) ∧
  (∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
    (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A)
    (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
    ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
      (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
      (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
      pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z) ∧
  (∀ (T : Type) [CommRing T] [Algebra S T]
    (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
    (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
    (gA : A'.A ⟶ A.A)
    (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
    (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
    (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
    (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
    (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
    (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂')
    (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
    pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ =
      pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ → φ₁ = φ₂ ∧ φ₁' = φ₂')

theorem representsOn_iff (r d : ℕ) {S : Type} [CommRing S]
    (E A : FakeEllipticCurve Λ N S) {X : Scheme.{0}}
    (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : PtFamily r d E A ξ) :
    RepresentsOn r d E A ξ pt ↔
      (∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
        (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
        (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A)
        (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E''
          gE'')
        (gA'' : A''.A ⟶ A.A)
        (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A''
          gA'')
        (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
        (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
        (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
        (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f)
        (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
        FakeEllipticCurve.IsoVia E' E'' iE hiE →
        FakeEllipticCurve.IsoVia A' A'' iA hiA → iE.hom ≫ gE'' = gE →
        iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
        pt T E' A' gE hgE gA hgA φ φ' hφ hp hl =
          pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T']
        [Algebra S T'] (f : T →ₐ[S] T')
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
        (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
        (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A)
        (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
        (hA : A''.A ⟶ A'.A)
        (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
        (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E''
          (hE ≫ gE))
        (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A''
          (hA ≫ gA))
        (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
        (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
        (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
        ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
        (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq
          hm).left =
          Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫
            (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).left) ∧
      (∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (z : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
        ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
          pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z) ∧
      (∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
        (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
        (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
        (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
        (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂')
        (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
        pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ =
          pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ →
          φ₁ = φ₂ ∧ φ₁' = φ₂') := Iff.rfl

end FakeEllipticCurve.IsogenyPair

end CerednikDrinfeld.QM
