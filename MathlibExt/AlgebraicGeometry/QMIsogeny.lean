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

public import MathlibExt.AlgebraicGeometry.QMFakeEllipticCurve

/-!
# Isogenies, lattice actions and representability for fake elliptic curves

For a positive integer `d`, a `d`-isogeny pair between fake elliptic
curves is a pair of morphisms over the base, each respecting the group laws
and the action of the subring `Λ`, whose composites are the action of the
element `d` of `Λ`. A single morphism is level-preserving if it
sends level points to level points. The family of such pairs over all base
changes is representable when a point of a scheme `X` over the base
determines the pair, uniquely and naturally, and isomorphisms of the
pullbacks, compatible with their maps to the original curves, that carry
both maps of one pair to both maps of another give the same point. A lattice
action is a unital, multiplicative and additive action of `Λ` alone, without
the rest of a fake elliptic curve; `RepresentsLatticeActions` says that a
scheme represents the functor of lattice actions.

Unlike the source, where `Λ` is a `ℤ`-submodule, `Λ` is a subring, as in
`FakeEllipticCurve`: every integer lies in `Λ`, so the composites of an
isogeny pair are stated without a membership hypothesis, and a lattice
action is unital and multiplicative without membership side conditions.
The integer `d` of an isogeny pair is required to be positive, and the
isomorphism invariance of a representing point family relates the reverse
maps of the two pairs as well as the forward maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Subring ℍ[ℚ,a,b]} {N : ℕ}
  {S : Type u} [CommRing S]

/-- `φ : E.A ⟶ E'.A` and `ψ : E'.A ⟶ E.A` form a `d`-isogeny pair if `d`
is positive, both maps are over the base, preserve the group law on
points and commute with the action of `Λ`, and `φ ≫ ψ` and `ψ ≫ φ` are the
actions of the element `d` of `Λ`. -/
def IsIsogenyPair (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) : Prop :=
  0 < d ∧ ∃ (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E.f), mapPt φ hφ (E.L.mul t P Q) =
        E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E'.f), mapPt ψ hψ (E'.L.mul t P Q) =
        E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
    (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (φ ≫ ψ = E.act (d : ↥Λ) ∧ ψ ≫ φ = E'.act (d : ↥Λ))

/-- The conditions of `IsIsogenyPair` for given proofs `hφ` and `hψ` that
`φ` and `ψ` are over the base: `d` is positive, both maps preserve the group
law on points and commute with the action of `Λ`, and `φ ≫ ψ` and `ψ ≫ φ`
are the actions of the element `d` of `Λ`. -/
def IsIsogenyPairVia (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
    (hψ : ψ ≫ E.f = E'.f) : Prop :=
  0 < d ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t E.f), mapPt φ hφ (E.L.mul t P Q) =
      E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t E'.f), mapPt ψ hψ (E'.L.mul t P Q) =
      E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
  (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
  (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
  (φ ≫ ψ = E.act (d : ↥Λ) ∧ ψ ≫ φ = E'.act (d : ↥Λ))

theorem isIsogenyPair_iff_exists_via (d : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) :
    IsIsogenyPair d E E' φ ψ ↔ ∃ (hφ : φ ≫ E'.f = E.f)
      (hψ : ψ ≫ E.f = E'.f), IsIsogenyPairVia d E E' φ hφ ψ hψ :=
  ⟨fun ⟨hd, hφ, hψ, h⟩ => ⟨hφ, hψ, hd, h⟩,
    fun ⟨hφ, hψ, hd, h⟩ => ⟨hd, hφ, hψ, h⟩⟩

theorem IsIsogenyPair.symm {d : ℕ} {E E' : FakeEllipticCurve Λ N S}
    {φ : E.A ⟶ E'.A} {ψ : E'.A ⟶ E.A}
    (h : IsIsogenyPair d E E' φ ψ) : IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hd, hφ, hψ, hm, hm', ha, ha', hc⟩ := h
  exact ⟨hd, hψ, hφ, hm', hm, ha', ha, hc.symm⟩

/-- Two fake elliptic curves are `d`-isogenous if a `d`-isogeny pair
between them exists. -/
def IsIsogeny (d : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A), IsIsogenyPair d E E' φ ψ

theorem isIsogeny_iff (d : ℕ) (E E' : FakeEllipticCurve Λ N S) :
    IsIsogeny d E E' ↔ ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A),
      IsIsogenyPair d E E' φ ψ := Iff.rfl

theorem IsIsogeny.symm {d : ℕ} {E E' : FakeEllipticCurve Λ N S}
    (h : IsIsogeny d E E') : IsIsogeny d E' E := by
  obtain ⟨φ, ψ, hp⟩ := h
  exact ⟨ψ, φ, hp.symm⟩

/-- Every fake elliptic curve is `1`-isogenous to itself. -/
theorem isIsogeny_one_refl (E : FakeEllipticCurve Λ N S) :
    IsIsogeny 1 E E := by
  refine ⟨𝟙 E.A, 𝟙 E.A, Nat.one_pos, Category.comp_id E.f,
    Category.comp_id E.f, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_id, mapPt_id, mapPt_id]
  · intro T t P Q
    rw [mapPt_id, mapPt_id, mapPt_id]
  · intro x
    rw [Category.id_comp, Category.comp_id]
  · intro x
    rw [Category.id_comp, Category.comp_id]
  · rw [Nat.cast_one, E.act_one]
    exact ⟨Category.comp_id _, Category.comp_id _⟩

/-- A morphism `φ : E.A ⟶ E'.A` over the base preserves the level structure
if, over every test scheme, it maps each level point of `E`, a point that
factors through `E.lev`, to a level point of `E'`. -/
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

/-- An action of the subring `Λ` of `ℍ[ℚ, a, b]` on a scheme `A` over
`Spec S` with a relative group law `L`: a unital, multiplicative and
additive action of `Λ` by endomorphisms over the base that preserve the
group law on points. -/
structure LatticeAction (Λ : Subring ℍ[ℚ,a,b]) {S : Type u}
    [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) : Type u where
  /-- The endomorphism given by an element of `Λ`. -/
  act : ↥Λ → (A ⟶ A)
  /-- Each endomorphism is over the base. -/
  act_over : ∀ x : ↥Λ, act x ≫ f = f
  /-- Each endomorphism is a group homomorphism on points. -/
  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)
  /-- The element `1` of `Λ` acts as the identity. -/
  act_one : act 1 = 𝟙 A
  /-- The action is multiplicative in `Λ`. -/
  act_mul : ∀ x y : ↥Λ, act (x * y) = act y ≫ act x
  /-- The action is additive in `Λ`: `x + y` sends a point to the sum of its
  images under `x` and `y`. -/
  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

namespace LatticeAction

variable {a b : ℚ} {Λ : Subring ℍ[ℚ,a,b]}

@[ext]
theorem ext {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {X Y : LatticeAction Λ f L} (h : X.act = Y.act) : X = Y := by
  cases X; cases Y; cases h; rfl

/-- The lattice action of `Λ` on the group law of a fake elliptic curve `E`
given by the action `E.act` of `Λ` on `E`. -/
def ofFakeEllipticCurve {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : LatticeAction Λ E.f E.L where
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add

@[simp]
theorem ofFakeEllipticCurve_act {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : (ofFakeEllipticCurve E).act = E.act :=
  rfl

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

/-- The group law `L'` on `A'` over `Spec S'` is the pullback of the group
law `L` on `A` over `Spec S` along `g : A' ⟶ A` if `g`, the structure
morphisms and `Spec φ` form a pullback square of schemes and `g` carries the
product of two points for `L'` to the product of their images for `L`. -/
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
              (CommRingCat.ofHom φ))) (V := Over.mk f) (P.left ≫ g)
              (comap_left_comp φ g hg P))
            (Over.homMk (U := Over.mk (t' ≫ Spec.map
              (CommRingCat.ofHom φ))) (V := Over.mk f) (Q.left ≫ g)
              (comap_left_comp φ g hg Q))).left :=
  Iff.rfl

/-- A scheme `E` over `Spec R` represents the functor of lattice actions of
`Λ` on pullbacks of the group law `L` via `cl`, which sends a lattice action
on a pullback of `L` along `φ : R →+* R'` to a point of `E` over `Spec R'`,
if `cl` is natural in the base ring, surjective and injective. -/
structure RepresentsLatticeActions (Λ : Subring ℍ[ℚ,a,b])
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

theorem cl_bijective {Λ : Subring ℍ[ℚ,a,b]} {R : Type u} [CommRing R]
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

variable {a b : ℚ} {Λ : Subring ℍ[ℚ,a,b]} {N : ℕ}

/-- The type of assignments that send each `r ^ d`-isogeny pair `(φ, φ')`
with level-preserving `φ`, between pullbacks `E'` and `A'` of `E` and `A`
along `S → T`, to a point of `X` over `Spec T`, where `ξ : X ⟶ Spec S` is
the structure morphism of `X`. -/
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

/-- A point family represents isogeny pairs if it is invariant under
isomorphisms of the pullbacks, compatible with their maps to `E` and `A`,
that carry both maps of one pair to both maps of the other, natural in the
base ring, surjective, and faithful on both maps of a pair. -/
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
    iA.hom ≫ ψ' = φ' ≫ iE.hom →
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
    (_hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
    (hA : A''.A ⟶ A'.A)
    (_hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
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
        iA.hom ≫ ψ' = φ' ≫ iE.hom →
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
        (_hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
        (hA : A''.A ⟶ A'.A)
        (_hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
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
