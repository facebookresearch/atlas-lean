/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_QMModuli.lean`,
`Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean` and
`Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean`
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

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.KrullDimension
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.SchemeHomOver

/-!
# Quaternion-multiplication fake elliptic curves

A fake elliptic curve over a commutative ring `S` is a scheme over
`Spec S` with a commutative relative group law, an action of an order
`Λ` in a quaternion algebra over `ℚ` by group endomorphisms satisfying
the trace identity on tangent spaces, and a level structure given by a
closed immersion whose points are the `N`-torsion points of rank `N²`.
Points over a test scheme, pushforward of points, multiples of points
and tangent vectors over dual numbers are defined first, in terms of
morphisms in the over category.

Unlike the source, `Λ` is a subring, so the order acts unitally and
multiplicatively without membership side conditions, and Hecke
neighbours are taken at a prime `ℓ`. The fibres are required to be
geometrically connected; the source's property bundle asks for connected
fibres, which is equivalent here because the identity section gives
every fibre a rational point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace CerednikDrinfeld.QM

variable {R : Type u} [CommRing R]

/-- Push a point forward along a morphism over the base. -/
def mapPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  P ≫ Over.homMk φ hφ

@[simp]
theorem mapPt_left {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : (mapPt φ hφ P).left = P.left ≫ φ := rfl

/-- Push a point forward along an endomorphism over the base. -/
abbrev pushPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A) (hφ : φ ≫ f = f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    SchemeHomOver t f :=
  mapPt φ hφ P

/-- Reindex a point along a morphism of test schemes. -/
def compPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t f) : SchemeHomOver t' f :=
  Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ P

@[simp]
theorem compPt_left {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t f) : (compPt ψ hψ P).left = ψ ≫ P.left := by
  simp [compPt]

/-- A point factors through a level morphism `lev : C ⟶ A`. -/
def FactorsThrough {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (lev : C ⟶ A) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : Prop :=
  ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.left

theorem factorsThrough_iff {A C : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (lev : C ⟶ A) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    FactorsThrough lev P ↔ ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.left := Iff.rfl

/-- The `n`-fold sum of a point for a relative group law. -/
def nsmulPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    ℕ → SchemeHomOver t f → SchemeHomOver t f
  | 0, _ => L.one t
  | n + 1, P => L.mul t (nsmulPt L t n P) P

@[simp]
theorem nsmulPt_zero {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    nsmulPt L t 0 P = L.one t := rfl

@[simp]
theorem nsmulPt_succ {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + 1) P = L.mul t (nsmulPt L t n P) P := rfl

/-- Commutativity of a relative group law. -/
def IsCommutativeLaw {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver t f), L.mul t P Q = L.mul t Q P

theorem IsCommutativeLaw.mul_comm {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {L : RelativeGroupLaw R f}
    (h : IsCommutativeLaw L) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    L.mul t P Q = L.mul t Q P :=
  h t P Q

variable {S : Type u} [CommRing S]

/-- The geometric point of `Spec S` at a map to a field. -/
def geomPoint (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom sk)

/-- The dual-number thickening of a geometric point. -/
def tangentBase (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp sk))

/-- The zero section of the dual-number thickening. -/
def tangentZero (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

/-- Scaling the dual-number coordinate by `c`. -/
def tangentScale (k : Type u) [Field k] (c : k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶
      Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)

/-- A point over dual numbers is a tangent vector if it reduces to the
identity point. -/
def IsTangentVector {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (k : Type u) [Field k] (sk : S →+* k)
    (P : SchemeHomOver (tangentBase k sk) f) : Prop :=
  tangentZero k ≫ P.left = (L.one (geomPoint k sk)).left

theorem isTangentVector_iff {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (k : Type u) [Field k] (sk : S →+* k)
    (P : SchemeHomOver (tangentBase k sk) f) :
    IsTangentVector L k sk P ↔
      tangentZero k ≫ P.left = (L.one (geomPoint k sk)).left := Iff.rfl

variable {a b : ℚ}

/-- A fake elliptic curve over `S`: a two-dimensional abelian-scheme-like
object with quaternion multiplication by the order `Λ` and level-`N`
structure. The fields are the data and axioms of the notion; the
characterization lemmas below restate isomorphisms, pullbacks and
neighbours in terms of an explicit mediating isomorphism or morphism. -/
structure FakeEllipticCurve (Λ : Subring ℍ[ℚ, a, b]) (N : ℕ)
    (S : Type u) [CommRing S] : Type (u + 1) where
  /-- The underlying scheme. -/
  A : Scheme.{u}
  /-- The structure morphism. -/
  f : A ⟶ Spec (CommRingCat.of S)
  /-- The relative group law. -/
  L : RelativeGroupLaw S f
  /-- The group law is commutative. -/
  comm : IsCommutativeLaw L
  /-- The structure morphism is smooth. -/
  smooth : Smooth f
  /-- The structure morphism is proper. -/
  proper : IsProper f
  /-- The fibres are geometrically connected. -/
  connected : GeometricallyConnected f
  /-- Every fibre has Krull dimension two. -/
  dim_fibre : ∀ s : ↥(Spec (CommRingCat.of S)),
    topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2
  /-- The action of the order `Λ`. -/
  act : ↥Λ → (A ⟶ A)
  /-- The action is over the base. -/
  act_over : ∀ x : ↥Λ, act x ≫ f = f
  /-- The action acts by group homomorphisms on points. -/
  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)
  /-- The element `1` of the order acts as the identity. -/
  act_one : act 1 = 𝟙 A
  /-- The action is multiplicative in the order. -/
  act_mul : ∀ x y : ↥Λ, act (x * y) = act y ≫ act x
  /-- The action is additive on points. -/
  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)
  /-- The trace of the action on tangent spaces is the quaternion trace. -/
  act_trace : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) f),
    Function.Injective τ →
    (∀ P : SchemeHomOver (tangentBase k sk) f,
      P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
    (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
    (∀ (c : k) (v : V), (τ (c • v)).left = tangentScale k c ≫ (τ v).left) →
    ∀ (m : ↥Λ) (Φ : V →ₗ[k] V),
    (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
    ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) =
      ((n : ℚ) : ℍ[ℚ, a, b]) → LinearMap.trace k V Φ = (n : k)
  /-- The level scheme. -/
  C : Scheme.{u}
  /-- The level morphism. -/
  lev : C ⟶ A
  /-- The level morphism is a closed immersion. -/
  lev_closed : IsClosedImmersion lev
  /-- Level points form a subgroup. -/
  lev_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t f), FactorsThrough lev P →
    FactorsThrough lev Q →
    FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P)
  /-- The identity is a level point. -/
  lev_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
    FactorsThrough lev (L.one t)
  /-- Level points are `N`-torsion. -/
  lev_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t f), FactorsThrough lev P →
    nsmulPt L t N P = L.one t
  /-- Level points are stable under the order action. -/
  lev_stable : ∀ (x : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    FactorsThrough lev P → FactorsThrough lev (pushPt (act x) (act_over x) P)
  /-- The level morphism is finite over the base. -/
  lev_finite : IsFinite (lev ≫ f)
  /-- The level morphism is flat over the base. -/
  lev_flat : Flat (lev ≫ f)
  /-- The level morphism is locally of finite presentation over the base. -/
  lev_finitePresentation : LocallyOfFinitePresentation (lev ≫ f)
  /-- The level morphism has rank `N ^ 2`. -/
  lev_rank : ∀ s : ↥(Spec (CommRingCat.of S)), (lev ≫ f).finrank s = N ^ 2
  /-- Geometric level points are `ZMod N × ZMod N` as a group. -/
  lev_fibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    (N : k) ≠ 0 →
    ∃ e : ZMod N × ZMod N ≃
      {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
      ∀ x y : ZMod N × ZMod N,
        (e (x + y) : SchemeHomOver (geomPoint k sk) f) =
          L.mul (geomPoint k sk) (e x) (e y)

namespace FakeEllipticCurve

variable {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}

/-- The pushforward of a point along the action of `x`. -/
theorem act_hom_apply {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (x : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) (E.L.mul t P Q) =
      E.L.mul t (pushPt (E.act x) (E.act_over x) P)
        (pushPt (E.act x) (E.act_over x) Q) :=
  E.act_hom x t P Q

/-- An isomorphism of fake elliptic curves, as a predicate. -/
def Iso {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S) :
    Prop :=
  ∃ (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) =
        E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom he P))

/-- The same isomorphism condition, for a named mediating isomorphism. -/
def IsoVia {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f) : Prop :=
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t E.f),
    mapPt e.hom he (E.L.mul t P Q) =
      E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
  (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f),
    FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt e.hom he P))

theorem iso_iff_exists_via {S : Type u} [CommRing S]
    (E E' : FakeEllipticCurve Λ N S) :
    Iso E E' ↔ ∃ (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f),
      IsoVia E E' e he := Iff.rfl

@[simp]
theorem mapPt_id {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) :
    mapPt (𝟙 E.A) (Category.comp_id E.f) P = P := by
  apply Over.OverMorphism.ext
  show P.left ≫ 𝟙 E.A = P.left
  exact Category.comp_id _

theorem iso_refl {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    Iso E E := by
  have hid : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t E.f),
      mapPt (Iso.refl E.A).hom (Category.comp_id E.f) P = P := by
    intro T t P
    apply Over.OverMorphism.ext
    show P.left ≫ 𝟙 E.A = P.left
    exact Category.comp_id _
  refine ⟨Iso.refl E.A, Category.comp_id E.f, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [hid, hid, hid]
  · intro x
    simp
  · intro T t P
    have hm : (mapPt (Iso.refl E.A).hom (Category.comp_id E.f) P).left =
        P.left := Category.comp_id _
    constructor
    · rintro ⟨P₀, hP₀⟩
      exact ⟨P₀, by rw [hP₀, hm]⟩
    · rintro ⟨P₀, hP₀⟩
      exact ⟨P₀, by rw [hP₀, hm]⟩

/-- A point of `E'` transported to `E` along a pullback square. -/
def comapPt {S S' : Type u} [CommRing S] [CommRing S']
    {φ : S →+* S'} {E : FakeEllipticCurve Λ N S}
    {E' : FakeEllipticCurve Λ N S'} (g : E'.A ⟶ E.A)
    (hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
  Over.homMk (U := Over.mk (t' ≫ Spec.map (CommRingCat.ofHom φ)))
    (V := Over.mk E.f) (P.left ≫ g) (by
    have hwP : P.left ≫ E'.f = t' := Over.w P
    have hw : P.left ≫ g ≫ E.f =
        t' ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [hg.w, ← Category.assoc, hwP]
    exact hw)

/-- Pullback of fake elliptic curves along a ring map, for a named map. -/
def IsPullbackVia {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') (E : FakeEllipticCurve Λ N S)
    (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A) : Prop :=
  ∃ hg : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P Q : SchemeHomOver t' E'.f),
      (E'.L.mul t' P Q).left ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          (comapPt g hg P) (comapPt g hg Q)).left) ∧
    (∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x) ∧
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P : SchemeHomOver t' E'.f), FactorsThrough E'.lev P →
      ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.left ≫ g)

/-- Pullback of fake elliptic curves along a ring map. -/
def IsPullback {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') (E : FakeEllipticCurve Λ N S)
    (E' : FakeEllipticCurve Λ N S') : Prop :=
  ∃ g : E'.A ⟶ E.A, IsPullbackVia φ E E' g

theorem isPullback_iff_exists_via {S S' : Type u} [CommRing S]
    [CommRing S'] (φ : S →+* S') (E : FakeEllipticCurve Λ N S)
    (E' : FakeEllipticCurve Λ N S') :
    IsPullback φ E E' ↔ ∃ g : E'.A ⟶ E.A, IsPullbackVia φ E E' g :=
  Iff.rfl

/-- Hecke neighbours at a prime `ℓ`: an isogeny-like pair with both level
structures preserved and both composites given by the action of `ℓ`,
neither map an isomorphism. -/
def HeckeNeighbour {S : Type u} [CommRing S] (ℓ : ℕ)
    (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ℓ.Prime ∧
  ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
    (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E.f), mapPt φ hφ (E.L.mul t P Q) =
        E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t E'.f), mapPt ψ hψ (E'.L.mul t P Q) =
        E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
    (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t E.f), FactorsThrough E.lev P →
      FactorsThrough E'.lev (mapPt φ hφ P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t E'.f), FactorsThrough E'.lev P →
      FactorsThrough E.lev (mapPt ψ hψ P)) ∧
    (φ ≫ ψ = E.act (ℓ : ↥Λ) ∧ ψ ≫ φ = E'.act (ℓ : ↥Λ)) ∧
    ¬ IsIso φ ∧ ¬ IsIso ψ

theorem heckeNeighbour_symm {S : Type u} [CommRing S] {ℓ : ℕ}
    {E E' : FakeEllipticCurve Λ N S} (h : HeckeNeighbour ℓ E E') :
    HeckeNeighbour ℓ E' E := by
  obtain ⟨hℓ, φ, hφ, ψ, hψ, hm, hm', ha, ha', hl, hl', hc, hni, hnj⟩ := h
  exact ⟨hℓ, ψ, hψ, φ, hφ, hm', hm, ha', ha, hl', hl, hc.symm, hnj, hni⟩

end FakeEllipticCurve

end CerednikDrinfeld.QM
