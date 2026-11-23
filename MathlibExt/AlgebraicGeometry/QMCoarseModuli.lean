/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_QMCoarseModuli.lean`,
`Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`,
`Definitions/Def_CerednikDrinfeld_QMFineModuliT.lean` and
`Definitions/Def_CerednikDrinfeld_QMModuliProps.lean`
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
# Coarse and fine moduli for fake elliptic curves

A coarse moduli scheme for fake elliptic curves is a scheme with a
point assignment that is invariant under isomorphism, natural under
pullback, bijective on geometric points, and universal among such
assignments. Adding an extra level structure, a full level-`m` section,
or both gives the variants with extra level, the fine moduli notion, and
the notions with a twist action of a group on the fine moduli scheme.
Each predicate is a structure of properties, with a characterization
lemma restating it as the conjunction of its fields.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  {S : Type u} [CommRing S]

/-- An extra level-`ℓ` structure: a second finite flat closed level
subgroup, disjoint from the level-`N` structure except at the identity. -/
structure ExtraLevel (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) :
    Type (u + 1) where
  /-- The extra level scheme. -/
  K : Scheme.{u}
  /-- The extra level morphism. -/
  levK : K ⟶ E.A
  /-- The extra level morphism is a closed immersion. -/
  levK_closed : IsClosedImmersion levK
  /-- Extra level points form a subgroup. -/
  levK_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t E.f), FactorsThrough levK P →
    FactorsThrough levK Q → FactorsThrough levK (E.L.mul t P Q) ∧
    FactorsThrough levK (E.L.inv t P)
  /-- The identity is an extra level point. -/
  levK_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
    FactorsThrough levK (E.L.one t)
  /-- Extra level points are `ℓ`-torsion. -/
  levK_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f), FactorsThrough levK P →
    nsmulPt E.L t ℓ P = E.L.one t
  /-- Extra level points are stable under the order action. -/
  levK_stable : ∀ (x : ↥Λ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P →
    FactorsThrough levK (pushPt (E.act x) (E.act_over x) P)
  /-- The two level structures meet only at the identity. -/
  levK_disjoint : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f), FactorsThrough levK P →
    FactorsThrough E.lev P → P = E.L.one t
  /-- The extra level morphism is finite over the base. -/
  levK_finite : IsFinite (levK ≫ E.f)
  /-- The extra level morphism is flat over the base. -/
  levK_flat : Flat (levK ≫ E.f)
  /-- The extra level morphism is locally of finite presentation. -/
  levK_finitePresentation : LocallyOfFinitePresentation (levK ≫ E.f)
  /-- The extra level morphism has rank `ℓ ^ 2`. -/
  levK_rank : ∀ s : ↥(Spec (CommRingCat.of S)),
    (levK ≫ E.f).finrank s = ℓ ^ 2
  /-- Geometric extra level points are `ZMod ℓ × ZMod ℓ` as a group. -/
  levK_fibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    (ℓ : k) ≠ 0 →
    ∃ e : ZMod ℓ × ZMod ℓ ≃
      {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough levK P},
      ∀ x y : ZMod ℓ × ZMod ℓ,
        (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) =
          E.L.mul (geomPoint k sk) (e x) (e y)

/-- A fake elliptic curve with an extra level-`ℓ` structure. -/
abbrev WithExtraLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.ExtraLevel ℓ

/-- Isomorphism of fake elliptic curves with extra level. -/
def WithExtraLevel.Iso {ℓ : ℕ} (u v : WithExtraLevel Λ N ℓ S) : Prop :=
  ∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t u.1.f), mapPt e.hom he (u.1.L.mul t P Q) =
        v.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ v.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P ↔
        FactorsThrough v.1.lev (mapPt e.hom he P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t u.1.f), FactorsThrough u.2.levK P ↔
        FactorsThrough v.2.levK (mapPt e.hom he P))

/-- Pullback of extra-level objects, for a named mediating morphism. -/
def WithExtraLevel.IsPullback {S' : Type u} [CommRing S']
    (φ : S →+* S') {ℓ : ℕ} (u : WithExtraLevel Λ N ℓ S)
    (u' : WithExtraLevel Λ N ℓ S') : Prop :=
  ∃ (g : u'.1.A ⟶ u.1.A)
    (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P Q : SchemeHomOver t' u'.1.f),
      (u'.1.L.mul t' P Q).left ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          (comapPt g hg P) (comapPt g hg Q)).left) ∧
    (∀ x : ↥Λ, u'.1.act x ≫ g = g ≫ u.1.act x) ∧
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P : SchemeHomOver t' u'.1.f),
      (FactorsThrough u'.1.lev P →
        ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.left ≫ g) ∧
      (FactorsThrough u'.2.levK P →
        ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.left ≫ g))

/-- Level restriction: the underlying curve is isomorphic to `d`. -/
def IsLevelRestrict {ℓ : ℕ} (u : WithExtraLevel Λ N ℓ S)
    (d : FakeEllipticCurve Λ N S) : Prop :=
  FakeEllipticCurve.Iso u.1 d

theorem isLevelRestrict_iff {ℓ : ℕ} (u : WithExtraLevel Λ N ℓ S)
    (d : FakeEllipticCurve Λ N S) :
    IsLevelRestrict u d ↔ FakeEllipticCurve.Iso u.1 d := Iff.rfl

/-- The level isogeny from an extra-level object to `d`, of degree `ℓ`. -/
def IsLevelIsogeny (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S)
    (d : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A)
    (hψ : ψ ≫ u.1.f = d.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t u.1.f), mapPt φ hφ (u.1.L.mul t P Q) =
        d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t d.f), mapPt ψ hψ (d.L.mul t P Q) =
        u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ d.act x) ∧
    (∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧
        ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t u.1.f), mapPt φ hφ P = d.L.one t ↔
        FactorsThrough u.2.levK P) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P →
        FactorsThrough d.lev (mapPt φ hφ P))

/-- The level isogeny condition for named mediating morphisms. -/
def IsLevelIsogenyVia (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S)
    (d : FakeEllipticCurve Λ N S) (φ : u.1.A ⟶ d.A)
    (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A)
    (hψ : ψ ≫ u.1.f = d.f) : Prop :=
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t u.1.f), mapPt φ hφ (u.1.L.mul t P Q) =
      d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t d.f), mapPt ψ hψ (d.L.mul t P Q) =
      u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
  (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ d.act x) ∧
  (∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ u.1.act x) ∧
  (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
    φ ≫ ψ = u.1.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧
      ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t u.1.f), mapPt φ hφ P = d.L.one t ↔
      FactorsThrough u.2.levK P) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P →
      FactorsThrough d.lev (mapPt φ hφ P))

theorem isLevelIsogeny_iff_exists_via (ℓ : ℕ)
    (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) :
    IsLevelIsogeny ℓ u d ↔ ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f)
      (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f),
      IsLevelIsogenyVia ℓ u d φ hφ ψ hψ := Iff.rfl

/-- The Atkin--Lehner quotient at `r`, as a predicate. -/
def IsAtkinLehnerQuotient (r : ℕ) (E E' : FakeEllipticCurve Λ N S) :
    Prop :=
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
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧
        ψ ≫ φ = E'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t E.f), mapPt φ hφ P = E'.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ),
          (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) =
            (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (E.act m) (E.act_over m) P = E.L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t E.f), FactorsThrough E.lev P →
        FactorsThrough E'.lev (mapPt φ hφ P))

/-- The Atkin--Lehner quotient condition for named mediating morphisms. -/
def IsAtkinLehnerQuotientVia (r : ℕ) (E E' : FakeEllipticCurve Λ N S)
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
  (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
    φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧
      ψ ≫ φ = E'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f), mapPt φ hφ P = E'.L.one t ↔
      ∀ (m : ↥Λ) (n : ℤ),
        (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) =
          (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m) (E.act_over m) P = E.L.one t) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f), FactorsThrough E.lev P →
      FactorsThrough E'.lev (mapPt φ hφ P))

theorem isAtkinLehnerQuotient_iff_exists_via (r : ℕ)
    (E E' : FakeEllipticCurve Λ N S) :
    IsAtkinLehnerQuotient r E E' ↔
      ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
        (hψ : ψ ≫ E.f = E'.f), IsAtkinLehnerQuotientVia r E E' φ hφ ψ hψ :=
  Iff.rfl

/-- The value of a section at a geometric point. -/
def sectionAt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (k : Type u)
    [Field k] (sk : S →+* k) : SchemeHomOver (geomPoint k sk) f :=
  compPt (geomPoint k sk) (Category.comp_id _) P

/-- A full level-`m` structure: a section whose `Λ`-orbit is all
`m`-torsion at geometric points, with annihilator exactly `mΛ`. -/
structure FullLevel (E : FakeEllipticCurve Λ N S) (m : ℕ) : Type u where
  /-- The section. -/
  P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f
  /-- The section is `m`-torsion. -/
  torsion : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P =
    E.L.one (𝟙 (Spec (CommRingCat.of S)))
  /-- The orbit of the section is all geometric `m`-torsion. -/
  generates : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (Q : SchemeHomOver (geomPoint k sk) E.f),
    nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
    ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (sectionAt P k sk) = Q
  /-- The annihilator of the section is exactly `mΛ`. -/
  annihilator : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (x : ↥Λ), pushPt (E.act x) (E.act_over x) (sectionAt P k sk) =
      E.L.one (geomPoint k sk) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

/-- A fake elliptic curve with a full level-`m` structure. -/
abbrev WithFullLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.FullLevel m

/-- Isomorphism of full-level objects, for a named isomorphism. -/
def WithFullLevel.IsoVia {m : ℕ} (u v : WithFullLevel Λ N m S)
    (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f) : Prop :=
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t u.1.f), mapPt e.hom he (u.1.L.mul t P Q) =
      v.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
  (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ v.1.act x) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P ↔
      FactorsThrough v.1.lev (mapPt e.hom he P)) ∧
  mapPt e.hom he u.2.P = v.2.P

/-- Isomorphism of full-level objects. -/
def WithFullLevel.Iso {m : ℕ} (u v : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f),
    WithFullLevel.IsoVia u v e he

theorem WithFullLevel.iso_iff_exists_via {m : ℕ}
    (u v : WithFullLevel Λ N m S) :
    WithFullLevel.Iso u v ↔ ∃ (e : u.1.A ≅ v.1.A)
      (he : e.hom ≫ v.1.f = u.1.f), WithFullLevel.IsoVia u v e he :=
  Iff.rfl

/-- Being a twist of a full-level object by `c`, for a named iso. -/
def WithFullLevel.IsTwistVia {m : ℕ} (c : ↥Λ)
    (u v : WithFullLevel Λ N m S) (e : u.1.A ≅ v.1.A)
    (he : e.hom ≫ v.1.f = u.1.f) : Prop :=
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P Q : SchemeHomOver t u.1.f), mapPt e.hom he (u.1.L.mul t P Q) =
      v.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
  (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ v.1.act x) ∧
  (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t u.1.f), FactorsThrough u.1.lev P ↔
      FactorsThrough v.1.lev (mapPt e.hom he P)) ∧
  mapPt e.hom he (pushPt (u.1.act c) (u.1.act_over c) u.2.P) = v.2.P

/-- Being a twist of a full-level object by `c`. -/
def WithFullLevel.IsTwist {m : ℕ} (c : ↥Λ)
    (u v : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f),
    WithFullLevel.IsTwistVia c u v e he

theorem WithFullLevel.isTwist_iff_exists_via {m : ℕ} (c : ↥Λ)
    (u v : WithFullLevel Λ N m S) :
    WithFullLevel.IsTwist c u v ↔ ∃ (e : u.1.A ≅ v.1.A)
      (he : e.hom ≫ v.1.f = u.1.f), WithFullLevel.IsTwistVia c u v e he :=
  Iff.rfl

/-- Pullback of full-level objects. -/
def WithFullLevel.IsPullback {S' : Type u} [CommRing S'] (φ : S →+* S')
    {m : ℕ} (u : WithFullLevel Λ N m S) (u' : WithFullLevel Λ N m S') :
    Prop :=
  ∃ (g : u'.1.A ⟶ u.1.A)
    (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P Q : SchemeHomOver t' u'.1.f),
      (u'.1.L.mul t' P Q).left ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          (comapPt g hg P) (comapPt g hg Q)).left) ∧
    (∀ x : ↥Λ, u'.1.act x ≫ g = g ≫ u.1.act x) ∧
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (P : SchemeHomOver t' u'.1.f), FactorsThrough u'.1.lev P →
      ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.left ≫ g) ∧
    (u'.2.P).left ≫ g =
      Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).left

/-- Isomorphism with extra level, for full-level objects. -/
def WithFullLevel.IsoTVia {n ℓ : ℕ} (u v : WithFullLevel Λ N n S)
    (C : u.1.ExtraLevel ℓ) (C' : v.1.ExtraLevel ℓ)
    (i : u.1.A ≅ v.1.A) (hi : i.hom ≫ v.1.f = u.1.f) : Prop :=
  WithFullLevel.IsoVia u v i hi ∧
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P : SchemeHomOver t u.1.f), FactorsThrough C.levK P ↔
        FactorsThrough C'.levK (mapPt i.hom hi P)

end FakeEllipticCurve

variable {a b : ℚ}

/-- A coarse moduli scheme for fake elliptic curves: iso-invariant,
pullback-natural, bijective on geometric points, and universal. -/
structure IsCoarseModuli (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    {B : Type} [CommRing B] (X : Scheme.{0})
    (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX) : Prop where
  /-- Points are invariant under isomorphism. -/
  pt_iso : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' →
    pt S s E = pt S s E'
  /-- Points are natural under pullback. -/
  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S']
    (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
    FakeEllipticCurve.IsPullback φ E E' →
    (pt S' s' E').left = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).left
  /-- Every geometric point comes from a fake elliptic curve. -/
  pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x
  /-- Geometric points determine the curve up to isomorphism. -/
  pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' →
    FakeEllipticCurve.Iso E E'
  /-- Universality among iso-invariant pullback-natural assignments. -/
  univ : ∀ (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πT),
    (∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' →
      pt' S s E = pt' S s E') →
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' →
      (pt' S' s' E').left =
        Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s E).left) →
    ∃! g : X ⟶ T, g ≫ πT = πX ∧ ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (E : FakeEllipticCurve Λ N S), (pt' S s E).left = (pt S s E).left ≫ g

theorem isCoarseModuli_iff {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (N : ℕ) {B : Type} [CommRing B] (X : Scheme.{0})
    (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX) :
    IsCoarseModuli Λ N X πX pt ↔
      (∀ (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' →
        pt S s E = pt S s E') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
        FakeEllipticCurve.IsPullback φ E E' →
        (pt S' s' E').left =
          Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).left) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
        (x : SchemeHomOver s πX),
        ∃ E : FakeEllipticCurve Λ N k, pt k s E = x) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
        (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' →
        FakeEllipticCurve.Iso E E') ∧
      (∀ (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of B))
        (pt' : ∀ (S : Type) [CommRing S]
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
          FakeEllipticCurve Λ N S → SchemeHomOver s πT),
        (∀ (S : Type) [CommRing S]
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' →
          pt' S s E = pt' S s E') →
        (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
          Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
          ∀ (E : FakeEllipticCurve Λ N S)
            (E' : FakeEllipticCurve Λ N S'),
          FakeEllipticCurve.IsPullback φ E E' →
          (pt' S' s' E').left =
            Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s E).left) →
        ∃! g : X ⟶ T, g ≫ πT = πX ∧ ∀ (S : Type) [CommRing S]
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (E : FakeEllipticCurve Λ N S),
          (pt' S s E).left = (pt S s E).left ≫ g) :=
  ⟨fun h => ⟨h.pt_iso, h.pt_pullback, h.pt_surjective, h.pt_injective,
    h.univ⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-- A coarse moduli scheme for fake elliptic curves with extra level. -/
structure IsCoarseModuliT (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ)
    {B : Type} [CommRing B] (Y : Scheme.{0})
    (πY : Y ⟶ Spec (CommRingCat.of B))
    (ptT : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S →
      SchemeHomOver s πY) : Prop where
  /-- Points are invariant under isomorphism. -/
  ptT_iso : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
    FakeEllipticCurve.WithExtraLevel.Iso u v → ptT S s u = ptT S s v
  /-- Points are natural under pullback. -/
  ptT_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S']
    (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
      (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
    FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' →
    (ptT S' s' u').left = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).left
  /-- Every geometric point comes from an extra-level object. -/
  ptT_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (y : SchemeHomOver s πY),
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, ptT k s u = y
  /-- Geometric points determine the object up to isomorphism. -/
  ptT_injective : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ k),
    ptT k s u = ptT k s v → FakeEllipticCurve.WithExtraLevel.Iso u v
  /-- Universality among iso-invariant pullback-natural assignments. -/
  univ : ∀ (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT),
    (∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      FakeEllipticCurve.WithExtraLevel.Iso u v → pt' S s u = pt' S s v) →
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
        (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
      FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' →
      (pt' S' s' u').left =
        Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).left) →
    ∃! g : Y ⟶ T, g ≫ πT = πY ∧ ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
      (pt' S s u).left = (ptT S s u).left ≫ g

theorem isCoarseModuliT_iff {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (N ℓ : ℕ) {B : Type} [CommRing B] (Y : Scheme.{0})
    (πY : Y ⟶ Spec (CommRingCat.of B))
    (ptT : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY) :
    IsCoarseModuliT Λ N ℓ Y πY ptT ↔
      (∀ (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        FakeEllipticCurve.WithExtraLevel.Iso u v →
        ptT S s u = ptT S s v) ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
          (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' →
        (ptT S' s' u').left =
          Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).left) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
        (y : SchemeHomOver s πY),
        ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, ptT k s u = y) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ k),
        ptT k s u = ptT k s v →
        FakeEllipticCurve.WithExtraLevel.Iso u v) ∧
      (∀ (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of B))
        (pt' : ∀ (S : Type) [CommRing S]
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
          FakeEllipticCurve.WithExtraLevel Λ N ℓ S →
          SchemeHomOver s πT),
        (∀ (S : Type) [CommRing S]
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
          FakeEllipticCurve.WithExtraLevel.Iso u v →
          pt' S s u = pt' S s v) →
        (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
          Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
          ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
            (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' →
          (pt' S' s' u').left =
            Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).left) →
        ∃! g : Y ⟶ T, g ≫ πT = πY ∧ ∀ (S : Type) [CommRing S]
          (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
          (pt' S s u).left = (ptT S s u).left ≫ g) :=
  ⟨fun h => ⟨h.ptT_iso, h.ptT_pullback, h.ptT_surjective, h.ptT_injective,
    h.univ⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-- A fine moduli scheme for full-level objects: points over every ring
(not only geometric points) are bijective with full-level objects. -/
structure IsFineModuli (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    {B : Type} [CommRing B] (M : Scheme.{0})
    (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM) :
    Prop where
  /-- Points are invariant under isomorphism. -/
  ptF_iso : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithFullLevel Λ N m S),
    FakeEllipticCurve.WithFullLevel.Iso u v → ptF S s u = ptF S s v
  /-- Points are natural under pullback. -/
  ptF_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S']
    (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N m S)
      (u' : FakeEllipticCurve.WithFullLevel Λ N m S'),
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' →
    (ptF S' s' u').left = Spec.map (CommRingCat.ofHom φ) ≫ (ptF S s u).left
  /-- Every point over every ring comes from a full-level object. -/
  ptF_surjective : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (x : SchemeHomOver s πM),
    ∃ u : FakeEllipticCurve.WithFullLevel Λ N m S, ptF S s u = x
  /-- Points determine the object up to isomorphism. -/
  ptF_injective : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithFullLevel Λ N m S),
    ptF S s u = ptF S s v → FakeEllipticCurve.WithFullLevel.Iso u v

theorem isFineModuli_iff {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    {B : Type} [CommRing B] (M : Scheme.{0})
    (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM) :
    IsFineModuli Λ N m M πM ptF ↔
      (∀ (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithFullLevel Λ N m S),
        FakeEllipticCurve.WithFullLevel.Iso u v →
        ptF S s u = ptF S s v) ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithFullLevel Λ N m S)
          (u' : FakeEllipticCurve.WithFullLevel Λ N m S'),
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' →
        (ptF S' s' u').left =
          Spec.map (CommRingCat.ofHom φ) ≫ (ptF S s u).left) ∧
      (∀ (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (x : SchemeHomOver s πM),
        ∃ u : FakeEllipticCurve.WithFullLevel Λ N m S, ptF S s u = x) ∧
      (∀ (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithFullLevel Λ N m S),
        ptF S s u = ptF S s v →
        FakeEllipticCurve.WithFullLevel.Iso u v) :=
  ⟨fun h => ⟨h.ptF_iso, h.ptF_pullback, h.ptF_surjective, h.ptF_injective⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- An action of a group `G` on a fine moduli scheme by twists, labelled
by elements of the order modulo `mΛ`. -/
structure IsLevelTwistAction (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    {B : Type} [CommRing B] (M : Scheme.{0})
    (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) : Prop where
  /-- The action is over the base. -/
  over_base : ∀ g : G, (ρ g).asIso.hom ≫ πM = πM
  /-- Twisting by the label moves points by the group action. -/
  twist : ∀ (g : G) (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithFullLevel Λ N m S),
    FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u v →
    (ptF S s v).left = (ptF S s u).left ≫ (ρ g).asIso.hom
  /-- The label of `1` is `1` modulo `mΛ`. -/
  label_one : ∃ y : ↥Λ, (χ 1 : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])
  /-- Labels multiply modulo `mΛ`. -/
  label_mul : ∀ g g' : G, ∃ y : ↥Λ,
    (χ (g * g') : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) =
      (m : ℚ) • (y : ℍ[ℚ, a, b])
  /-- Labels cover commuting pairs modulo `mΛ`. -/
  label_surjective : ∀ c d : ↥Λ,
    (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 =
      (m : ℚ) • (y : ℍ[ℚ, a, b])) →
    (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 =
      (m : ℚ) • (y : ℍ[ℚ, a, b])) →
    ∃ (g : G) (y : ↥Λ),
      (χ g : ℍ[ℚ, a, b]) - (c : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])
  /-- Labels are distinct modulo `mΛ`. -/
  label_injective : ∀ g g' : G,
    (∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) - (χ g' : ℍ[ℚ, a, b]) =
      (m : ℚ) • (y : ℍ[ℚ, a, b])) → g = g'

theorem isLevelTwistAction_iff {a b : ℚ}
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) :
    IsLevelTwistAction Λ N m M πM ptF G ρ χ ↔
      (∀ g : G, (ρ g).asIso.hom ≫ πM = πM) ∧
      (∀ (g : G) (S : Type) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithFullLevel Λ N m S),
        FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u v →
        (ptF S s v).left = (ptF S s u).left ≫ (ρ g).asIso.hom) ∧
      (∃ y : ↥Λ, (χ 1 : ℍ[ℚ, a, b]) - 1 =
        (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ g g' : G, ∃ y : ↥Λ,
        (χ (g * g') : ℍ[ℚ, a, b]) -
          (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) =
          (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ c d : ↥Λ,
        (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 =
          (m : ℚ) • (y : ℍ[ℚ, a, b])) →
        (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 =
          (m : ℚ) • (y : ℍ[ℚ, a, b])) →
        ∃ (g : G) (y : ↥Λ),
          (χ g : ℍ[ℚ, a, b]) - (c : ℍ[ℚ, a, b]) =
            (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ g g' : G, (∃ y : ↥Λ,
        (χ g : ℍ[ℚ, a, b]) - (χ g' : ℍ[ℚ, a, b]) =
          (m : ℚ) • (y : ℍ[ℚ, a, b])) → g = g') :=
  ⟨fun h => ⟨h.over_base, h.twist, h.label_one, h.label_mul,
    h.label_surjective, h.label_injective⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

/-- A fine moduli scheme for full-level objects with extra level. -/
structure IsFineModuliT (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n ℓ : ℕ)
    {B : Type u} [CommRing B] (Mℓ : Scheme.{u})
    (πMℓ : Mℓ ⟶ Spec (CommRingCat.of B))
    (ptFℓ : ∀ (S : Type u) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ) : Prop where
  /-- Points are invariant under extra-level isomorphism. -/
  ptFℓ_iso : ∀ (S : Type u) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithFullLevel Λ N n S)
    (C : u.1.ExtraLevel ℓ) (C' : v.1.ExtraLevel ℓ)
    (i : u.1.A ≅ v.1.A) (hi : i.hom ≫ v.1.f = u.1.f),
    FakeEllipticCurve.WithFullLevel.IsoTVia u v C C' i hi →
    ptFℓ S s u C = ptFℓ S s v C'
  /-- Points are natural under pullback. -/
  ptFℓ_pullback : ∀ (S S' : Type u) [CommRing S] [CommRing S']
    (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
      (g : u'.1.A ⟶ u.1.A),
    FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g →
    (u'.2.P).left ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).left →
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S'))
      (P : SchemeHomOver t u'.1.f), FactorsThrough C'.levK P →
      ∃ P₀ : T ⟶ C.K, P₀ ≫ C.levK = P.left ≫ g) →
    (ptFℓ S' s' u' C').left =
      Spec.map (CommRingCat.ofHom φ) ≫ (ptFℓ S s u C).left
  /-- Every point comes from a full-level object with extra level. -/
  ptFℓ_surjective : ∀ (S : Type u) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (x : SchemeHomOver s πMℓ),
    ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel ℓ), ptFℓ S s u C = x
  /-- Points determine the object with extra level up to isomorphism. -/
  ptFℓ_injective : ∀ (S : Type u) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v : FakeEllipticCurve.WithFullLevel Λ N n S)
    (C : u.1.ExtraLevel ℓ) (C' : v.1.ExtraLevel ℓ),
    ptFℓ S s u C = ptFℓ S s v C' →
    ∃ (i : u.1.A ≅ v.1.A) (hi : i.hom ≫ v.1.f = u.1.f),
      FakeEllipticCurve.WithFullLevel.IsoTVia u v C C' i hi

theorem isFineModuliT_iff {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (N n ℓ : ℕ) {B : Type u} [CommRing B] (Mℓ : Scheme.{u})
    (πMℓ : Mℓ ⟶ Spec (CommRingCat.of B))
    (ptFℓ : ∀ (S : Type u) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ) :
    IsFineModuliT Λ N n ℓ Mℓ πMℓ ptFℓ ↔
      (∀ (S : Type u) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithFullLevel Λ N n S)
        (C : u.1.ExtraLevel ℓ) (C' : v.1.ExtraLevel ℓ)
        (i : u.1.A ≅ v.1.A) (hi : i.hom ≫ v.1.f = u.1.f),
        FakeEllipticCurve.WithFullLevel.IsoTVia u v C C' i hi →
        ptFℓ S s u C = ptFℓ S s v C') ∧
      (∀ (S S' : Type u) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
          (g : u'.1.A ⟶ u.1.A),
        FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g →
        (u'.2.P).left ≫ g =
          Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).left →
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S'))
          (P : SchemeHomOver t u'.1.f), FactorsThrough C'.levK P →
          ∃ P₀ : T ⟶ C.K, P₀ ≫ C.levK = P.left ≫ g) →
        (ptFℓ S' s' u' C').left =
          Spec.map (CommRingCat.ofHom φ) ≫ (ptFℓ S s u C).left) ∧
      (∀ (S : Type u) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (x : SchemeHomOver s πMℓ),
        ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S)
          (C : u.1.ExtraLevel ℓ), ptFℓ S s u C = x) ∧
      (∀ (S : Type u) [CommRing S]
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u v : FakeEllipticCurve.WithFullLevel Λ N n S)
        (C : u.1.ExtraLevel ℓ) (C' : v.1.ExtraLevel ℓ),
        ptFℓ S s u C = ptFℓ S s v C' →
        ∃ (i : u.1.A ≅ v.1.A) (hi : i.hom ≫ v.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoTVia u v C C' i hi) :=
  ⟨fun h => ⟨h.ptFℓ_iso, h.ptFℓ_pullback, h.ptFℓ_surjective,
    h.ptFℓ_injective⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

end CerednikDrinfeld.QM
