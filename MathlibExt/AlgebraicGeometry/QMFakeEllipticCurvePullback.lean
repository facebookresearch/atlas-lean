/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp.lean` and
`P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp.lean`
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
# Composition of pullbacks of fake elliptic curves

If `E'` is the pullback of `E` along `φ : S →+* S'` via `g`, and `E''` is
the pullback of `E'` along `ψ : S' →+* S''` via `g'`, then `E''` is the
pullback of `E` along `ψ.comp φ` via `g' ≫ g`: the pullback squares paste,
and compatibility with the group law, the quaternion action and the level
structure transfers along the composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped Quaternion

universe u

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}

-- `hP` and `hQ` are stated in `T ⟶ A`. Written as `P₁.left = P₂.left`, their
-- type mentions both `Over.mk t₁` and `Over.mk t₂`, and at the use in
-- `IsPullbackVia.comp` the kernel then compares the two base points by
-- unfolding, which took minutes of type checking.
/-- The group law only depends on the underlying morphisms of its
arguments, and on the base point up to equality. -/
private theorem mul_left_congr {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f)
    (hP : @Eq (T ⟶ A) P₁.left P₂.left) (hQ : @Eq (T ⟶ A) Q₁.left Q₂.left) :
    (L.mul t₁ P₁ Q₁).left = (L.mul t₂ P₂ Q₂).left := by
  subst h
  obtain rfl : P₁ = P₂ := Over.OverMorphism.ext hP
  obtain rfl : Q₁ = Q₂ := Over.OverMorphism.ext hQ
  rfl

@[simp]
theorem comapPt_left {S S' : Type u} [CommRing S] [CommRing S']
    {φ : S →+* S'} {E : FakeEllipticCurve Λ N S}
    {E' : FakeEllipticCurve Λ N S'} (g : E'.A ⟶ E.A)
    (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (P : SchemeHomOver t' E'.f) : (comapPt g hg P).left = P.left ≫ g :=
  rfl

/-- Pullbacks of fake elliptic curves compose: a pullback along `φ` via
`g` followed by a pullback along `ψ` via `g'` is a pullback along
`ψ.comp φ` via `g' ≫ g`. -/
theorem IsPullbackVia.comp {S S' S'' : Type u} [CommRing S]
    [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (E'' : FakeEllipticCurve Λ N S'') (g : E'.A ⟶ E.A) (g' : E''.A ⟶ E'.A)
    (hg : IsPullbackVia φ E E' g) (hg' : IsPullbackVia ψ E' E'' g') :
    IsPullbackVia (ψ.comp φ) E E'' (g' ≫ g) := by
  obtain ⟨hsq, hlaw, hact, hlev⟩ := hg
  obtain ⟨hsq', hlaw', hact', hlev'⟩ := hg'
  have hsp : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hsq'' : CategoryTheory.IsPullback (g' ≫ g) E''.f E.f
      (Spec.map (CommRingCat.ofHom (ψ.comp φ))) := by
    rw [hsp]
    exact hsq'.paste_horiz hsq
  refine ⟨hsq'', ?_, ?_, ?_⟩
  · intro T t'' P Q
    have e1 := hlaw' t'' P Q
    have e2 := hlaw (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
      (comapPt g' hsq' P) (comapPt g' hsq' Q)
    rw [← Category.assoc, e1, e2]
    refine mul_left_congr E.L ?_ _ _ _ _ ?_ ?_
    · rw [Category.assoc, ← hsp]
    · simp only [comapPt_left, Category.assoc]
    · simp only [comapPt_left, Category.assoc]
  · intro x
    rw [← Category.assoc, hact' x, Category.assoc, hact x, Category.assoc]
  · intro T t'' P hP
    obtain ⟨P₁, hP₁⟩ := hlev' t'' P hP
    obtain ⟨P₀, hP₀⟩ := hlev (t'' ≫ Spec.map (CommRingCat.ofHom ψ))
      (comapPt g' hsq' P) ⟨P₁, by rw [comapPt_left]; exact hP₁⟩
    refine ⟨P₀, ?_⟩
    rw [hP₀]
    simp only [comapPt_left, Category.assoc]

end FakeEllipticCurve

end CerednikDrinfeld.QM
