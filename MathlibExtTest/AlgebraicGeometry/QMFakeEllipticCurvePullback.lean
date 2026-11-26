/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMFakeEllipticCurvePullback

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM

open scoped Quaternion

namespace QMFakeEllipticCurvePullbackTest

/-- Consumer with the original binders (base rings in `Type`). -/
private theorem exactSource
    {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (E'' : FakeEllipticCurve Λ N S'')
    (g : E'.A ⟶ E.A) (g' : E''.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g)
    (hg' : FakeEllipticCurve.IsPullbackVia ψ E' E'' g') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E'' (g' ≫ g) :=
  FakeEllipticCurve.IsPullbackVia.comp φ ψ E E' E'' g g' hg hg'

/-- The statement is universe-polymorphic: base rings in `Type 1`. -/
private theorem higherUniverse
    {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type 1} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (E'' : FakeEllipticCurve Λ N S'')
    (g : E'.A ⟶ E.A) (g' : E''.A ⟶ E'.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g)
    (hg' : FakeEllipticCurve.IsPullbackVia ψ E' E'' g') :
    FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E E'' (g' ≫ g) :=
  FakeEllipticCurve.IsPullbackVia.comp φ ψ E E' E'' g g' hg hg'

/-- The unnamed pullback relation composes as well. -/
private theorem isPullback_comp
    {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (E'' : FakeEllipticCurve Λ N S'')
    (h : FakeEllipticCurve.IsPullback φ E E') (h' : FakeEllipticCurve.IsPullback ψ E' E'') :
    FakeEllipticCurve.IsPullback (ψ.comp φ) E E'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g' ≫ g, FakeEllipticCurve.IsPullbackVia.comp φ ψ E E' E'' g g' hg hg'⟩

/-- `simp` computes the underlying morphism of a point transported along two
pullback squares, through the simp lemma `comapPt_left`. -/
private theorem comapPt_comapPt_left
    {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    {φ : S →+* S'} {ψ : S' →+* S''}
    {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'}
    {E'' : FakeEllipticCurve Λ N S''} (g : E'.A ⟶ E.A) (g' : E''.A ⟶ E'.A)
    (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hg' : CategoryTheory.IsPullback g' E''.f E'.f (Spec.map (CommRingCat.ofHom ψ)))
    {T : Scheme} {t'' : T ⟶ Spec (CommRingCat.of S'')} (P : SchemeHomOver t'' E''.f) :
    (FakeEllipticCurve.comapPt g hg (FakeEllipticCurve.comapPt g' hg' P)).left =
      P.left ≫ g' ≫ g := by
  simp

end QMFakeEllipticCurvePullbackTest
