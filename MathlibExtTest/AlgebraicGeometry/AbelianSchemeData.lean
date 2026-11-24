/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AbelianSchemeData

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

/-- Consumer with the original binders: the trivial designation over a
field. -/
example {k : Type} [Field k] {C : Scheme.{0}}
    (c : C ⟶ Spec (CommRingCat.of k)) :
    GoodReductionJacobian.RelativePic0Designation k c :=
  GoodReductionJacobian.trivialPic0Designation k c

/-- Higher-universe consumer. -/
example {k : Type (u + 1)} [Field k] {C : Scheme.{u + 1}}
    (c : C ⟶ Spec (CommRingCat.of k)) :
    GoodReductionJacobian.RelativePic0Designation k c :=
  GoodReductionJacobian.trivialPic0Designation k c

/-- Consumer assembling Jacobian scheme data from its core, with the
original binders. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A] {C : Scheme.{0}}
    (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ) {J : Scheme.{0}}
    (f : J ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A,
      pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hsmooth : Smooth f) (hproper : IsProper f)
    (hconn : ∀ s : Spec (CommRingCat.of k), _root_.IsConnected (f.base ⁻¹' {s})) :
    MilneJVScheme.JacobianSchemeData A c g
      (𝟙 (Spec (CommRingCat.of k))) :=
  MilneJVScheme.JacobianSchemeData.ofCore A c g f L pts pts_add hsmooth
    hproper hconn

/-- The identity point of the group law agrees with the bridge image of
zero. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A] {C : Scheme.{0}}
    {c : C ⟶ Spec (CommRingCat.of k)}
    (D : GoodReductionJacobian.RelativePic0Designation k c)
    (L : RelativeGroupLaw k D.toBase) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (B : GoodReductionJacobian.AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 :=
  B.law_one_eq_pts_zero

/-- Boundary: the abelian-scheme bundle requires a group law; its
`hasGroupLaw` field is the data that a bare smooth proper morphism does
not supply. -/
example {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)}
    (h : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    Nonempty (RelativeGroupLaw R f) :=
  h.hasGroupLaw
