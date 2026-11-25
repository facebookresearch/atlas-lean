/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_JacJ1Iface.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.AbelianSchemes
public import MathlibExt.AlgebraicGeometry.PointedPicardFamilies
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.SchemeHomOver

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace GoodReductionJacobian

variable (R : Type u) [CommRing R]

/-- A pointed scheme over `Spec R`: a scheme over the base with a zero
section. It records no relation to a curve; `MilneJVScheme.JacobianSchemeData`
identifies such a scheme with the Picard-zero scheme of a pointed curve. -/
public structure PointedRelativeScheme where
  /-- The underlying scheme. -/
  P : Scheme.{u}
  /-- Its structure morphism. -/
  toBase : P ⟶ Spec (CommRingCat.of R)
  /-- The zero section. -/
  zeroSection : Spec (CommRingCat.of R) ⟶ P
  /-- The zero section is a section of the structure morphism. -/
  zeroSection_toBase : zeroSection ≫ toBase = 𝟙 (Spec (CommRingCat.of R))

/-- The base itself, pointed by the identity. -/
public noncomputable def PointedRelativeScheme.trivial : PointedRelativeScheme R where
  P := Spec (CommRingCat.of R)
  toBase := 𝟙 _
  zeroSection := 𝟙 _
  zeroSection_toBase := Category.comp_id _

variable {R}

/-- A bridge identifying an abstract abelian group with the points of a
pointed relative scheme, compatibly with a group law and the zero section. -/
public structure AvatarSchemeBridge (A : Type*) [AddCommGroup A]
    (D : PointedRelativeScheme R) (L : RelativeGroupLaw R D.toBase)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of R)) where
  /-- The identification of the abstract group with scheme points. -/
  pts : A ≃ SchemeHomOver σ D.toBase
  /-- The identification preserves addition. -/
  pts_add : ∀ x y : A, pts (x + y) = L.mul σ (pts x) (pts y)
  /-- The identification sends zero to the zero section. -/
  pts_zero : (pts 0).left = σ ≫ D.zeroSection

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : PointedRelativeScheme R} {L : RelativeGroupLaw R D.toBase}
variable {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)}

/-- The identity point of the group law is the image of zero under a
bridge. -/
public theorem law_one_eq_pts_zero (B : AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 := by
  have hidem : L.mul σ (B.pts 0) (B.pts 0) = B.pts 0 := by
    rw [← B.pts_add, add_zero]
  calc L.one σ
      = L.mul σ (L.inv σ (B.pts 0)) (B.pts 0) :=
        (L.inv_mul_cancel σ (B.pts 0)).symm
    _ = L.mul σ (L.inv σ (B.pts 0)) (L.mul σ (B.pts 0) (B.pts 0)) := by
        rw [hidem]
    _ = L.mul σ (L.mul σ (L.inv σ (B.pts 0)) (B.pts 0)) (B.pts 0) :=
        (L.mul_assoc σ _ _ _).symm
    _ = L.mul σ (L.one σ) (B.pts 0) := by rw [L.inv_mul_cancel]
    _ = B.pts 0 := L.one_mul σ _

end AvatarSchemeBridge

end GoodReductionJacobian

namespace MilneJVScheme

open GoodReductionJacobian MonoidalCategory
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.PointedPicardFamilies

variable {k : Type u} [Field k]

/-- Jacobian scheme data of a proper scheme `C` over `k` with a rational point
`p`, such as a pointed curve: a pointed scheme with a group law whose identity
is the zero section, an identification of it with the Picard-zero model of `C`
normalized along `p` that respects the group laws, a points bridge,
properness, and smoothness of relative dimension `g`.
`JacobianSchemeData.abelianScheme` is the resulting abelian scheme. -/
public structure JacobianSchemeData (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of k)) where
  /-- The pointed scheme. -/
  D : PointedRelativeScheme k
  /-- The relative group law on the scheme. -/
  L : RelativeGroupLaw k D.toBase
  /-- The zero section is the identity section of the group law. -/
  zeroSection_eq : D.zeroSection = (L.one (𝟙 (Spec (CommRingCat.of k)))).left
  /-- The points bridge. -/
  bridge : AvatarSchemeBridge A D L σ
  /-- The scheme is proper. -/
  hProper : IsProper D.toBase
  /-- The scheme is smooth of relative dimension `g`. -/
  hDim : SmoothOfRelativeDimension g D.toBase
  /-- The Picard-zero model of `C`, normalized along `p`. -/
  picard : PicardZeroModel C p
  /-- The scheme is the Picard-zero scheme of `C`. -/
  picardIso : Over.mk D.toBase ≅ picard.J
  /-- The identification carries the group law to that of the Picard-zero
  model, under which addition represents the tensor product of line bundles. -/
  picardIso_isMonHom :
    letI := L.grpObjOverMk; letI := picard.group; IsMonHom picardIso.hom

/-- The scheme of Jacobian scheme data, with its group law, as an abelian
scheme over `Spec k`: its model is `Over.mk J.D.toBase` and its group object is
that of `J.L`. Smoothness comes from `hDim` and properness from `hProper`;
commutativity and geometric connectedness are carried over from the
Picard-zero model through `picardIso`. -/
public noncomputable def JacobianSchemeData.abelianScheme {A : Type*} [AddCommGroup A]
    {C : Over (Spec (CommRingCat.of k))} [IsProper C.hom]
    {p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C} {g : ℕ}
    {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of k)}
    (J : JacobianSchemeData A C p g σ) : AbelianScheme (Spec (CommRingCat.of k)) :=
  letI := J.L.grpObjOverMk
  letI := J.picard.group
  haveI := J.picard.commutative
  haveI := J.picardIso_isMonHom
  haveI := J.hDim
  { model := Over.mk J.D.toBase
    group := J.L.grpObjOverMk
    commutative := ⟨by
      rw [← cancel_mono J.picardIso.hom, Category.assoc, IsMonHom.mul_hom,
        ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩
    smooth := SmoothOfRelativeDimension.smooth g J.D.toBase
    proper := J.hProper
    connected := by
      have := J.picard.connected
      have : IsIso J.picardIso.hom.left :=
        inferInstanceAs (IsIso ((Over.forget _).map J.picardIso.hom))
      have : MorphismProperty.RespectsIso @GeometricallyConnected :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      have hw : J.picardIso.hom.left ≫ J.picard.J.hom = J.D.toBase :=
        Over.w J.picardIso.hom
      change GeometricallyConnected J.D.toBase
      rw [← hw, MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected]
      infer_instance }

/-- Jacobian scheme data assembled from a scheme with a group law, a points
identification over the base, smoothness of relative dimension `g`,
properness, and an identification with the Picard-zero model of `C`
compatible with the group laws. The zero section is the image of zero, which
is the identity of the group law. -/
public noncomputable def JacobianSchemeData.ofCore (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ)
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A,
      pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hdim : SmoothOfRelativeDimension g f) (hproper : IsProper f)
    (M : PicardZeroModel C p) (e : Over.mk f ≅ M.J)
    (he : letI := L.grpObjOverMk; letI := M.group; IsMonHom e.hom) :
    JacobianSchemeData A C p g (𝟙 (Spec (CommRingCat.of k))) :=
  let D : PointedRelativeScheme k :=
    { P := J
      toBase := f
      zeroSection := (pts 0).left
      zeroSection_toBase := Over.w (pts 0) }
  let B : AvatarSchemeBridge A D L (𝟙 (Spec (CommRingCat.of k))) :=
    { pts := pts
      pts_add := pts_add
      pts_zero := (Category.id_comp _).symm }
  { D := D
    L := L
    zeroSection_eq := (congrArg Over.Hom.left B.law_one_eq_pts_zero).symm
    bridge := B
    hProper := hproper
    hDim := hdim
    picard := M
    picardIso := e
    picardIso_isMonHom := he }

end MilneJVScheme
