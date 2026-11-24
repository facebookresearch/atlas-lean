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
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.SchemeHomOver

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace GoodReductionJacobian

variable (R : Type u) [CommRing R]

/-- The property bundle of an abelian scheme over `Spec R`: smoothness,
properness, connected fibres, and a relative group law. -/
public structure AbelianSchemePropertyBundle {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) : Prop where
  /-- The structure morphism is smooth. -/
  smooth : Smooth f
  /-- The structure morphism is proper. -/
  proper : IsProper f
  /-- Every fibre is connected. -/
  connectedFibres : ∀ s : Spec (CommRingCat.of R),
    _root_.IsConnected (f.base ⁻¹' {s})
  /-- The scheme carries a relative group law. -/
  hasGroupLaw : Nonempty (RelativeGroupLaw R f)

/-- A designation of a relative Picard scheme of degree zero: a scheme
over the base with a zero section. -/
public structure RelativePic0Designation {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) where
  /-- The designated Picard scheme. -/
  P : Scheme.{u}
  /-- Its structure morphism. -/
  toBase : P ⟶ Spec (CommRingCat.of R)
  /-- The zero section. -/
  zeroSection : Spec (CommRingCat.of R) ⟶ P
  /-- The zero section is a section of the structure morphism. -/
  zeroSection_toBase : zeroSection ≫ toBase = 𝟙 (Spec (CommRingCat.of R))

/-- The trivial relative Picard designation, given by the base itself. -/
public noncomputable def trivialPic0Designation {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) : RelativePic0Designation R c where
  P := Spec (CommRingCat.of R)
  toBase := 𝟙 _
  zeroSection := 𝟙 _
  zeroSection_toBase := Category.comp_id _

variable {R}
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

/-- A bridge identifying an abstract abelian group with the points of a
designated relative Picard scheme, compatibly with addition and zero. -/
public structure AvatarSchemeBridge (A : Type*) [AddCommGroup A]
    (D : RelativePic0Designation R c) (L : RelativeGroupLaw R D.toBase)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of R)) where
  /-- The identification of the abstract group with scheme points. -/
  pts : A ≃ SchemeHomOver σ D.toBase
  /-- The identification preserves addition. -/
  pts_add : ∀ x y : A, pts (x + y) = L.mul σ (pts x) (pts y)
  /-- The identification sends zero to the zero section. -/
  pts_zero : (pts 0).left = σ ≫ D.zeroSection

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : RelativePic0Designation R c} {L : RelativeGroupLaw R D.toBase}
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

open GoodReductionJacobian

variable {k : Type u} [Field k]

/-- Jacobian scheme data: a relative Picard designation with a group law,
a points bridge, the abelian-scheme property bundle, and a dimension
proposition. -/
public structure JacobianSchemeData (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of k)) where
  /-- The relative Picard designation. -/
  D : RelativePic0Designation k c
  /-- The relative group law on the designated scheme. -/
  L : RelativeGroupLaw k D.toBase
  /-- The points bridge. -/
  bridge : AvatarSchemeBridge A D L σ
  /-- The abelian-scheme property bundle. -/
  hAbel : AbelianSchemePropertyBundle k D.toBase
  /-- The dimension proposition. -/
  hDim : Prop

/-- Jacobian scheme data assembled from a scheme with a group law, a
points identification, and smoothness, properness and connected fibres. -/
public noncomputable def JacobianSchemeData.ofCore (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A,
      pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hsmooth : Smooth f) (hproper : IsProper f)
    (hconn : ∀ s : Spec (CommRingCat.of k),
      _root_.IsConnected (f.base ⁻¹' {s})) :
    JacobianSchemeData A c g (𝟙 (Spec (CommRingCat.of k))) where
  D :=
    { P := J
      toBase := f
      zeroSection := (pts 0).left
      zeroSection_toBase := Over.w (pts 0) }
  L := L
  bridge :=
    { pts := pts
      pts_add := pts_add
      pts_zero := (Category.id_comp _).symm }
  hAbel :=
    { smooth := hsmooth
      proper := hproper
      connectedFibres := hconn
      hasGroupLaw := ⟨L⟩ }
  hDim := True

end MilneJVScheme
