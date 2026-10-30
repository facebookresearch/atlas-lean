/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_
residueFieldMap.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_
residueFieldMap.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Points of a pullback

Two points of a pullback of schemes with the same projections are equal,
provided the residue field map at the second point's first projection is an
isomorphism: the points then have the same triplet, and the extra residue
field data agrees because the relevant pushout leg is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Two points of a pullback with the same first and second projections are
equal, when the residue field map at the second point's first projection is
an isomorphism. -/
theorem AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : ↥(pullback f g)}
    (h₁ : (pullback.fst f g).base t₁ = (pullback.fst f g).base t₂)
    (h₂ : (pullback.snd f g).base t₁ = (pullback.snd f g).base t₂)
    [IsIso (f.residueFieldMap ((pullback.fst f g).base t₂))] :
    t₁ = t₂ := by
  apply Scheme.Pullback.carrierEquiv.injective
  refine Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨Scheme.Pullback.Triplet.ext h₁ h₂, ?_⟩
  set T := Scheme.Pullback.Triplet.ofPoint t₂ with hT
  have : IsIso ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := by
    have : IsIso (f.residueFieldMap T.x) :=
      inferInstanceAs (IsIso (f.residueFieldMap ((pullback.fst f g).base t₂)))
    infer_instance
  have hinr : IsIso (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
    pushout_inr_iso_of_left_iso _ _
  have hsub : Subsingleton ↥(Spec T.tensor) := by
    constructor
    intro a b
    exact (Spec.map (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))).isOpenEmbedding.injective
      (Subsingleton.elim _ _)
  exact @Subsingleton.elim _ hsub _ _
