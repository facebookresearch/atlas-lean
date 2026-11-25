/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated.lean`
and
`P2M/Sol/S_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated.lean`
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

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private theorem isSchemeTheoreticallyDominant_specMap_of_injective
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have hinj : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom := by
    have e : (Spec.map (CommRingCat.ofHom φ)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫
          (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
      rw [← Iso.inv_comp_eq]
      exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
    have i1 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    have i2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      RingHom.coe_comp]
    exact (i1.comp hφ).comp i2
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp [Scheme.IdealSheafData.ideal_bot]

private theorem eq_of_pullback_fst_comp_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y)
    (H : pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ g₁ =
      pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ g₂) :
    g₁ = g₂ := by
  haveI := isSchemeTheoreticallyDominant_specMap_of_injective (algebraMap k K)
    (algebraMap k K).injective
  haveI : IsSchemeTheoreticallyDominant
      (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    inferInstance
  haveI : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from fY]
    infer_instance
  let e := equalizer.ι g₁ g₂
  haveI : IsClosedImmersion e := inferInstance
  let l := equalizer.lift _ H
  have hl : l ≫ e = pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    equalizer.lift_ι _ _
  have hker : e.ker = ⊥ := by
    apply le_bot_iff.mp
    have := Scheme.Hom.le_ker_comp l e
    rw [hl, Scheme.Hom.ker_eq_bot
      (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))] at this
    exact this
  haveI : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact eq_of_epi_equalizer

/-- Equality of morphisms into a separated scheme is detected after extending
the base field: if two morphisms `g₁ g₂ : X ⟶ Y` over `Spec k` induce the same
morphism after base change along `Spec K ⟶ Spec k`, then `g₁ = g₂`.

The base-changed first projection is scheme-theoretically dominant since
`k → K` is injective, so the equalizer of `g₁` and `g₂`, a closed immersion
by separatedness, has trivial kernel and is an isomorphism. -/
public theorem eq_of_pullback_map_eq_pullback_map_of_isSeparated
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k))
    (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y) (h₁ : g₁ ≫ fY = fX) (h₂ : g₂ ≫ fY = fX)
    (H : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₁ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₁])
            (by rw [Category.comp_id, Category.id_comp]) =
         pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₂ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₂])
            (by rw [Category.comp_id, Category.id_comp])) :
    g₁ = g₂ := by
  apply eq_of_pullback_fst_comp_eq fX fY g₁ g₂ (K := K)
  have := congrArg (· ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))) H
  simpa only [pullback.lift_fst] using this

end AlgebraicGeometry
