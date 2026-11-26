/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.Affine
import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.InvariantAffineOpen
import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient.Glue

/-!
# Quotients by finite locally free equivalence relations

A scheme with a finite, flat, finitely presented equivalence relation such that every
equivalence class lies in an affine open has a quotient: a finite locally free
surjection that is the coequalizer of the relation and has the relation as kernel pair.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

section restrict

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X.Opens) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W)

/-- The restriction of `s` over an open `W`. -/
private noncomputable def quotSW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme := s ∣_ W

/-- The restriction of `t` over an invariant open `W`, with source `s ⁻¹ᵁ W`. -/
private noncomputable def quotTW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme :=
  (R.isoOfEq hinv).hom ≫ (t ∣_ W)

private theorem quotSW_ι : quotSW s W ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s := by simp [quotSW]

private theorem quotTW_ι : quotTW s t W hinv ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t := by simp [quotTW]

private theorem quot_isPullback_sW : IsPullback (s ⁻¹ᵁ W).ι (quotSW s W) s W.ι :=
  (isPullback_morphismRestrict s W).flip

private theorem quot_isPullback_tW : IsPullback (s ⁻¹ᵁ W).ι (quotTW s t W hinv) t W.ι := by
  refine (isPullback_morphismRestrict t W).flip.of_iso (R.isoOfEq hinv).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · simp [quotTW]

private theorem quotSW_finite [IsFinite s] : IsFinite (quotSW s W) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (quot_isPullback_sW s W) inferInstance

private theorem quotSW_flat [Flat s] : Flat (quotSW s W) :=
  MorphismProperty.of_isPullback (P := @Flat) (quot_isPullback_sW s W) inferInstance

private theorem quotSW_lfp [LocallyOfFinitePresentation s] :
    LocallyOfFinitePresentation (quotSW s W) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (quot_isPullback_sW s W)
    inferInstance

private theorem quotTW_finite [IsFinite t] : IsFinite (quotTW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (quot_isPullback_tW s t W hinv) inferInstance

private theorem quotTW_flat [Flat t] : Flat (quotTW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @Flat) (quot_isPullback_tW s t W hinv) inferInstance

private theorem quotTW_lfp [LocallyOfFinitePresentation t] :
    LocallyOfFinitePresentation (quotTW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (quot_isPullback_tW s t W hinv) inferInstance

private theorem quot_mono_restrict
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    {T : Scheme.{u}} (a b : T ⟶ (s ⁻¹ᵁ W).toScheme) (h₁ : a ≫ quotSW s W = b ≫ quotSW s W)
    (h₂ : a ≫ quotTW s t W hinv = b ≫ quotTW s t W hinv) : a = b := by
  rw [← cancel_mono (s ⁻¹ᵁ W).ι]
  apply hmono
  · rw [Category.assoc, Category.assoc, ← quotSW_ι, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, ← quotTW_ι s t W hinv, reassoc_of% h₂]

private theorem quot_rel_restrict_iff {T : Scheme.{u}} (x y : T ⟶ W.toScheme) :
    (∃ φ : T ⟶ (s ⁻¹ᵁ W).toScheme, φ ≫ quotSW s W = x ∧ φ ≫ quotTW s t W hinv = y) ↔
      ∃ ψ : T ⟶ R, ψ ≫ s = x ≫ W.ι ∧ ψ ≫ t = y ≫ W.ι := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨φ ≫ (s ⁻¹ᵁ W).ι, by rw [Category.assoc, Category.assoc, quotSW_ι],
      by rw [Category.assoc, Category.assoc, quotTW_ι]⟩
  · rintro ⟨ψ, h₁, h₂⟩
    have hrange : Set.range ψ.base ⊆ Set.range (s ⁻¹ᵁ W).ι.base := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      change s (ψ p) ∈ W
      rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply]
      exact (x p).2
    refine ⟨IsOpenImmersion.lift (s ⁻¹ᵁ W).ι ψ hrange, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, quotSW_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac, h₁]
    · rw [← cancel_mono W.ι, Category.assoc, quotTW_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac, h₂]

private theorem quot_equivalence_restrict
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ W.toScheme =>
      ∃ φ : T ⟶ (s ⁻¹ᵁ W).toScheme, φ ≫ quotSW s W = x ∧ φ ≫ quotTW s t W hinv = y := by
  have E := hequiv T
  exact
    { refl := fun x => (quot_rel_restrict_iff s t W hinv x x).2 (E.refl _)
      symm := fun h => (quot_rel_restrict_iff s t W hinv _ _).2
        (E.symm ((quot_rel_restrict_iff s t W hinv _ _).1 h))
      trans := fun h h' => (quot_rel_restrict_iff s t W hinv _ _).2
        (E.trans ((quot_rel_restrict_iff s t W hinv _ _).1 h)
          ((quot_rel_restrict_iff s t W hinv _ _).1 h')) }

end restrict

/-- A finite, flat, finitely presented equivalence relation `s t : R ⟶ X` whose
equivalence classes each lie in an affine open has a quotient `p : X ⟶ Y` that is finite,
flat, of finite presentation and surjective, has `R` as kernel pair, and is the
coequalizer of `s` and `t`. -/
public theorem exists_quotient_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  choose U hU hxU using haff
  choose W hW hxW _ hinv using fun x =>
    exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation s t hequiv (hU x)
      (hxU x)
  refine exists_quotient_of_forall_exists_quotient_restrict s t W hxW hinv fun x => ?_
  have : IsAffine (W x).toScheme := hW x
  have := quotSW_finite s (W x)
  have := quotSW_flat s (W x)
  have := quotSW_lfp s (W x)
  have := quotTW_finite s t (W x) (hinv x)
  have := quotTW_flat s t (W x) (hinv x)
  have := quotTW_lfp s t (W x) (hinv x)
  obtain ⟨Y, -, p, w, h₁, h₂, h₃, h₄, h₅, -⟩ :=
    exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation (quotSW s (W x))
      (quotTW s t (W x) (hinv x))
      (fun a b h₁ h₂ => quot_mono_restrict s t (W x) (hinv x) hmono a b h₁ h₂)
      (quot_equivalence_restrict s t (W x) (hinv x) hequiv)
  exact ⟨Y, p, w, h₁, h₂, h₃, h₄, h₅⟩

end AlgebraicGeometry.Scheme
