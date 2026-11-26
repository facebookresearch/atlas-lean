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

`Theorems/Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation.lean`,
`Theorems/Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean`, and
`P2M/Sol/S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean`
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
public import MathlibExt.RingTheory.RingHom.IsPushoutEqLocus
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.Tactic.Algebraize

/-!
# Quotients of affine schemes by finite locally free equivalence relations

An affine scheme with a finite, flat, finitely presented equivalence relation
has a quotient: a finite locally free surjection to an affine scheme that is a
coequalizer and whose kernel pair is the relation. Such quotients are stable
under base change.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

private theorem aff_finite_projective_appTop {X R : Scheme.{u}} [IsAffine X] [IsAffine R]
    (s : R ⟶ X) [IsFinite s] [Flat s] [LocallyOfFinitePresentation s] :
    (letI := s.appTop.hom.toAlgebra; Module.Finite Γ(X, ⊤) Γ(R, ⊤)) ∧
    (letI := s.appTop.hom.toAlgebra; Module.Projective Γ(X, ⊤) Γ(R, ⊤)) := by
  have h₁ : RingHom.Finite s.appTop.hom :=
    s.finite_app ⊤ (isAffineOpen_top X)
  have h₂ : RingHom.Flat s.appTop.hom := HasRingHomProperty.appTop (P := @Flat) s inferInstance
  have h₃ : RingHom.FinitePresentation s.appTop.hom :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) s inferInstance
  algebraize [s.appTop.hom]
  refine ⟨h₁, ?_⟩
  have : Module.FinitePresentation Γ(X, ⊤) Γ(R, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact Module.Flat.projective_of_finitePresentation

private theorem aff_range_sup_range_eq_top {X R : Scheme.{u}} [IsAffine X] [IsAffine R]
    (s t : R ⟶ X) [IsFinite s]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b) :
    s.appTop.hom.range ⊔ t.appTop.hom.range = ⊤ := by
  classical
  set B₀ : Subring Γ(R, ⊤) := s.appTop.hom.range ⊔ t.appTop.hom.range with hB₀
  let s₀ : Γ(X, ⊤) →+* B₀ := s.appTop.hom.codRestrict B₀ (fun a => by
    rw [hB₀]; exact (le_sup_left : s.appTop.hom.range ≤ _) ⟨a, rfl⟩)
  let t₀ : Γ(X, ⊤) →+* B₀ := t.appTop.hom.codRestrict B₀ (fun a => by
    rw [hB₀]; exact (le_sup_right : t.appTop.hom.range ≤ _) ⟨a, rfl⟩)
  let incl : CommRingCat.of B₀ ⟶ Γ(R, ⊤) := CommRingCat.ofHom B₀.subtype
  have hfacs : s.appTop = CommRingCat.ofHom s₀ ≫ incl := by ext; rfl
  have hfact : t.appTop = CommRingCat.ofHom t₀ ≫ incl := by ext; rfl
  have : Epi incl := by
    constructor
    intro T φ ψ h
    have key : Spec.map φ ≫ R.isoSpec.inv = Spec.map ψ ≫ R.isoSpec.inv := by
      apply hmono
      · simp only [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc]
        rw [hfacs, Category.assoc, Category.assoc, h]
      · simp only [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc]
        rw [hfact, Category.assoc, Category.assoc, h]
    have : Spec.map φ = Spec.map ψ := by
      simpa using congrArg (· ≫ R.isoSpec.hom) key
    exact Spec.map_injective this
  have hfin : RingHom.Finite incl.hom := by
    have h₁ : RingHom.Finite s.appTop.hom :=
      s.finite_app ⊤ (isAffineOpen_top X)
    have hfac : incl.hom.comp s₀ = s.appTop.hom := RingHom.ext fun _ => rfl
    rw [← hfac] at h₁
    exact RingHom.Finite.of_comp_finite h₁
  have hsurj : Function.Surjective incl.hom := RingHom.surjective_of_epi_of_finite incl hfin
  rw [eq_top_iff]
  rintro b -
  obtain ⟨⟨b₀, hb₀⟩, rfl⟩ := hsurj b
  exact hb₀

private theorem aff_equivalence_ringPoints {X R : Scheme.{u}} [IsAffine X] [IsAffine R]
    (s t : R ⟶ X)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (T : Type u) [CommRing T] :
    _root_.Equivalence fun x y : Γ(X, ⊤) →+* T =>
      ∃ φ : Γ(R, ⊤) →+* T, φ.comp s.appTop.hom = x ∧ φ.comp t.appTop.hom = y := by
  let Φ : (Γ(X, ⊤) →+* T) → (Spec (.of T) ⟶ X) := fun x =>
    Spec.map (CommRingCat.ofHom x) ≫ X.isoSpec.inv
  let ΦR : (Γ(R, ⊤) →+* T) → (Spec (.of T) ⟶ R) := fun φ =>
    Spec.map (CommRingCat.ofHom φ) ≫ R.isoSpec.inv
  have hΦ : ∀ (f : R ⟶ X) (φ : Γ(R, ⊤) →+* T), ΦR φ ≫ f = Φ (φ.comp f.appTop.hom) :=
    fun f φ => by
      simp only [ΦR, Φ, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc,
        CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]
  have hsurjR : ∀ ψ : Spec (.of T) ⟶ R, ∃ φ, ΦR φ = ψ := fun ψ => by
    obtain ⟨g, hg⟩ := Spec.map_surjective (ψ ≫ R.isoSpec.hom)
    refine ⟨g.hom, ?_⟩
    simp only [ΦR, CommRingCat.ofHom_hom, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hΦinj : Function.Injective Φ := fun x y hxy => by
    have h1 : Spec.map (CommRingCat.ofHom x) = Spec.map (CommRingCat.ofHom y) := by
      simpa [Φ] using congrArg (· ≫ X.isoSpec.hom) hxy
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have key : ∀ x y : Γ(X, ⊤) →+* T,
      (∃ φ : Γ(R, ⊤) →+* T, φ.comp s.appTop.hom = x ∧ φ.comp t.appTop.hom = y) ↔
        (∃ ψ : Spec (.of T) ⟶ R, ψ ≫ s = Φ x ∧ ψ ≫ t = Φ y) := fun x y => by
    constructor
    · rintro ⟨φ, rfl, rfl⟩
      exact ⟨ΦR φ, hΦ s φ, hΦ t φ⟩
    · rintro ⟨ψ, h1, h2⟩
      obtain ⟨φ, rfl⟩ := hsurjR ψ
      exact ⟨φ, hΦinj (by rw [← hΦ, h1]), hΦinj (by rw [← hΦ, h2])⟩
  have E := hequiv (Spec (.of T))
  exact
    { refl := fun x => (key x x).2 (E.refl _)
      symm := fun h => (key _ _).2 (E.symm ((key _ _).1 h))
      trans := fun h h' => (key _ _).2 (E.trans ((key _ _).1 h) ((key _ _).1 h')) }

/-- An affine scheme `X` with a finite, flat, finitely presented equivalence relation
`s t : R ⟶ X` has an affine quotient `p : X ⟶ Y`: `p` is finite, flat, of finite
presentation and surjective, `R` is the kernel pair of `p`, and `p` is the coequalizer
of `s` and `t`. -/
public theorem exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  have : IsAffine R := isAffine_of_isAffineHom s
  set A : Type u := ↥Γ(X, ⊤) with hA
  set B : Type u := ↥Γ(R, ⊤) with hB
  let sr : A →+* B := s.appTop.hom
  let tr : A →+* B := t.appTop.hom
  let C : Subring A := sr.eqLocus tr
  obtain ⟨hs, hs'⟩ := aff_finite_projective_appTop s
  obtain ⟨ht, ht'⟩ := aff_finite_projective_appTop t
  have hgen := aff_range_sup_range_eq_top s t hmono
  have heq := aff_equivalence_ringPoints s t hequiv
  have hinj : Function.Injective (algebraMap C A) := Subtype.val_injective
  have hinv : ∀ a : A, sr a = tr a ↔ a ∈ Set.range (algebraMap C A) := fun a => by
    constructor
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨c, rfl⟩; exact c.2
  obtain ⟨hfin, hproj, hff, hpo⟩ :=
    RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation sr tr hs hs' ht ht' hgen
      heq hinj hinv
  let ι : CommRingCat.of C ⟶ Γ(X, ⊤) := CommRingCat.ofHom (algebraMap C A)
  have hιs : ι ≫ s.appTop = ι ≫ t.appTop := by
    ext c
    exact c.2
  let p : X ⟶ Spec (.of C) := X.isoSpec.hom ≫ Spec.map ι
  have w : s ≫ p = t ≫ p := by
    simp only [p, ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, ← Spec.map_comp, hιs]
  have hι_fin : RingHom.Finite ι.hom := RingHom.finite_algebraMap.mpr hfin
  have hι_ff : ι.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  have : Module.FinitePresentation C A := Module.finitePresentation_of_projective C A
  have hι_fp : RingHom.FinitePresentation ι.hom :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  have : IsFinite (Spec.map ι) := (IsFinite.SpecMap_iff ι).mpr hι_fin
  have : Flat (Spec.map ι) := ((flat_and_surjective_SpecMap_iff ι).mpr hι_ff).1
  have : Surjective (Spec.map ι) := ((flat_and_surjective_SpecMap_iff ι).mpr hι_ff).2
  have : LocallyOfFinitePresentation (Spec.map ι) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hι_fp
  have hpb : IsPullback (Spec.map s.appTop) (Spec.map t.appTop) (Spec.map ι) (Spec.map ι) :=
    isPullback_SpecMap_of_isPushout ι ι s.appTop t.appTop hpo
  have hker : IsPullback s t p p := by
    refine hpb.of_iso R.isoSpec.symm X.isoSpec.symm X.isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa [Iso.symm_hom] using (Scheme.isoSpec_inv_naturality s)
    · simpa [Iso.symm_hom] using (Scheme.isoSpec_inv_naturality t)
    · simp [p]
    · simp [p]
  have hk : IsKernelPair p s t := hker
  exact ⟨Spec (.of C), inferInstance, p, w, inferInstance, inferInstance, inferInstance,
    inferInstance, hker, ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi p)⟩⟩

/-- A finite locally free surjective quotient `p : X ⟶ Y` of `s t : R ⟶ X` with kernel
pair `R` stays a quotient after base change along any `g : Y' ⟶ Y`. -/
public theorem quotient_baseChange_of_finiteLocallyFree_of_isPullback
    {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by
  have : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hX inferInstance
  have : Flat p' := MorphismProperty.of_isPullback (P := @Flat) hX inferInstance
  have : LocallyOfFinitePresentation p' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hX inferInstance
  have : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hX inferInstance
  have hker : IsPullback s' t' p' p' := by
    refine IsPullback.of_isLimit' ⟨w'⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_)
      (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
    · refine hsq.lift (hR.lift (c.fst ≫ gX) (c.snd ≫ gX) ?_) c.fst ?_
      · rw [Category.assoc, Category.assoc, hX.w, ← Category.assoc, ← Category.assoc,
          c.condition]
      · rw [IsPullback.lift_fst]
    · exact hsq.lift_snd _ _ _
    · apply hX.hom_ext
      · rw [Category.assoc, ← htq, ← Category.assoc, hsq.lift_fst, hR.lift_snd]
      · rw [Category.assoc, ← w', ← Category.assoc, hsq.lift_snd, c.condition]
    · apply hsq.hom_ext
      · rw [hsq.lift_fst]
        apply hR.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, hsq.w, ← Category.assoc, hm₁]
        · rw [IsPullback.lift_snd, Category.assoc, htq, ← Category.assoc, hm₂]
      · rw [hsq.lift_snd]
        exact hm₁
  have hk : IsKernelPair p' s' t' := hker
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hker, ⟨?_⟩⟩
  exact hk.toCoequalizer (regularEpiOfEffectiveEpi p')

end AlgebraicGeometry.Scheme
