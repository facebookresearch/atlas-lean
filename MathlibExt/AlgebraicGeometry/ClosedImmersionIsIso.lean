/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.lean` and
`P2M/Sol/S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Noetherian.Orzech

/-!
# A closed immersion of constant fibre rank is an isomorphism

If `i : X ⟶ Y` is a closed immersion and `g : Y ⟶ S`, `f : X ⟶ S` are
finite, flat, locally of finite presentation with `i ≫ g = f` and the
fibres of `f` and `g` have the same rank at every point of `S`, then `i`
is an isomorphism. The proof reduces to the affine case, where a
surjective map between finite flat modules of the same rank is injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RankCountAux

private lemma injective_of_surjective_of_rankAtStalk_eq
    {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B]
    (ψ : A →ₗ[R] B) (hψ : Function.Surjective ψ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk A p = Module.rankAtStalk B p) :
    Function.Injective ψ := by
  apply injective_of_localized_maximal
  intro J hJ
  haveI hA : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl A) :=
    Module.free_of_flat_of_isLocalRing
  haveI hB : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl A) =
      Module.finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl B) := by
    simpa [Module.rankAtStalk] using h ⟨J, hJ.isPrime⟩
  let e := (LinearEquiv.ofFinrankEq _ _ hrank).symm
  let F := LocalizedModule.map J.primeCompl ψ
  have hF : Function.Surjective F := IsLocalizedModule.map_surjective _ _ _ _ hψ
  have hinj : Function.Injective (e.toLinearMap.comp F) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hF)
  intro x y hxy
  exact hinj (congrArg e hxy)

end RankCountAux

open RankCountAux

namespace AlgebraicGeometry

/-- A closed immersion between maps of constant fibre rank is an
isomorphism. -/
theorem isIso_of_isClosedImmersion_of_finrank_comp_eq
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S) (f : X ⟶ S) (w : i ≫ g = f)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : ↥S, f.finrank s = g.finrank s) :
    IsIso i := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · let 𝒰 := S.affineCover
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme) (𝒰.pullback₁ g)]
    intro j
    have hfin : IsFinite f := by rw [← w]; infer_instance
    let V : pullback g (𝒰.f j) ⟶ Y := pullback.fst g (𝒰.f j)
    let i' : pullback i V ⟶ pullback g (𝒰.f j) := pullback.snd i V
    let g' : pullback g (𝒰.f j) ⟶ 𝒰.X j := pullback.snd g (𝒰.f j)
    have sq : IsPullback (i' ≫ g') (pullback.fst i V) (𝒰.f j) (i ≫ g) :=
      (IsPullback.of_hasPullback i V).flip.paste_horiz (IsPullback.of_hasPullback g (𝒰.f j)).flip
    rw [w] at sq
    haveI hflat' : Flat (i' ≫ g') := MorphismProperty.of_isPullback sq.flip inferInstance
    haveI hlofp' : LocallyOfFinitePresentation (i' ≫ g') :=
      MorphismProperty.of_isPullback sq.flip inferInstance
    have h' : ∀ s, (i' ≫ g').finrank s = g'.finrank s := fun s ↦ by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq.flip, Scheme.Hom.finrank_pullback_snd]
      exact h _
    simp only [MorphismProperty.isomorphisms.iff]
    exact this i' g' (i' ≫ g') rfl h' ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hS
  wlog hY : ∃ A, Y = Spec A generalizing X Y
  · haveI hYaff : IsAffine Y := isAffine_of_isAffineHom g
    rw [← isIso_comp_right_iff i Y.isoSpec.hom]
    refine this (i ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ g) f (by simp [w]) (fun s ↦ ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso]
    exact h s
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hXaff : IsAffine X := isAffine_of_isAffineHom i
    haveI hfinf : IsFinite f := by rw [← w]; infer_instance
    rw [← isIso_comp_left_iff X.isoSpec.inv i]
    refine this (f := X.isoSpec.inv ≫ f) (i := X.isoSpec.inv ≫ i) (by simp [w])
      (fun s ↦ ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso]
    exact h s
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective i
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨θ, rfl⟩ := Spec.map_surjective f
  have hθ : θ = φ ≫ ψ := Spec.map_injective (by rw [Spec.map_comp, w])
  have hψsurj : Function.Surjective ψ.hom := by
    have H := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)).2
    have e : ψ = (Scheme.ΓSpecIso A).inv ≫ (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso B).hom := by
      simp
    rw [e]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).hom).2.comp
      (H.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)
  have hfin : IsFinite (Spec.map θ) := by rw [← w]; infer_instance
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  have h' : ∀ p, θ.hom.finrank p = φ.hom.finrank p := fun p ↦ by
    have := h p
    rwa [Scheme.Hom.finrank_SpecMap_eq_finrank ‹θ.hom.Finite› ‹θ.hom.Flat›,
      Scheme.Hom.finrank_SpecMap_eq_finrank ‹φ.hom.Finite› ‹φ.hom.Flat›] at this
  algebraize [φ.hom, θ.hom]
  have hrk : ∀ p, Module.rankAtStalk (R := R) A p = Module.rankAtStalk (R := R) B p := fun p ↦ by
    have := h' p
    simp only [RingHom.finrank] at this
    exact this.symm
  let ψₗ : A →ₗ[R] B :=
    { toFun := ψ.hom
      map_add' := fun a b ↦ map_add _ a b
      map_smul' := fun r a ↦ by
        simp only [RingHom.id_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, hθ,
          CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] }
  have hinj : Function.Injective ψ.hom :=
    injective_of_surjective_of_rankAtStalk_eq ψₗ hψsurj hrk
  haveI hiso : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).mpr ⟨hinj, hψsurj⟩
  infer_instance

end AlgebraicGeometry
