/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_
of_smoothOfRelativeDimension_of_surjective.lean`
and
`P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_
of_smoothOfRelativeDimension_of_surjective.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

@[expose] public section

universe u

open TensorProduct

namespace SmoothRelDimSubAux

private theorem rank_baseChange_eq {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Nontrivial B] (N : Type u) [AddCommGroup N] [Module A N] [Module.Free A N] :
    Module.rank B (B ⊗[A] N) = Module.rank A N := by
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial
  let b := Module.Free.chooseBasis A N
  let b' := Algebra.TensorProduct.basis B b
  rw [← b.mk_eq_rank'', ← b'.mk_eq_rank'']

private noncomputable def omegaLocEquiv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (T' : Type u) [CommRing T'] [Algebra T T'] [Algebra R T'] [IsScalarTower R T T']
    (M : Submonoid T) [IsLocalization M T'] :
    Ω[T'⁄R] ≃ₗ[T'] T' ⊗[T] Ω[T⁄R] :=
  haveI : Algebra.FormallyEtale T T' := Algebra.FormallyEtale.of_isLocalization M
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R T T').symm

private theorem exists_kaehler_equiv_prod (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C] [Algebra.FormallySmooth S C]
    [Module.Projective C Ω[C⁄S]] :
    Nonempty (Ω[C⁄R] ≃ₗ[C] (C ⊗[S] Ω[S⁄R]) × Ω[C⁄S]) := by
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R S C)
      (KaehlerDifferential.map R S C C) :=
    KaehlerDifferential.exact_mapBaseChange_map R S C
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S C x).mp hx
    haveI : Subsingleton (Algebra.H1Cotangent S C) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (KaehlerDifferential.map R S C C) :=
    KaehlerDifferential.map_surjective R S C
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (KaehlerDifferential.map R S C C)
    LinearMap.id hsurj
  exact ⟨(hex.splitSurjectiveEquiv hinj ⟨l, hl⟩).1⟩

private theorem rank_kaehler_eq_sub {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.IsStandardSmooth R S] [Nontrivial T]
    (a b : ℕ)
    (hb : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (algebraMap S T))
    (ha : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension a) (algebraMap R T)) :
    Module.rank S Ω[S⁄R] = ((a - b : ℕ) : Cardinal) ∧ b ≤ a := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal T
  obtain ⟨sb, hsb, hPb⟩ := hb
  obtain ⟨sa, hsa, hPa⟩ := ha
  obtain ⟨t, ht, ht𝔪⟩ : ∃ t ∈ sb, t ∉ 𝔪 := by
    by_contra hcon; push Not at hcon
    exact h𝔪.ne_top (top_le_iff.mp (hsb ▸ Ideal.span_le.mpr hcon))
  obtain ⟨t', ht', ht'𝔪⟩ : ∃ t' ∈ sa, t' ∉ 𝔪 := by
    by_contra hcon; push Not at hcon
    exact h𝔪.ne_top (top_le_iff.mp (hsa ▸ Ideal.span_le.mpr hcon))
  let Tb := Localization.Away t
  let Ta := Localization.Away t'
  let C := Localization.AtPrime 𝔪
  have hTb : Algebra.IsStandardSmoothOfRelativeDimension b S Tb := by
    have hthis := hPb t ht
    rwa [← IsScalarTower.algebraMap_eq (R := S) (S := T) (A := Tb),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hthis
  have hTa : Algebra.IsStandardSmoothOfRelativeDimension a R Ta := by
    have hthis := hPa t' ht'
    rwa [← IsScalarTower.algebraMap_eq (R := R) (S := T) (A := Ta),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hthis
  haveI : Algebra.IsStandardSmooth S Tb := hTb.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R Ta := hTa.isStandardSmooth
  have hCt : IsUnit (algebraMap T C t) := IsLocalization.map_units C (⟨t, ht𝔪⟩ : 𝔪.primeCompl)
  have hCt' : IsUnit (algebraMap T C t') := IsLocalization.map_units C (⟨t', ht'𝔪⟩ : 𝔪.primeCompl)
  letI : Algebra Tb C := (IsLocalization.Away.lift t hCt).toAlgebra
  haveI : IsScalarTower T Tb C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t hCt x).symm
  letI : Algebra Ta C := (IsLocalization.Away.lift t' hCt').toAlgebra
  haveI : IsScalarTower T Ta C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t' hCt' x).symm
  haveI : Nontrivial Tb := (algebraMap Tb C).domain_nontrivial
  haveI : Nontrivial Ta := (algebraMap Ta C).domain_nontrivial
  have hTS : Algebra.Smooth S T := by
    rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
    exact RingHom.locally_of_locally
      (fun {R' S' : Type u} [CommRing R'] [CommRing S'] (f : R' →+* S')
        (hf : RingHom.IsStandardSmoothOfRelativeDimension b f) =>
        RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth b f hf) ⟨sb, hsb, hPb⟩
  haveI : Algebra.FormallySmooth S T := hTS.formallySmooth
  haveI : Algebra.FormallySmooth T C := Algebra.FormallySmooth.of_isLocalization 𝔪.primeCompl
  haveI : Algebra.FormallySmooth S C := Algebra.FormallySmooth.comp S T C
  have eb : Ω[C⁄S] ≃ₗ[C] C ⊗[Tb] Ω[Tb⁄S] :=
    omegaLocEquiv (R := S) C 𝔪.primeCompl
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange T Tb C C Ω[T⁄S]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
            (omegaLocEquiv (R := S) Tb (Submonoid.powers t)).symm
  have ea : Ω[C⁄R] ≃ₗ[C] C ⊗[Ta] Ω[Ta⁄R] :=
    omegaLocEquiv (R := R) C 𝔪.primeCompl
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange T Ta C C Ω[T⁄R]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
            (omegaLocEquiv (R := R) Ta (Submonoid.powers t')).symm
  haveI : Module.Free C Ω[C⁄S] := Module.Free.of_equiv eb.symm
  haveI : Module.Projective C Ω[C⁄S] := Module.Projective.of_free
  obtain ⟨e⟩ := exists_kaehler_equiv_prod R S C
  have hrb : Module.rank C Ω[C⁄S] = b := by
    rw [eb.rank_eq, rank_baseChange_eq C Ω[Tb⁄S]]
    exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential b
  have hra : Module.rank C Ω[C⁄R] = a := by
    rw [ea.rank_eq, rank_baseChange_eq C Ω[Ta⁄R]]
    exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential a
  have hsum : (a : Cardinal) = Module.rank S Ω[S⁄R] + b := by
    rw [← hra, e.rank_eq, rank_prod', rank_baseChange_eq C Ω[S⁄R], hrb]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Module.rank S Ω[S⁄R] = r := by
    refine Cardinal.lt_aleph0.mp ?_
    calc Module.rank S Ω[S⁄R] ≤ Module.rank S Ω[S⁄R] + b := self_le_add_right _ _
      _ = a := hsum.symm
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  rw [hr] at hsum ⊢
  norm_cast at hsum
  refine ⟨?_, by omega⟩
  congr 1
  omega

end SmoothRelDimSubAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
/-- Relative dimensions subtract along a surjective smooth first arrow: if
`f ≫ g` is smooth of relative dimension `a`, `f` is smooth of relative
dimension `b`, `f` is surjective and `g` is smooth, then `g` is smooth of
relative dimension `a - b` and `b ≤ a`. -/
public theorem
    AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
    {X Y Z : Scheme.{u}} [Nonempty X] (f : X ⟶ Y) (g : Y ⟶ Z) (a b : ℕ)
    [SmoothOfRelativeDimension a (f ≫ g)] [SmoothOfRelativeDimension b f] [Surjective f]
    [Smooth g] :
    SmoothOfRelativeDimension (a - b) g ∧ b ≤ a := by
  have key : ∀ (y : Y) (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
      (hy : y ∈ V) (e : V ≤ g ⁻¹ᵁ U), (g.appLE U V e).hom.IsStandardSmooth →
      (g.appLE U V e).hom.IsStandardSmoothOfRelativeDimension (a - b) ∧ b ≤ a := by
    intro y U hU V hV hy e hstd
    obtain ⟨x, hx⟩ := f.surjective y
    obtain ⟨W, hW, hxW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ V by simpa [← hx] using hy)
    have hb : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b)
        (f.appLE V W hWV).hom :=
      HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension b) f inferInstance ⟨V, hV⟩ ⟨W, hW⟩
        hWV
    have ha : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension a)
        ((f.appLE V W hWV).hom.comp (g.appLE U V e).hom) := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension a) (f ≫ g) inferInstance
        ⟨U, hU⟩ ⟨W, hW⟩ _
    haveI : Nontrivial Γ(X, W) := (X.presheaf.germ W x hxW).hom.domain_nontrivial
    haveI : Nontrivial Γ(Y, V) := (Y.presheaf.germ V y hy).hom.domain_nontrivial
    letI algRS : Algebra Γ(Z, U) Γ(Y, V) := (g.appLE U V e).hom.toAlgebra
    letI algST : Algebra Γ(Y, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
    letI algRT : Algebra Γ(Z, U) Γ(X, W) :=
      ((f.appLE V W hWV).hom.comp (g.appLE U V e).hom).toAlgebra
    haveI : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, W) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Algebra.IsStandardSmooth Γ(Z, U) Γ(Y, V) := hstd
    obtain ⟨hr, hle⟩ := SmoothRelDimSubAux.rank_kaehler_eq_sub (R := Γ(Z, U)) (S := Γ(Y, V))
      (T := Γ(X, W)) a b hb ha
    exact ⟨(Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth (a - b)).mpr hr,
      hle⟩
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨⟨fun y => ?_⟩, ?_⟩
  · obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth g y
    exact ⟨U, hU, V, hV, hy, e, (key y U hU V hV hy e hstd).1⟩
  · obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth g (f.base x₀)
    exact (key _ U hU V hV hy e hstd).2
