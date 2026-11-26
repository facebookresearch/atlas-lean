/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_<name>.lean` and `P2M/Sol/S_<name>.lean`, where `<name>` is
`GoodReductionJacobian_RelativeGroupLaw_` followed by
`etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension`,
`formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing` or
`formallyUnramified_schemeNsmul_of_forall_sqZero`
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

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegree
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Multiplication by a unit on a smooth commutative group law is étale

Let `G` be a commutative relative group law on a scheme `A` over `Spec R`, with
`R` a local ring. If the natural number `n` is a unit in `R`, then
multiplication by `n` is formally unramified as a scheme endomorphism of `A`;
when moreover `A ⟶ Spec R` is smooth of relative dimension `d`, it is étale.

The formally unramified step checks the infinitesimal lifting criterion: a
point over a square-zero thickening that reduces to the identity and is killed
by `n` is the identity. Near the identity section the group law is given on an
affine chart by a map of rings out of a tensor square, and modulo the square
of the augmentation ideal it is additive, so such a point is killed by `n`
only through `n` times its first-order part, which vanishes since `n` is a
unit. The étale step uses that a formally unramified morphism between schemes
smooth of the same relative dimension over a common base is étale.

## Main results

* `RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero`: the
  lifting criterion for `schemeNsmul n` in terms of points.
* `RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit`: over a local
  ring with `n` a unit, infinitesimal `n`-torsion points are trivial.
* `RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit`.
* `RelativeGroupLaw.etale_schemeNsmul_of_isUnit`.

The source requires commutativity as a hypothesis on the multiplication; here
it is `RelativeGroupLaw.IsCommutative`, which unfolds to the same statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace RelativeGroupLawEtale

section Algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

private theorem subsingleton_kaehler_of_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton Ω[T⁄S] := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hsurj := KaehlerDifferential.map_surjective R S T
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map R S T T a' = 0 := by
    obtain ⟨x, rfl⟩ := h a'
    exact hex.apply_apply_eq_zero x
  have hb : KaehlerDifferential.map R S T T b' = 0 := by
    obtain ⟨x, rfl⟩ := h b'
    exact hex.apply_apply_eq_zero x
  rw [ha, hb]

private theorem formallyEtale_of_formallySmooth_of_bijective [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hΩ : Subsingleton Ω[T⁄S] := subsingleton_kaehler_of_surjective h.2
  have : Algebra.FormallyUnramified S T := ⟨hΩ⟩
  have hδ : ∀ x, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R S T
    have hmem : Algebra.H1Cotangent.δ R S T x ∈
        LinearMap.ker (KaehlerDifferential.mapBaseChange R S T) := by
      rw [LinearMap.mem_ker]
      exact hex.apply_apply_eq_zero x
    rwa [LinearMap.ker_eq_bot.mpr h.1, Submodule.mem_bot] at hmem
  have hH1 : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun a b => ?_⟩
    have hex := Algebra.H1Cotangent.exact_map_δ R S T
    have ha : a ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex a).mp (hδ a)
    have hb : b ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex b).mp (hδ b)
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Subsingleton.elim a' b']
  have : Module.Projective T Ω[T⁄S] := Module.Projective.of_free
  have : Algebra.FormallySmooth S T := ⟨inferInstance, hH1⟩
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

private theorem mapBaseChange_surjective_of_formallyUnramified
    [Algebra.FormallyUnramified S T] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
  intro y
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hy : KaehlerDifferential.map R S T T y = 0 := Subsingleton.elim _ _
  exact (hex y).mp hy

private theorem bijective_of_surjective_of_finrank_eq {A : Type*} [CommRing A] [Nontrivial A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hrank : Module.finrank A M = Module.finrank A N) : Function.Bijective f := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective hf

private theorem etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T := by
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.FormallyEtale S T := by
    refine formallyEtale_of_formallySmooth_of_bijective (R := R) ?_
    have hsurj := mapBaseChange_surjective_of_formallyUnramified (R := R) (S := S) (T := T)
    cases subsingleton_or_nontrivial T with
    | inl hT =>
        exact ⟨fun a b _ => Subsingleton.elim _ _, hsurj⟩
    | inr hT =>
        have : Nontrivial S := (algebraMap S T).domain_nontrivial
        have hS : Module.rank S Ω[S⁄R] = n :=
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
        have hTr : Module.rank T Ω[T⁄R] = n :=
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
        have hSf : Module.finrank S Ω[S⁄R] = n := Module.finrank_eq_of_rank_eq hS
        have hTf : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq hTr
        exact bijective_of_surjective_of_finrank_eq _ hsurj
          (by rw [Module.finrank_baseChange, hSf, hTf])
  have : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

end Algebra

section RingHom

private theorem ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)
    (φ : R →+* S) (ψ : S →+* T)
    (hφ : φ.IsStandardSmoothOfRelativeDimension n)
    (hψφ : (ψ.comp φ).IsStandardSmoothOfRelativeDimension n)
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  algebraize [φ, ψ, ψ.comp φ]
  exact etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n

private theorem ringHom_etale_of_formallyUnramified_of_locally
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (n : ℕ)
    (φ : R →+* S) (ψ : S →+* T)
    (hφ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) φ)
    (hψφ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (ψ.comp φ))
    (hψ : ψ.FormallyUnramified) : ψ.Etale := by
  obtain ⟨sS, hsS, hS⟩ := hφ
  obtain ⟨sT, hsT, hT⟩ := hψφ
  let ι : Type u := sT × sS
  let g : ι → T := fun i => (i.1 : T) * ψ (i.2 : S)
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    have h1 : Ideal.span (ψ '' sS) = ⊤ := by
      have := congrArg (Ideal.map ψ) hsS
      rwa [Ideal.map_span, Ideal.map_top] at this
    have h2 : Ideal.span sT * Ideal.span (ψ '' sS) = Ideal.span (Set.range g) := by
      rw [Ideal.span_mul_span]
      congr 1
      ext x
      simp only [Set.mem_mul, Set.mem_image, Set.mem_range, g, ι, Prod.exists,
        Subtype.exists, exists_prop]
      constructor
      · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    rw [← h2, hsT, h1, Ideal.top_mul]
  let Tt : ι → Type u := fun i => Localization.Away (i.1 : T)
  let Tg : ι → Type u := fun i => Localization.Away (algebraMap T (Tt i) (ψ (i.2 : S)))
  have key : ∀ i : ι, RingHom.Etale ((algebraMap T (Tg i)).comp ψ) := by
    intro i
    obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := i
    let Ss := Localization.Away s
    have hunit : IsUnit ((algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ s) := by
      simp only [RingHom.coe_comp, Function.comp_apply, Tg]
      rw [IsScalarTower.algebraMap_apply T (Tt (⟨t, ht⟩, ⟨s, hs⟩)) (Tg (⟨t, ht⟩, ⟨s, hs⟩))]
      exact IsLocalization.Away.algebraMap_isUnit _
    let ψ' : Ss →+* Tg (⟨t, ht⟩, ⟨s, hs⟩) :=
      IsLocalization.Away.lift s (g := (algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ) hunit
    have hψ' : ψ'.comp (algebraMap S Ss) = (algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp ψ := by
      ext x
      simp [ψ']
    have h1 : ((algebraMap S Ss).comp φ).IsStandardSmoothOfRelativeDimension n := hS s hs
    have h2 : ((algebraMap T (Tg (⟨t, ht⟩, ⟨s, hs⟩))).comp
        (ψ.comp φ)).IsStandardSmoothOfRelativeDimension n := by
      have h2a : ((algebraMap T (Tt (⟨t, ht⟩, ⟨s, hs⟩))).comp
          (ψ.comp φ)).IsStandardSmoothOfRelativeDimension n := hT t ht
      have :=
        RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
      have h2b := this.2 (Tg (⟨t, ht⟩, ⟨s, hs⟩))
        (algebraMap T (Tt (⟨t, ht⟩, ⟨s, hs⟩)) (ψ s)) _ h2a
      rwa [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h2b
    have h3 : ψ'.FormallyUnramified := by
      refine RingHom.FormallyUnramified.of_comp (f := algebraMap S Ss) ?_
      rw [hψ']
      exact RingHom.FormallyUnramified.comp hψ
        (RingHom.FormallyUnramified.holdsForLocalizationAway _ (t * ψ s))
    have h2' : (ψ'.comp ((algebraMap S Ss).comp φ)).IsStandardSmoothOfRelativeDimension n := by
      rwa [← RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    have h4 : ψ'.Etale :=
      ringHom_etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension n _ ψ'
        h1 h2' h3
    have h5 : (algebraMap S Ss).Etale := by
      rw [RingHom.etale_algebraMap]
      exact Algebra.Etale.of_isLocalizationAway s
    rw [← hψ']
    exact RingHom.Etale.stableUnderComposition _ _ h5 h4
  have hloc : RingHom.Locally RingHom.Etale ψ :=
    RingHom.locally_of_exists RingHom.Etale.respectsIso ψ g hspan Tg key
  exact (RingHom.locally_iff_of_localizationSpanTarget RingHom.Etale.respectsIso
    RingHom.Etale.ofLocalizationSpanTarget _).mp hloc

end RingHom

/-- A formally unramified morphism `X ⟶ Y` over `Z`, where `X` and `Y` are smooth of the
same relative dimension over `Z`, is étale. -/
private theorem etale_of_formallyUnramified_of_smoothOfRelativeDimension
    {X Y Z : Scheme.{u}} (n : ℕ) {f : X ⟶ Y} {g : Y ⟶ Z}
    (h1 : SmoothOfRelativeDimension n (f ≫ g)) (h2 : SmoothOfRelativeDimension n g)
    (h3 : FormallyUnramified f) : Etale f := by
  have : IsZariskiLocalAtTarget @Etale := HasRingHomProperty.instIsZariskiLocalAtTarget _
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  have : IsZariskiLocalAtTarget @FormallyUnramified :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H1 := IsZariskiLocalAtTarget.restrict h1 U.1
    rw [morphismRestrict_comp] at H1
    have H2 : SmoothOfRelativeDimension n (g ∣_ U.1) := IsZariskiLocalAtTarget.restrict h2 U.1
    have H3 : FormallyUnramified (f ∣_ g ⁻¹ᵁ U.1) := IsZariskiLocalAtTarget.restrict h3 _
    exact this H1 H2 H3 inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H1 := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n)
      (f ⁻¹ᵁ U.1).ι (f ≫ g) h1
    rw [← morphismRestrict_ι_assoc] at H1
    have H2 : SmoothOfRelativeDimension n (U.1.ι ≫ g) :=
      HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n) _ _ h2
    have H3 : FormallyUnramified (f ∣_ U.1) := IsZariskiLocalAtTarget.restrict h3 _
    exact this H1 H2 H3 U.2
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H1 := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension n)
      U.1.ι (f ≫ g) h1
    rw [← Category.assoc] at H1
    have H3 : FormallyUnramified (U.1.ι ≫ f) :=
      MorphismProperty.IsStableUnderComposition.comp_mem (P := @FormallyUnramified) _ _
        (inferInstance : FormallyUnramified U.1.ι) h3
    exact this H1 H3 U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)] at h1 h2
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)] at h3
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h1
  exact ringHom_etale_of_formallyUnramified_of_locally n _ _ h2 h1 h3

end RelativeGroupLawEtale

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

private theorem nsmul_left (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    (G.nsmul t n x).left = x.left ≫ G.schemeNsmul n := by
  rw [← G.comp_nsmul_idPoint t n x]
  rfl

private theorem one_left (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).left = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).left := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

/-- The infinitesimal lifting criterion for multiplication by `n` on a commutative relative
group law: if every point over a square-zero thickening that reduces to the identity and is
killed by `n` is the identity, then `schemeNsmul n` is formally unramified. -/
theorem formallyUnramified_schemeNsmul_of_forall_sqZero (G : RelativeGroupLaw R f)
    (hc : G.IsCommutative) (n : ℕ)
    (hTF : ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
      RingHom.ker φ.hom ^ 2 = ⊥ →
      ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : Over.mk t ⟶ Over.mk f),
        Over.homMk (U := Over.mk (Spec.map φ ≫ t)) (V := Over.mk t) (Spec.map φ) rfl ≫ k =
          G.one (Spec.map φ ≫ t) →
        G.nsmul t n k = G.one t → k = G.one t) :
    FormallyUnramified (G.schemeNsmul n) := by
  refine FormallyUnramified.of_hom_ext _ (fun R' S' φ hsurj hker g₁ g₂ hred hcomp => ?_)
  let t : Spec R' ⟶ Spec (CommRingCat.of R) := g₁ ≫ f
  have ht₂ : g₂ ≫ f = t := by
    have h₁ : g₁ ≫ f = g₁ ≫ G.schemeNsmul n ≫ f := by rw [G.schemeNsmul_comp]
    have h₂ : g₂ ≫ f = g₂ ≫ G.schemeNsmul n ≫ f := by rw [G.schemeNsmul_comp]
    rw [h₂, ← Category.assoc, ← hcomp, Category.assoc, ← h₁]
  let x₁ : Over.mk t ⟶ Over.mk f := Over.homMk g₁ rfl
  let x₂ : Over.mk t ⟶ Over.mk f := Over.homMk g₂ ht₂
  let := G.pointCommGroup hc t
  have hnpow : x₁ ^ n = x₂ ^ n := by
    rw [← G.nsmul_eq_pow, ← G.nsmul_eq_pow]
    exact Over.OverMorphism.ext
      (((G.nsmul_left n x₁).trans hcomp).trans (G.nsmul_left n x₂).symm)
  let k : Over.mk t ⟶ Over.mk f := x₁ * x₂⁻¹
  have hknpow : G.nsmul t n k = G.one t := by
    rw [G.nsmul_eq_pow]
    change (x₁ * x₂⁻¹) ^ n = 1
    rw [← div_eq_mul_inv, div_pow, hnpow, div_self']
  let t' : Spec S' ⟶ Spec (CommRingCat.of R) := Spec.map φ ≫ t
  let grp' : Group (Over.mk t' ⟶ Over.mk f) := G.pointGroup t'
  let red : (Over.mk t ⟶ Over.mk f) →* (Over.mk t' ⟶ Over.mk f) :=
    { toFun := fun x => Over.homMk (U := Over.mk t') (V := Over.mk t) (Spec.map φ) rfl ≫ x
      map_one' := G.one_natural t t' (Spec.map φ) rfl
      map_mul' := fun x y => G.mul_natural t t' (Spec.map φ) rfl x y }
  have hkred : Over.homMk (U := Over.mk t') (V := Over.mk t) (Spec.map φ) rfl ≫ k =
      G.one t' := by
    have hx₁₂ : red x₁ = red x₂ := Over.OverMorphism.ext hred
    change red (x₁ * x₂⁻¹) = 1
    rw [map_mul, map_inv, hx₁₂, _root_.mul_inv_cancel]
  have hkone : k = G.one t := hTF R' S' φ hsurj hker t k hkred hknpow
  have hx : x₁ = x₂ := by
    have : x₁ * x₂⁻¹ = 1 := hkone
    exact mul_inv_eq_one.mp this
  exact congrArg (fun x => x.left) hx

/-- The identity section of a relative group law. -/
noncomputable def unitSection (G : RelativeGroupLaw R f) :
    Spec (CommRingCat.of R) ⟶ A :=
  (G.one (𝟙 (Spec (CommRingCat.of R)))).left

theorem unitSection_comp (G : RelativeGroupLaw R f) :
    G.unitSection ≫ f = 𝟙 (Spec (CommRingCat.of R)) :=
  Over.w (G.one (𝟙 (Spec (CommRingCat.of R))))

private theorem specMap_surjective_of_sqZero {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    Function.Surjective (Spec.map φ) := by
  intro p
  have hkerp : RingHom.ker φ.hom ≤ p.asIdeal :=
    Ideal.IsPrime.le_of_pow_le (hP := p.isPrime) (n := 2) (hker ▸ bot_le)
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap φ.hom) := by
    rw [range_comap_of_surjective _ φ.hom hsurj]
    exact hkerp
  exact ⟨q, (Spec.map_apply φ q).trans hq⟩

private theorem range_subset_of_isKer (G : RelativeGroupLaw R f)
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : Over.mk t ⟶ Over.mk f)
    (hkred : Over.homMk (U := Over.mk (Spec.map φ ≫ t)) (V := Over.mk t) (Spec.map φ) rfl ≫ k =
      G.one (Spec.map φ ≫ t)) :
    Set.range k.left ⊆ Set.range G.unitSection := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, rfl⟩ := specMap_surjective_of_sqZero φ hsurj hker p
  have h1 : Spec.map φ ≫ k.left = (G.one (Spec.map φ ≫ t)).left :=
    congrArg (fun x => x.left) hkred
  have hcoe : (Spec.map φ ≫ k.left) q = ((Spec.map φ ≫ t) ≫ G.unitSection) q := by
    rw [h1, G.one_left]
    rfl
  exact ⟨(Spec.map φ ≫ t) q, hcoe.symm.trans rfl⟩

section RingTheory

variable {B R' S' : Type*} [CommRing B] [CommRing R'] [CommRing S']
variable [Algebra R B] [Algebra R R']
variable (ε₀ : B →ₐ[R] R) (φ : R' →+* S')

/-- The trivial lift of an augmentation `B → R` to an `R`-algebra `R'`. -/
private def trivLift : B →ₐ[R] R' := (Algebra.ofId R R').comp (ε₀.restrictScalars R)

private theorem trivLift_apply (x : B) : trivLift ε₀ x = algebraMap R R' (ε₀ x) := rfl

private theorem mem_ker_of_mem_augIdeal (kR : B →ₐ[R] R')
    (hk : ∀ x, φ (kR x) = φ (trivLift ε₀ x))
    {a : B} (ha : a ∈ RingHom.ker ε₀) : kR a ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, hk a, trivLift_apply]
  rw [RingHom.mem_ker] at ha
  rw [ha, map_zero, map_zero]

private theorem eq_zero_of_mem_sq (hkerφ : RingHom.ker φ ^ 2 = ⊥)
    (kR : B →ₐ[R] R') (hk : ∀ x, φ (kR x) = φ (trivLift ε₀ x))
    {a : B} (ha : a ∈ (RingHom.ker ε₀) ^ 2) : kR a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have : kR x * kR y ∈ RingHom.ker φ ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (mem_ker_of_mem_augIdeal ε₀ φ kR hk hx)
        (mem_ker_of_mem_augIdeal ε₀ φ kR hk hy)
    rw [hkerφ, Ideal.mem_bot] at this
    rwa [map_mul]
  · rw [map_add, hx, hy, add_zero]

private theorem sub_algebraMap_mem_augIdeal (x : B) :
    x - algebraMap R B (ε₀ x) ∈ RingHom.ker ε₀ := by
  simp [RingHom.mem_ker, map_sub, AlgHom.commutes]

end RingTheory

section FourTerm

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The map out of a tensor square determined by two algebra maps. -/
private abbrev tensorPair (p q : B →ₐ[R] C) : (B ⊗[R] B) →ₐ[R] C :=
  Algebra.TensorProduct.lift p q (fun _ _ => mul_comm _ _)

private theorem fourTerm_tensorPair (ε₀ : B →ₐ[R] R) {J : Ideal C} (hJ2 : J ^ 2 = ⊥)
    (p q : B →ₐ[R] C) (hp : ∀ a ∈ RingHom.ker ε₀, p a ∈ J)
    (hq : ∀ a ∈ RingHom.ker ε₀, q a ∈ J) (z : B ⊗[R] B) :
    tensorPair p q z - tensorPair p (trivLift ε₀) z
      - tensorPair (trivLift ε₀) q z
      + tensorPair (trivLift ε₀) (trivLift ε₀) z = 0 := by
  induction z with
  | add x y hx hy => simp only [map_add]; linear_combination hx + hy
  | tmul b c =>
    change p b * q c - p b * trivLift ε₀ c - trivLift ε₀ b * q c
      + trivLift ε₀ b * trivLift ε₀ c = 0
    have key : (p b - trivLift ε₀ b) * (q c - trivLift ε₀ c) = 0 := by
      have hmem : (p b - trivLift ε₀ b) * (q c - trivLift ε₀ c) ∈ J ^ 2 := by
        rw [pow_two]
        refine Ideal.mul_mem_mul ?_ ?_
        · rw [trivLift_apply]
          have := hp _ (sub_algebraMap_mem_augIdeal ε₀ b)
          rwa [map_sub, AlgHom.commutes] at this
        · rw [trivLift_apply]
          have := hq _ (sub_algebraMap_mem_augIdeal ε₀ c)
          rwa [map_sub, AlgHom.commutes] at this
      rwa [hJ2, Ideal.mem_bot] at hmem
    linear_combination key

private theorem tensorPair_lifts_trivLift (ε₀ : B →ₐ[R] R) {S' : Type*} [CommRing S']
    (φ : C →+* S') (p q : B →ₐ[R] C)
    (hp : ∀ b, φ (p b) = φ (trivLift ε₀ b)) (hq : ∀ b, φ (q b) = φ (trivLift ε₀ b))
    (z : B ⊗[R] B) :
    φ (tensorPair p q z) = φ (trivLift (tensorPair ε₀ ε₀) z) := by
  induction z with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    change φ (p b * q c) = φ (algebraMap R C (ε₀ b * ε₀ c))
    simp only [map_mul, hp b, hq c, trivLift_apply]

end FourTerm

section AffineBridge

variable (G : RelativeGroupLaw R f)
variable (B₁ : CommRingCat.{u}) (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
variable (hιe : Set.range G.unitSection ⊆ Set.range ι)
variable {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
variable (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
variable (t : Spec R' ⟶ Spec (CommRingCat.of R))

/-- A point over `Spec R'` that reduces to the identity over `Spec S'`. -/
private def IsKerElt (k : Over.mk t ⟶ Over.mk f) : Prop :=
  Over.homMk (U := Over.mk (Spec.map φ ≫ t)) (V := Over.mk t) (Spec.map φ) rfl ≫ k =
    G.one (Spec.map φ ≫ t)

private theorem isKerElt_one : IsKerElt G φ t (G.one t) :=
  G.one_natural t (Spec.map φ ≫ t) (Spec.map φ) rfl

private theorem isKerElt_mul {x y : Over.mk t ⟶ Over.mk f}
    (hx : IsKerElt G φ t x) (hy : IsKerElt G φ t y) :
    IsKerElt G φ t (G.mul t x y) := by
  unfold IsKerElt at hx hy ⊢
  rw [G.mul_natural t (Spec.map φ ≫ t) (Spec.map φ) rfl x y, hx, hy, G.one_mul]

private theorem isKerElt_nsmul {k : Over.mk t ⟶ Over.mk f} (hk : IsKerElt G φ t k)
    (m : ℕ) : IsKerElt G φ t (G.nsmul t m k) := by
  unfold IsKerElt at hk ⊢
  rw [G.homMk_comp_nsmul t _ (Spec.map φ) rfl m k, hk, G.nsmul_one_point]

omit hsurj hker hιe in
/-- The ring map out of the affine chart classifying a point near the identity. -/
private noncomputable def kerRing (G : RelativeGroupLaw R f) (B₁ : CommRingCat.{u})
    (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι] (hιe : Set.range G.unitSection ⊆ Set.range ι)
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S') (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥) (t : Spec R' ⟶ Spec (CommRingCat.of R))
    (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k) : B₁ ⟶ R' :=
  Spec.preimage (IsOpenImmersion.lift ι k.left
    ((range_subset_of_isKer G φ hsurj hker t k hk).trans hιe))

private theorem map_kerRing (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k) :
    Spec.map (kerRing G B₁ ι hιe φ hsurj hker t k hk) ≫ ι = k.left := by
  rw [kerRing, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

private theorem eq_of_kerRing_eq {k k' : Over.mk t ⟶ Over.mk f}
    (hk : IsKerElt G φ t k) (hk' : IsKerElt G φ t k')
    (h : kerRing G B₁ ι hιe φ hsurj hker t k hk = kerRing G B₁ ι hιe φ hsurj hker t k' hk') :
    k = k' :=
  Over.OverMorphism.ext <| by
    rw [← map_kerRing G B₁ ι hιe φ hsurj hker t k hk,
      ← map_kerRing G B₁ ι hιe φ hsurj hker t k' hk', h]

private theorem kerRing_reduces (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k) (b : B₁) :
    φ.hom ((kerRing G B₁ ι hιe φ hsurj hker t k hk).hom b)
      = φ.hom ((kerRing G B₁ ι hιe φ hsurj hker t (G.one t) (isKerElt_one G φ t)).hom b) := by
  have heq : Spec.map φ ≫ Spec.map (kerRing G B₁ ι hιe φ hsurj hker t k hk)
      = Spec.map φ ≫ Spec.map (kerRing G B₁ ι hιe φ hsurj hker t (G.one t)
          (isKerElt_one G φ t)) := by
    rw [← cancel_mono ι, Category.assoc, Category.assoc, map_kerRing, map_kerRing]
    exact congrArg (fun x => x.left) (hk.trans (isKerElt_one G φ t).symm)
  simp only [← Spec.map_comp] at heq
  have := Spec.map_injective heq
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) b

end AffineBridge

section TensorArgument

open Algebra.TensorProduct

variable (G : RelativeGroupLaw R f)
variable (B₁ : CommRingCat.{u}) [Algebra R B₁]
variable (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
variable (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
variable (hιe : Set.range G.unitSection ⊆ Set.range ι)

include hιf in
private theorem preimage_lift_algebraMap {T : CommRingCat.{u}}
    (g : Spec T ⟶ A) (hrange : Set.range g ⊆ Set.range ι)
    (algT : CommRingCat.of R ⟶ T) (hg : g ≫ f = Spec.map algT) (r : R) :
    (Spec.preimage (IsOpenImmersion.lift ι g hrange)).hom (algebraMap R B₁ r)
      = algT.hom r := by
  have h2 : IsOpenImmersion.lift ι g hrange
      ≫ Spec.map (CommRingCat.ofHom (algebraMap R B₁)) = Spec.map algT := by
    rw [← hιf, ← Category.assoc, IsOpenImmersion.lift_fac, hg]
  have h3 := Spec.preimage_comp (IsOpenImmersion.lift ι g hrange)
    (Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
  rw [h2, Spec.preimage_map, Spec.preimage_map] at h3
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3.symm) r

/-- The augmentation of the affine chart at the identity section. -/
private noncomputable def aug (G : RelativeGroupLaw R f) (B₁ : CommRingCat.{u}) [Algebra R B₁]
    (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
    (hιe : Set.range G.unitSection ⊆ Set.range ι) : (B₁ : Type u) →ₐ[R] R :=
  { (Spec.preimage (IsOpenImmersion.lift ι G.unitSection hιe)).hom with
    commutes' := fun r => preimage_lift_algebraMap B₁ ι hιf
      G.unitSection hιe (𝟙 (CommRingCat.of R)) (G.unitSection_comp.trans
        (Spec.map_id _).symm) r }

private theorem map_aug :
    Spec.map (CommRingCat.ofHom (aug G B₁ ι hιf hιe).toRingHom) ≫ ι = G.unitSection := by
  have : (CommRingCat.ofHom (aug G B₁ ι hιf hιe).toRingHom)
      = Spec.preimage (IsOpenImmersion.lift ι G.unitSection hιe) := by
    apply CommRingCat.hom_ext; rfl
  rw [this, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The structure morphism of the spectrum of the tensor square of the chart. -/
private noncomputable def tensorStruct : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁))
    ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R ((B₁ : Type u) ⊗[R] B₁)))

/-- The point of `A` over the tensor square given by an algebra map out of the chart. -/
private noncomputable def tensorPoint (B₁ : CommRingCat.{u}) [Algebra R B₁]
    (ι : Spec B₁ ⟶ A) (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
    (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)) :
    Over.mk (tensorStruct (R := R) B₁) ⟶ Over.mk f :=
  Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ι) (by
    change _ ≫ f = tensorStruct B₁
    rw [Category.assoc, hιf, ← Spec.map_comp, tensorStruct]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    change ρ.toRingHom (algebraMap R B₁ r) = algebraMap R ((B₁ : Type u) ⊗[R] B₁) r
    exact ρ.commutes r)

/-- The universal product of the two points of the chart over its tensor square. -/
private noncomputable def universalMul (G : RelativeGroupLaw R f) (B₁ : CommRingCat.{u})
    [Algebra R B₁] (ι : Spec B₁ ⟶ A)
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁))) :
    Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁)) ⟶ A :=
  (G.mul (tensorStruct (R := R) B₁)
    (tensorPoint B₁ ι hιf includeLeft) (tensorPoint B₁ ι hιf includeRight)).left

/-- The augmentation of the tensor square. -/
private noncomputable abbrev augAug (G : RelativeGroupLaw R f) (B₁ : CommRingCat.{u})
    [Algebra R B₁] (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
    (hιe : Set.range G.unitSection ⊆ Set.range ι) : ((B₁ : Type u) ⊗[R] B₁) →ₐ[R] R :=
  tensorPair (aug G B₁ ι hιf hιe) (aug G B₁ ι hιf hιe)

private theorem augAug_surjective : Function.Surjective (augAug G B₁ ι hιf hιe) := fun r =>
  ⟨algebraMap R _ r, (augAug G B₁ ι hιf hιe).commutes r⟩

private theorem universalMul_aug :
    Spec.map (CommRingCat.ofHom (augAug G B₁ ι hιf hιe).toRingHom)
      ≫ universalMul G B₁ ι hιf = G.unitSection := by
  set εε := augAug G B₁ ι hιf hιe
  have hτ0 : Spec.map (CommRingCat.ofHom εε.toRingHom) ≫ tensorStruct (R := R) B₁
      = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [tensorStruct, ← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext εε.commutes))
  have hξ : ∀ (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)),
      εε.comp ρ = aug G B₁ ι hιf hιe →
      Over.homMk (U := Over.mk (𝟙 (Spec (CommRingCat.of R))))
          (V := Over.mk (tensorStruct (R := R) B₁))
          (Spec.map (CommRingCat.ofHom εε.toRingHom)) hτ0 ≫ tensorPoint B₁ ι hιf ρ =
        G.one (𝟙 _) := fun ρ hρ => Over.OverMorphism.ext <| by
    simp only [Over.comp_left, Over.homMk_left, tensorPoint, ← Category.assoc,
      ← Spec.map_comp]
    change _ = G.unitSection
    rw [← map_aug G B₁ ι hιf hιe]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun b =>
      (DFunLike.congr_fun (congrArg AlgHom.toRingHom hρ) b :))
  have h := G.mul_natural (tensorStruct (R := R) B₁) (𝟙 _)
    (Spec.map (CommRingCat.ofHom εε.toRingHom)) hτ0
    (tensorPoint B₁ ι hιf includeLeft) (tensorPoint B₁ ι hιf includeRight)
  rw [hξ includeLeft (Algebra.TensorProduct.lift_comp_includeLeft _ _ _),
    hξ includeRight (Algebra.TensorProduct.lift_comp_includeRight' _ _ _), G.one_mul] at h
  exact congrArg (fun x => x.left) h

private theorem range_truncMul_subset :
    Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (RingHom.ker (augAug G B₁ ι hιf hιe).toRingHom ^ 2)))
      ≫ universalMul G B₁ ι hιf) ⊆ Set.range ι := by
  set εε := augAug G B₁ ι hιf hιe
  set 𝔐 := RingHom.ker εε.toRingHom
  rintro _ ⟨p, rfl⟩
  set P := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔐 ^ 2)))) p with hPdef
  have h𝔐P : 𝔐 ≤ P.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := P.isPrime) (n := 2)
    fun x hx => by
      change Ideal.Quotient.mk (𝔐 ^ 2) x ∈ p.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact p.asIdeal.zero_mem
  obtain ⟨q, hqP⟩ : P ∈ Set.range (PrimeSpectrum.comap εε.toRingHom) := by
    rw [range_comap_of_surjective _ εε.toRingHom (augAug_surjective G B₁ ι hιf hιe)]
    exact h𝔐P
  refine hιe ⟨q, ?_⟩
  change G.unitSection q = universalMul G B₁ ι hιf P
  rw [← hqP, ← universalMul_aug G B₁ ι hιf hιe]
  rfl

/-- The product map on the chart, modulo the square of the augmentation ideal. -/
private noncomputable def mBar (G : RelativeGroupLaw R f) (B₁ : CommRingCat.{u})
    [Algebra R B₁] (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
    (hιe : Set.range G.unitSection ⊆ Set.range ι) : B₁ ⟶ CommRingCat.of
    (((B₁ : Type u) ⊗[R] B₁) ⧸ RingHom.ker (augAug G B₁ ι hιf hιe).toRingHom ^ 2) :=
  Spec.preimage (IsOpenImmersion.lift ι _ (range_truncMul_subset G B₁ ι hιf hιe))

private theorem map_mBar :
    Spec.map (mBar G B₁ ι hιf hιe) ≫ ι
      = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (RingHom.ker (augAug G B₁ ι hιf hιe).toRingHom ^ 2)))
        ≫ universalMul G B₁ ι hιf := by
  rw [mBar, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

variable {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
variable (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
variable (t : Spec R' ⟶ Spec (CommRingCat.of R))
variable [Algebra R R'] (htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom)

/-- `kerRing` as a map of `R`-algebras. -/
private noncomputable def kerAlg (G : RelativeGroupLaw R f) (B₁ : CommRingCat.{u})
    [Algebra R B₁] (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
    (hιe : Set.range G.unitSection ⊆ Set.range ι)
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S') (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥) (t : Spec R' ⟶ Spec (CommRingCat.of R))
    [Algebra R R'] (htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom)
    (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k) :
    (B₁ : Type u) →ₐ[R] R' :=
  { (kerRing G B₁ ι hιe φ hsurj hker t k hk).hom with
    commutes' := fun r => (preimage_lift_algebraMap B₁ ι hιf k.left _
      (Spec.preimage t) ((Over.w k).trans (Spec.map_preimage t).symm) r).trans
      (DFunLike.congr_fun htR'.symm r) }

private theorem kerAlg_apply (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k) (b : B₁) :
    kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = (kerRing G B₁ ι hιe φ hsurj hker t k hk).hom b := rfl

private theorem kerAlg_one :
    kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t) (isKerElt_one G φ t)
      = trivLift (aug G B₁ ι hιf hιe) := by
  apply AlgHom.ext
  intro b
  rw [kerAlg_apply, trivLift_apply]
  have heq : Spec.map (kerRing G B₁ ι hιe φ hsurj hker t (G.one t) (isKerElt_one G φ t))
      = t ≫ Spec.map (CommRingCat.ofHom (aug G B₁ ι hιf hιe).toRingHom) := by
    rw [← cancel_mono ι, map_kerRing, Category.assoc, map_aug, G.one_left]
    rfl
  have hmap : kerRing G B₁ ι hιe φ hsurj hker t (G.one t) (isKerElt_one G φ t)
      = CommRingCat.ofHom (aug G B₁ ι hιf hιe).toRingHom ≫ Spec.preimage t :=
    Spec.map_injective (heq.trans (by rw [Spec.map_comp, Spec.map_preimage]))
  refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmap) b).trans ?_
  exact DFunLike.congr_fun htR'.symm _

private theorem mul_eq_tensorPair_universalMul
    (x y : Over.mk t ⟶ Over.mk f) (hx : IsKerElt G φ t x) (hy : IsKerElt G φ t y) :
    (G.mul t x y).left
      = Spec.map (CommRingCat.ofHom (tensorPair
          (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' x hx)
          (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' y hy)).toRingHom)
        ≫ universalMul G B₁ ι hιf := by
  set ψ := tensorPair (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' x hx)
    (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' y hy)
  have hτ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ tensorStruct (R := R) B₁ = t := by
    rw [tensorStruct, ← Spec.map_comp, ← Spec.map_preimage t]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (ψ.commutes r).trans (DFunLike.congr_fun htR' r)
  have hξ : ∀ (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)) (z : Over.mk t ⟶ Over.mk f)
      (hz : IsKerElt G φ t z),
      ψ.comp ρ = kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' z hz →
      Over.homMk (U := Over.mk t) (V := Over.mk (tensorStruct (R := R) B₁))
          (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hτ ≫ tensorPoint B₁ ι hιf ρ = z :=
    fun ρ z hz hρ => by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, tensorPoint, ← Category.assoc,
      ← Spec.map_comp]
    rw [← map_kerRing G B₁ ι hιe φ hsurj hker t z hz]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun b => (DFunLike.congr_fun hρ b).trans rfl)
  have h := G.mul_natural (tensorStruct (R := R) B₁) t
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hτ
    (tensorPoint B₁ ι hιf includeLeft) (tensorPoint B₁ ι hιf includeRight)
  rw [hξ includeLeft x hx (Algebra.TensorProduct.lift_comp_includeLeft _ _ _),
    hξ includeRight y hy (Algebra.TensorProduct.lift_comp_includeRight' _ _ _)] at h
  exact (congrArg (fun x => x.left) h).symm

private theorem kerAlg_val_eq {k k' : Over.mk t ⟶ Over.mk f}
    (hk : IsKerElt G φ t k) (hk' : IsKerElt G φ t k') (h : k = k') (b : B₁) :
    kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k' hk' b := by
  subst h
  rfl

private theorem kerAlg_reduces (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k) (b : B₁) :
    φ.hom (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b)
      = φ.hom (trivLift (aug G B₁ ι hιf hιe) b) := by
  rw [kerAlg_apply, kerRing_reduces G B₁ ι hιe φ hsurj hker t k hk,
    ← kerAlg_apply G B₁ ι hιf hιe φ hsurj hker t htR', kerAlg_one]

private theorem kerAlg_mul_fourTerm (x y : Over.mk t ⟶ Over.mk f)
    (hx : IsKerElt G φ t x) (hy : IsKerElt G φ t y) (b : B₁) :
    kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.mul t x y) (isKerElt_mul G φ t hx hy) b
      - kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' x hx b
      - kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' y hy b
      + kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t) (isKerElt_one G φ t) b = 0 := by
  set ε₀ := aug G B₁ ι hιf hιe
  set εε := augAug G B₁ ι hιf hιe
  set 𝔐 := RingHom.ker εε.toRingHom
  have he := isKerElt_one G φ t
  have hψ2 : ∀ (p q : Over.mk t ⟶ Over.mk f) (hp : IsKerElt G φ t p)
      (hq : IsKerElt G φ t q), ∀ a ∈ 𝔐 ^ 2,
      (tensorPair (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
        (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' q hq)).toRingHom a = 0 :=
    fun p q hp hq a ha => eq_zero_of_mem_sq εε φ.hom hker _
      (tensorPair_lifts_trivLift ε₀ φ.hom _ _
        (kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
        (kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' q hq)) ha
  have hfac : ∀ (p q : Over.mk t ⟶ Over.mk f) (hp : IsKerElt G φ t p)
      (hq : IsKerElt G φ t q),
      kerRing G B₁ ι hιe φ hsurj hker t (G.mul t p q) (isKerElt_mul G φ t hp hq)
        = mBar G B₁ ι hιf hιe ≫ CommRingCat.ofHom (Ideal.Quotient.lift (𝔐 ^ 2)
            (tensorPair (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
              (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' q hq)).toRingHom
            (hψ2 p q hp hq)) := fun p q hp hq => by
    apply Spec.map_injective
    rw [← cancel_mono ι, map_kerRing, Spec.map_comp, Category.assoc,
      map_mBar, ← Category.assoc, ← Spec.map_comp,
      mul_eq_tensorPair_universalMul G B₁ ι hιf hιe φ hsurj hker t htR' p q hp hq]
    exact congrArg (· ≫ universalMul G B₁ ι hιf) (congrArg Spec.map
      (CommRingCat.hom_ext (RingHom.ext fun a =>
        (Ideal.Quotient.lift_mk (𝔐 ^ 2) _ (hψ2 p q hp hq) (a := a)).symm)))
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((mBar G B₁ ι hιf hιe).hom b)
  have h4 : ∀ (p q : Over.mk t ⟶ Over.mk f) (hp : IsKerElt G φ t p)
      (hq : IsKerElt G φ t q),
      kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.mul t p q) (isKerElt_mul G φ t hp hq) b
        = tensorPair (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
            (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' q hq) z := fun p q hp hq => by
    have step : (kerRing G B₁ ι hιe φ hsurj hker t (G.mul t p q)
          (isKerElt_mul G φ t hp hq)).hom b
        = Ideal.Quotient.lift (𝔐 ^ 2) _ (hψ2 p q hp hq) ((mBar G B₁ ι hιf hιe).hom b) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hfac p q hp hq)) b
    rw [kerAlg_apply, step, ← hz]
    exact Ideal.Quotient.lift_mk _ _ _
  rw [h4 x y hx hy,
    kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR' hx
      (isKerElt_mul G φ t hx he) (G.mul_one t x).symm b,
    h4 x (G.one t) hx he,
    kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR' hy
      (isKerElt_mul G φ t he hy) (G.one_mul t y).symm b,
    h4 (G.one t) y he hy,
    kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR' he
      (isKerElt_mul G φ t he he) (G.one_mul t (G.one t)).symm b,
    h4 (G.one t) (G.one t) he he, kerAlg_one]
  exact fourTerm_tensorPair ε₀ hker _ _
    (fun a ha => mem_ker_of_mem_augIdeal ε₀ φ.hom _
      (kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' x hx) ha)
    (fun a ha => mem_ker_of_mem_augIdeal ε₀ φ.hom _
      (kerAlg_reduces G B₁ ι hιf hιe φ hsurj hker t htR' y hy) ha) z

private theorem kerAlg_nsmul_sub (k : Over.mk t ⟶ Over.mk f) (hk : IsKerElt G φ t k)
    (m : ℕ) (b : B₁) :
    kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.nsmul t m k) (isKerElt_nsmul G φ t hk m) b
      - kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t) (isKerElt_one G φ t) b
    = m • (kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      - kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t) (isKerElt_one G φ t) b) := by
  induction m with
  | zero =>
    rw [zero_smul,
      kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR'
        (isKerElt_nsmul G φ t hk 0) (isKerElt_one G φ t) (G.nsmul_zero t k) b,
      sub_self]
  | succ m ih =>
    have h4 := kerAlg_mul_fourTerm G B₁ ι hιf hιe φ hsurj hker t htR'
      (G.nsmul t m k) k (isKerElt_nsmul G φ t hk m) hk b
    rw [kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR'
        (isKerElt_nsmul G φ t hk (m + 1))
        (isKerElt_mul G φ t (isKerElt_nsmul G φ t hk m) hk)
        (G.nsmul_succ t m k) b,
      succ_nsmul, ← ih]
    linear_combination h4

end TensorArgument

/-- Over a local ring in which `n` is a unit, a point over a square-zero thickening that
reduces to the identity and is killed by `n` is the identity. -/
theorem eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit [IsLocalRing R]
    (G : RelativeGroupLaw R f) {n : ℕ} (hn : IsUnit (n : R))
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S') (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : Over.mk t ⟶ Over.mk f)
    (hk : Over.homMk (U := Over.mk (Spec.map φ ≫ t)) (V := Over.mk t) (Spec.map φ) rfl ≫ k =
      G.one (Spec.map φ ≫ t))
    (hnk : G.nsmul t n k = G.one t) :
    k = G.one t := by
  let pt : (Spec (CommRingCat.of R) : Scheme.{u}) := IsLocalRing.closedPoint R
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := G.unitSection pt) (U := ⊤) trivial
  let B₁ : CommRingCat.{u} := Γ(A, U)
  let ι : Spec B₁ ⟶ A := hU.fromSpec
  let : Algebra R B₁ := (Spec.preimage (ι ≫ f)).hom.toAlgebra
  have hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)) :=
    (Spec.map_preimage (ι ≫ f)).symm.trans (congrArg Spec.map (CommRingCat.hom_ext rfl))
  have hιe : Set.range G.unitSection ⊆ Set.range ι := by
    have hrange : Set.range ι = U := hU.range_fromSpec
    have hpt : G.unitSection pt ∈ Set.range ι := by rw [hrange]; exact hxU
    have hopen : IsOpen (G.unitSection ⁻¹' Set.range ι) := by
      rw [hrange]
      exact U.isOpen.preimage G.unitSection.continuous
    rintro _ ⟨p, rfl⟩
    exact (IsLocalRing.specializes_closedPoint p).mem_open hopen hpt
  let : Algebra R R' := (Spec.preimage t).hom.toAlgebra
  have htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom := rfl
  have hδ := kerAlg_nsmul_sub G B₁ ι hιf hιe φ hsurj hker t htR' k hk n
  simp only [kerAlg_val_eq G B₁ ι hιf hιe φ hsurj hker t htR'
    (isKerElt_nsmul G φ t hk n) (isKerElt_one G φ t) hnk, sub_self, nsmul_eq_mul] at hδ
  have hun : IsUnit (n : R') := by
    have := hn.map (algebraMap R R')
    rwa [map_natCast] at this
  have hkR0 : ∀ b, kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = kerAlg G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t) (isKerElt_one G φ t) b :=
    fun b => sub_eq_zero.mp (hun.mul_left_cancel ((hδ b).symm.trans (mul_zero _).symm))
  refine eq_of_kerRing_eq G B₁ ι hιe φ hsurj hker t hk (isKerElt_one G φ t)
    (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
  exact (kerAlg_apply G B₁ ι hιf hιe φ hsurj hker t htR' k hk b).symm.trans
    ((hkR0 b).trans (kerAlg_apply G B₁ ι hιf hιe φ hsurj hker t htR' _ _ b))

/-- On a commutative relative group law over a local ring, multiplication by a natural number
`n` that is a unit in the base ring is formally unramified. -/
theorem formallyUnramified_schemeNsmul_of_isUnit [IsLocalRing R] (G : RelativeGroupLaw R f)
    (hc : G.IsCommutative) (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) :=
  G.formallyUnramified_schemeNsmul_of_forall_sqZero hc n
    (fun _ _ φ hφ hker t k hk hnk ↦
      G.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit hn φ hφ hker t k hk hnk)

/-- On a commutative relative group law over a local ring, smooth of relative dimension `d`
over the base, multiplication by a natural number `n` that is a unit in the base ring is
étale. -/
theorem etale_schemeNsmul_of_isUnit [IsLocalRing R] (G : RelativeGroupLaw R f)
    (hc : G.IsCommutative) (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ)
    (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) := by
  have hu : FormallyUnramified (G.schemeNsmul n) :=
    G.formallyUnramified_schemeNsmul_of_isUnit hc n hn
  have h1 : SmoothOfRelativeDimension d (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_comp]
    infer_instance
  exact RelativeGroupLawEtale.etale_of_formallyUnramified_of_smoothOfRelativeDimension d h1
    ‹_› hu

end RelativeGroupLaw

end AlgebraicGeometry
