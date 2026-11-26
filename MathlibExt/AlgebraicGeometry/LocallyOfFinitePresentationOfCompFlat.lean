/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective.lean`
and
`P2M/Sol/S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_flat_of_surjective.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import MathlibExt.RingTheory.Finiteness.FinitePresentationOfFaithfullyFlat
import Mathlib.Tactic.Algebraize

/-!
# Descent of local finite presentation along flat surjective covers

If `f : X ⟶ Y` is flat, surjective and locally of finite presentation, and `f ≫ g` is locally of
finite presentation, then `g : Y ⟶ Z` is locally of finite presentation. Since `f` is open, every
affine open `V` of `Y` is the image of a quasi-compact open of `X`. A finite affine cover of that
open is a faithfully flat, finitely presented `Γ(Y, V)`-algebra, and the affine statement
`Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation` applies.

## Main results

* `AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`: local finite
  presentation descends along a flat, surjective, locally finitely presented morphism.

## References

* [Stacks Project, Lemma 35.14.3 (Tag 02KL)](https://stacks.math.columbia.edu/tag/02KL)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem exists_affine_cover (W : Scheme.{u}) [CompactSpace W] :
    ∃ (T : Scheme.{u}) (p : T ⟶ W), Surjective p ∧ Flat p ∧
      LocallyOfFinitePresentation p ∧ IsAffine T := by
  let 𝒰 := W.affineCover.finiteSubcover
  let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ W := Sigma.desc (fun i ↦ 𝒰.f i)
  have hι : ∀ i, Sigma.ι (fun i : 𝒰.I₀ ↦ 𝒰.X i) i ≫ p = 𝒰.f i :=
    fun i ↦ Sigma.ι_comp_desc _ _
  refine ⟨_, p, ⟨fun x ↦ ?_⟩, inferInstance,
    @IsZariskiLocalAtSource.sigmaDesc _
      (HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation))
      _ _ _ _ _ (fun _ ↦ inferInstance), inferInstance⟩
  obtain ⟨i, x, rfl⟩ := W.affineCover.finiteSubcover.exists_eq x
  use Sigma.ι W.affineCover.finiteSubcover.X i x
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]

/-- **Local finite presentation descends along flat surjective covers.** If `f : X ⟶ Y` is flat,
surjective and locally of finite presentation, and the composite `f ≫ g` is locally of finite
presentation, then `g : Y ⟶ Z` is locally of finite presentation.

In other words, local finite presentation descends along a flat, surjective, locally finitely
presented cover: it can be checked after precomposing with such a cover.

Source: [Stacks Project, Lemma 35.14.3 (Tag 02KL)](https://stacks.math.columbia.edu/tag/02KL). -/
public theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f]
    [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have hU : IsAffineOpen (U : Z.Opens) := U.2
  have hV : IsAffineOpen (V : Y.Opens) := V.2
  -- `f` is flat and locally of finite presentation, hence open, so the quasi-compact open `V`
  -- is the image of a quasi-compact open `W` of `X`.
  obtain ⟨W : X.Opens, hWc, hWV⟩ :=
    f.isOpenMap.exists_opens_image_eq_of_prespectralSpace f.continuous
      (fun y _ ↦ Set.mem_range.mpr (f.surjective y)) (V : Y.Opens).isOpen hV.isCompact
  have : CompactSpace (W : X.Opens) := isCompact_iff_compactSpace.mp hWc
  obtain ⟨T, p, hp, hpflat, hplfp, hT⟩ := exists_affine_cover (W : X.Opens)
  let q : T ⟶ Y := p ≫ W.ι ≫ f
  have hT' : IsAffineOpen (⊤ : T.Opens) := isAffineOpen_top T
  have hqapp : ∀ t : T, q t = f (p t).val := fun t ↦ by
    simp only [q, Scheme.Hom.comp_apply]; rfl
  have eq : (⊤ : T.Opens) ≤ q ⁻¹ᵁ (V : Y.Opens) := by
    rintro t -
    rw [Scheme.Hom.mem_preimage, hqapp]
    have hpt : f (p t).val ∈ f '' (W : Set X) := Set.mem_image_of_mem f (p t).2
    rw [hWV] at hpt
    exact hpt
  have eqU : (⊤ : T.Opens) ≤ (q ≫ g) ⁻¹ᵁ (U : Z.Opens) := by
    rw [Scheme.Hom.comp_preimage]; exact eq.trans (Scheme.Hom.preimage_mono q e)
  let Tt : T.affineOpens := ⟨⊤, hT'⟩
  set φRA : (Γ(Z, U) : Type u) →+* Γ(Y, V) := (g.appLE U V e).hom with hφRA
  set φAB : (Γ(Y, V) : Type u) →+* Γ(T, ⊤) := (q.appLE V ⊤ eq).hom with hφAB
  have hcomp : φAB.comp φRA = ((q ≫ g).appLE U ⊤ eqU).hom := by
    rw [hφRA, hφAB, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have : Flat q := by simp only [q]; infer_instance
  have : LocallyOfFinitePresentation q := by simp only [q]; infer_instance
  have : LocallyOfFinitePresentation (q ≫ g) := by
    have : q ≫ g = p ≫ W.ι ≫ (f ≫ g) := by simp only [q, Category.assoc]
    rw [this]; infer_instance
  have hflat : φAB.Flat := by
    rw [hφAB]; exact HasRingHomProperty.appLE (P := @Flat) (f := q) inferInstance V Tt eq
  have hfpAB : φAB.FinitePresentation := by
    rw [hφAB]
    exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := q)
      inferInstance V Tt eq
  have hfpRB : (φAB.comp φRA).FinitePresentation := by
    rw [hcomp]
    exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) (f := q ≫ g)
      inferInstance U Tt eqU
  have hsurj : Function.Surjective (PrimeSpectrum.comap φAB) := by
    intro 𝔭
    have hy : hV.fromSpec 𝔭 ∈ (V : Y.Opens) := by
      have : hV.fromSpec 𝔭 ∈ Set.range hV.fromSpec := ⟨𝔭, rfl⟩
      rwa [hV.range_fromSpec] at this
    obtain ⟨x, hxW, hx⟩ : hV.fromSpec 𝔭 ∈ f '' (W : Set X) := by rw [hWV]; exact hy
    obtain ⟨t, ht⟩ := hp.surj ⟨x, hxW⟩
    have hqt : q t = hV.fromSpec 𝔭 := by rw [hqapp, ht, ← hx]
    have htr : t ∈ Set.range hT'.fromSpec := by rw [hT'.range_fromSpec]; trivial
    obtain ⟨𝔮, rfl⟩ := htr
    refine ⟨𝔮, ?_⟩
    apply hV.fromSpec.isOpenEmbedding.injective
    have hnat := IsAffineOpen.SpecMap_appLE_fromSpec q hV hT' eq
    have h1 : hV.fromSpec ((Spec.map (q.appLE V ⊤ eq)) 𝔮) = q (hT'.fromSpec 𝔮) := by
      rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply]
    rw [← hqt, ← h1, hφAB]
    rfl
  algebraize [φRA, φAB, φAB.comp φRA]
  have : Module.FaithfullyFlat (Γ(Y, V) : Type u) (Γ(T, ⊤) : Type u) :=
    Module.FaithfullyFlat.of_comap_surjective hsurj
  have hRT : Algebra.FinitePresentation (Γ(Z, U) : Type u) (Γ(T, ⊤) : Type u) :=
    RingHom.finitePresentation_algebraMap.1 hfpRB
  have hST : Algebra.FinitePresentation (Γ(Y, V) : Type u) (Γ(T, ⊤) : Type u) :=
    RingHom.finitePresentation_algebraMap.1 hfpAB
  exact Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation
    (Γ(Z, U) : Type u) (Γ(Y, V) : Type u) (Γ(T, ⊤) : Type u)

end AlgebraicGeometry
