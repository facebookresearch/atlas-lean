/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper.lean`
and
`P2M/Sol/S_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper.lean`
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
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Tactic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
  (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
  (z : Z ⟶ Spec (CommRingCat.of K))

private noncomputable abbrev sectionThrough (x₀ : Spec (CommRingCat.of K) ⟶ X)
    (hx₀ : x₀ ≫ x = 𝟙 _) : Y ⟶ pullback x y :=
  pullback.lift (y ≫ x₀) (𝟙 Y) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])

private noncomputable abbrev sliceThrough (y₀ : Spec (CommRingCat.of K) ⟶ Y)
    (hy₀ : y₀ ≫ y = 𝟙 _) : X ⟶ pullback x y :=
  pullback.lift (𝟙 X) (x ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id])

end

set_option maxHeartbeats 1600000 in

/-- Rigidity for maps out of a fibre product over an algebraically closed
field: a map from `pullback x y` to `Z` over the base that is constant on one
slice factors through the second projection. -/
theorem AlgebraicGeometry.exists_eq_pullback_snd_comp_of_isProper
    {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
    (z : Z ⟶ Spec (CommRingCat.of K))
    [IsProper x] [IsIntegral X] [IsIntegral Y] [IsSeparated z]
    [LocallyOfFiniteType y] [LocallyOfFiniteType z] [IsReduced (pullback x y)]
    (f : pullback x y ⟶ Z) (hf : f ≫ z = pullback.fst x y ≫ x)
    (y₀ : Spec (CommRingCat.of K) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _)
    (z₀ : Spec (CommRingCat.of K) ⟶ Z)
    (h : pullback.lift (𝟙 X) (x ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀,
      Category.comp_id]) ≫ f = x ≫ z₀) :
    ∃ g : Y ⟶ Z, f = pullback.snd x y ≫ g := by
  classical
  have hcond : pullback.fst x y ≫ x = pullback.snd x y ≫ y := pullback.condition

  have : Nonempty X := inferInstance
  obtain ⟨p₀, hp₀⟩ : ∃ p : X, IsClosed ({p} : Set X) := by
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace x
    have hcpd : Dense (closedPoints X) := by
      rw [dense_iff_closure_eq, closure_closedPoints]
    obtain ⟨p₀, hp₀⟩ := hcpd.nonempty
    exact ⟨p₀, mem_closedPoints_iff.mp hp₀⟩
  let x₀ : Spec (CommRingCat.of K) ⟶ X := pointOfClosedPoint x p₀ hp₀
  have hx₀ : x₀ ≫ x = 𝟙 _ := pointOfClosedPoint_comp x p₀ hp₀

  let σ : Y ⟶ pullback x y := sectionThrough x y x₀ hx₀
  have hσ_snd : σ ≫ pullback.snd x y = 𝟙 Y := pullback.lift_snd _ _ _
  have hσ_fst : σ ≫ pullback.fst x y = y ≫ x₀ := pullback.lift_fst _ _ _
  refine ⟨σ ≫ f, ?_⟩

  have hover : f ≫ z = (pullback.snd x y ≫ (σ ≫ f)) ≫ z := by
    have h1 : (pullback.snd x y ≫ (σ ≫ f)) ≫ z = pullback.snd x y ≫ σ ≫ (f ≫ z) := by
      simp only [Category.assoc]
    rw [h1, hf, reassoc_of% hσ_fst, hx₀, Category.comp_id, ← hcond, ← hf]

  have hmain : ∃ V : Y.Opens, (y₀ (IsLocalRing.closedPoint K)) ∈ V ∧
      ∀ w ∈ (pullback.snd x y).base ⁻¹' (V : Set Y),
        IsClosed ({w} : Set _) →
        f w = (pullback.snd x y ≫ (σ ≫ f)) w := by

    have hφc : f ≫ z = pullback.snd x y ≫ y := hf.trans hcond
    let φ : pullback x y ⟶ pullback z y := pullback.lift f (pullback.snd x y) hφc
    have hφ_fst : φ ≫ pullback.fst z y = f := pullback.lift_fst _ _ _
    have hφ_snd : φ ≫ pullback.snd z y = pullback.snd x y := pullback.lift_snd _ _ _
    haveI := LocallyOfFiniteType.jacobsonSpace (pullback.snd x y ≫ y)

    let σX : X ⟶ pullback x y := sliceThrough x y y₀ hy₀
    have hσX_fst : σX ≫ pullback.fst x y = 𝟙 X := pullback.lift_fst _ _ _
    have hσX_snd : σX ≫ pullback.snd x y = x ≫ y₀ := pullback.lift_snd _ _ _
    have hσX_f : σX ≫ f = x ≫ z₀ := h
    let d : Spec (CommRingCat.of K) ⟶ pullback z y := x₀ ≫ σX ≫ φ

    have hσXφ : σX ≫ φ = x ≫ d := by
      apply pullback.hom_ext
      · have hL : (σX ≫ φ) ≫ pullback.fst z y = x ≫ z₀ := by
          rw [Category.assoc, hφ_fst]; exact h
        have hR : (x ≫ d) ≫ pullback.fst z y = x ≫ z₀ := by
          simp only [d, Category.assoc, hφ_fst]
          rw [hσX_f, reassoc_of% hx₀]
        rw [hL, hR]
      · have hL : (σX ≫ φ) ≫ pullback.snd z y = x ≫ y₀ := by
          rw [Category.assoc, hφ_snd, hσX_snd]
        have hR : (x ≫ d) ≫ pullback.snd z y = x ≫ y₀ := by
          simp only [d, Category.assoc, hφ_snd]
          rw [hσX_snd, reassoc_of% hx₀]
        rw [hL, hR]

    have hH : (φ.base '' ((φ ≫ pullback.snd z y).base ⁻¹'
        {y₀ (IsLocalRing.closedPoint K)})).Finite := by
      refine Set.Finite.subset (Set.finite_singleton (d (IsLocalRing.closedPoint K))) ?_
      rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
      intro H
      have hpt : IsClosed ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) :=
        isClosed_discrete _
      haveI : IsClosedImmersion y₀ := isClosedImmersion_of_comp_eq_id y y₀ hy₀
      have hdsnd : d ≫ pullback.snd z y = y₀ := by
        simp only [d, Category.assoc, hφ_snd]
        rw [hσX_snd, reassoc_of% hx₀]
      have hdsec : d ≫ pullback.snd z y ≫ y = 𝟙 _ := by
        rw [← Category.assoc, hdsnd, hy₀]
      haveI : IsClosedImmersion d :=
        isClosedImmersion_of_comp_eq_id (pullback.snd z y ≫ y) d hdsec
      have hy₀closed : IsClosed ({y₀ (IsLocalRing.closedPoint K)} : Set Y) :=
        Set.image_singleton ▸ y₀.isClosedMap _ hpt
      have hdclosed : IsClosed ({d (IsLocalRing.closedPoint K)} : Set _) :=
        Set.image_singleton ▸ d.isClosedMap _ hpt
      obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H
        (IsLocallyClosed.inter
          (hy₀closed.preimage (φ ≫ pullback.snd z y).base.hom.2).isLocallyClosed
          (hdclosed.preimage φ.base.hom.2).isOpen_compl.isLocallyClosed)
      ·
        obtain ⟨⟨c, hc⟩, e⟩ :=
          (pointEquivClosedPoint (pullback.snd x y ≫ y)).surjective ⟨c₀, hc₃⟩
        obtain rfl : c (IsLocalRing.closedPoint K) = c₀ := congr(($e).1)
        have hcy : (c ≫ pullback.snd x y) ≫ y = 𝟙 _ := by
          rw [Category.assoc]; exact hc
        have hcsnd : c ≫ pullback.snd x y = y₀ := by
          refine ext_of_apply_closedPoint_eq y hcy hy₀ ?_
          have h1 : (φ ≫ pullback.snd z y) (c (IsLocalRing.closedPoint K))
              = y₀ (IsLocalRing.closedPoint K) := hc₁
          rw [hφ_snd] at h1
          exact h1
        have hcx : (c ≫ pullback.fst x y) ≫ x = 𝟙 _ := by
          rw [Category.assoc, hcond, ← Category.assoc, hcsnd, hy₀]
        have hfact : c ≫ φ = ((c ≫ pullback.fst x y) ≫ x) ≫ d := by
          have hcfac : c = (c ≫ pullback.fst x y) ≫ σX := by
            apply pullback.hom_ext
            · rw [Category.assoc, hσX_fst, Category.comp_id]
            · rw [Category.assoc, hσX_snd, ← Category.assoc, hcx, Category.id_comp, hcsnd]
          calc c ≫ φ = ((c ≫ pullback.fst x y) ≫ σX) ≫ φ := by rw [← hcfac]
            _ = (c ≫ pullback.fst x y) ≫ σX ≫ φ := by rw [Category.assoc]
            _ = (c ≫ pullback.fst x y) ≫ x ≫ d := by rw [hσXφ]
            _ = ((c ≫ pullback.fst x y) ≫ x) ≫ d := by simp only [Category.assoc]
        apply hc₂
        have h6 : c ≫ φ = d := hfact.trans (by rw [hcx, Category.id_comp])
        have h7 := congrArg (fun (t : Spec (CommRingCat.of K) ⟶ pullback z y) =>
          t (IsLocalRing.closedPoint K)) h6
        simp only at h7
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact h7

    haveI : IsProper (φ ≫ pullback.snd z y) := by
      rw [hφ_snd]; infer_instance
    obtain ⟨V, hy₀V, hVfin⟩ :=
      exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
        φ (pullback.snd z y) (y₀ (IsLocalRing.closedPoint K)) hH
    refine ⟨V, hy₀V, ?_⟩
    intro w hw hwc

    have hvC : IsClosed ({(pullback.snd x y) w} : Set Y) := by
      simpa using (pullback.snd x y).isClosedMap _ hwc
    haveI hφproper : IsProper φ := by
      haveI : IsProper (φ ≫ pullback.snd z y) := by rw [hφ_snd]; infer_instance
      exact .of_comp _ (pullback.snd z y)
    have hfibr : ((pullback.snd z y).base ⁻¹' {(pullback.snd x y) w}
        ∩ Set.range φ.base).Finite := by
      refine ((((φ.imageι ≫ pullback.snd z y) ∣_ V).finite_preimage_singleton
        ⟨_, hw⟩).image (Scheme.Opens.ι _ ≫ φ.imageι)).subset ?_
      rintro a ⟨ha_pre, b, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha_pre
      have hmem : φ.toImage b ∈ (φ.imageι ≫ pullback.snd z y) ⁻¹ᵁ V := by
        show (φ.imageι ≫ pullback.snd z y) (φ.toImage b) ∈ V
        rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply φ.toImage, φ.toImage_imageι]
        exact ha_pre ▸ hw
      refine ⟨⟨φ.toImage b, hmem⟩, ?_, ?_⟩
      · show _ ∈ Set.preimage _ {(⟨_, hw⟩ : V)}
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        apply Subtype.ext
        have hmc := morphismRestrict_base_coe (φ.imageι ≫ pullback.snd z y) V
          ⟨φ.toImage b, hmem⟩
        rw [hmc]
        rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply φ.toImage, φ.toImage_imageι]
        exact ha_pre
      · show φ.imageι (φ.toImage b) = φ b
        rw [← Scheme.Hom.comp_apply, φ.toImage_imageι]
    have hfib : (φ.base '' ((pullback.snd x y).base ⁻¹' {(pullback.snd x y) w})).Finite := by
      refine hfibr.subset ?_
      rintro _ ⟨w', hw', rfl⟩
      refine ⟨?_, Set.mem_range_self _⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw' ⊢
      rw [← Scheme.Hom.comp_apply, hφ_snd]
      exact hw'
    have hffib : (f.base '' ((pullback.snd x y).base ⁻¹' {(pullback.snd x y) w})).Finite := by
      have hcomp : f.base '' ((pullback.snd x y).base ⁻¹' {(pullback.snd x y) w})
          = (pullback.fst z y).base '' (φ.base ''
            ((pullback.snd x y).base ⁻¹' {(pullback.snd x y) w})) := by
        rw [← Set.image_comp]
        refine Set.image_congr fun a _ => ?_
        have : (φ ≫ pullback.fst z y) a = f a := by rw [hφ_fst]
        simpa [Scheme.Hom.comp_apply] using this.symm
      rw [hcomp]
      exact hfib.image _

    let vpt : Spec (CommRingCat.of K) ⟶ Y := pointOfClosedPoint y ((pullback.snd x y) w) hvC
    have hvpt : vpt ≫ y = 𝟙 _ := pointOfClosedPoint_comp y _ hvC
    have hvpt_apply : vpt (IsLocalRing.closedPoint K) = (pullback.snd x y) w :=
      pointOfClosedPoint_apply y _ hvC _
    let σv : X ⟶ pullback x y := sliceThrough x y vpt hvpt
    have hσv_fst : σv ≫ pullback.fst x y = 𝟙 X := pullback.lift_fst _ _ _
    have hσv_snd : σv ≫ pullback.snd x y = x ≫ vpt := pullback.lift_snd _ _ _

    have hSv : Set.range σv.base = (pullback.snd x y).base ⁻¹' {(pullback.snd x y) w} := by
      apply Set.Subset.antisymm
      · rintro _ ⟨p, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        rw [← Scheme.Hom.comp_apply, hσv_snd, Scheme.Hom.comp_apply]
        rw [Subsingleton.elim (x p) (IsLocalRing.closedPoint K), hvpt_apply]
      ·
        have e₂ : y ≫ 𝟙 _ = (y ≫ vpt) ≫ y := by
          rw [Category.assoc, hvpt]
        let γv : pullback x y ⟶ pullback x y :=
          pullback.map x y x y (𝟙 X) (y ≫ vpt) (𝟙 _) (by simp) e₂
        have hγv_range : Set.range γv.base
            = (pullback.snd x y).base ⁻¹' Set.range (y ≫ vpt).base := by
          rw [Scheme.Pullback.range_map]
          simp [Set.range_id]
        have hγσ : γv = pullback.fst x y ≫ σv := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Category.assoc, hσv_fst]
          · rw [pullback.lift_snd, Category.assoc, hσv_snd, ← Category.assoc, ← hcond,
              Category.assoc]
        intro w' hw'
        have hw'γ : w' ∈ Set.range γv.base := by
          rw [hγv_range]
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw' ⊢
          refine ⟨(pullback.snd x y) w', ?_⟩
          rw [Scheme.Hom.comp_apply]
          rw [Subsingleton.elim (y ((pullback.snd x y) w')) (IsLocalRing.closedPoint K),
            hvpt_apply, hw']
        obtain ⟨a, ha⟩ := hw'γ
        refine ⟨(pullback.fst x y) a, ?_⟩
        rw [← ha, hγσ]
        rw [Scheme.Hom.comp_apply]

    haveI := LocallyOfFiniteType.jacobsonSpace x
    haveI hPσvf : IsProper (σv ≫ f) := by
      have h1 : (σv ≫ f) ≫ z = x := by
        rw [Category.assoc, hf, ← Category.assoc, hσv_fst, Category.id_comp]
      haveI : IsProper ((σv ≫ f) ≫ z) := by rw [h1]; infer_instance
      exact .of_comp _ z
    have hsub : ((σv ≫ f).base '' closure Set.univ).Subsingleton := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        isOpen_univ.isLocallyClosed (IrreducibleSpace.isIrreducible_univ X).2
        (σv ≫ f).base.hom.2 (σv ≫ f).isClosedMap ?_
      rw [Set.image_univ]
      have : Set.range (σv ≫ f).base = f.base '' Set.range σv.base := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp]
        exact Set.range_comp _ _
      rw [this, hSv]
      exact hffib
    rw [closure_univ, Set.image_univ] at hsub

    have hw_in : w ∈ Set.range σv.base := by
      rw [hSv]; exact Set.mem_singleton _
    obtain ⟨p, hp⟩ := hw_in
    have hσ_in : σ ((pullback.snd x y) w) ∈ Set.range σv.base := by

      have hcomp : vpt ≫ σ = x₀ ≫ σv := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hσ_fst, hσv_fst, Category.comp_id,
            ← Category.assoc, hvpt, Category.id_comp]
        · rw [Category.assoc, Category.assoc, hσ_snd, hσv_snd, Category.comp_id,
            ← Category.assoc, hx₀, Category.id_comp]
      refine ⟨x₀ (IsLocalRing.closedPoint K), ?_⟩
      have h8 := congrArg (fun (t : Spec (CommRingCat.of K) ⟶ pullback x y) =>
        t (IsLocalRing.closedPoint K)) hcomp
      simp only at h8
      have h8' : σ (vpt (IsLocalRing.closedPoint K))
          = σv (x₀ (IsLocalRing.closedPoint K)) := h8
      rw [hvpt_apply] at h8'
      exact h8'.symm
    obtain ⟨q, hq⟩ := hσ_in

    have h1 : f w = (σv ≫ f) p := by
      rw [Scheme.Hom.comp_apply, hp]
    have h2 : (pullback.snd x y ≫ (σ ≫ f)) w = (σv ≫ f) q := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hq]
    rw [h1, h2]
    exact hsub ⟨p, rfl⟩ ⟨q, rfl⟩

  haveI : LocallyOfFiniteType (f ≫ z) := by
    rw [hf]
    infer_instance
  obtain ⟨V, hy₀V, hagree⟩ := hmain
  have hVdense2 : Dense (V : Set Y) := V.isOpen.dense ⟨_, hy₀V⟩
  have hsndOpen2 : IsOpenMap ((pullback.snd x y).base) := by
    haveI : UniversallyOpen x := inferInstance
    exact (pullback.snd x y).isOpenMap
  have hSdense2 : Dense ((pullback.snd x y).base ⁻¹' (V : Set Y)) :=
    hVdense2.preimage hsndOpen2
  haveI : LocallyOfFiniteType (f ≫ z) := by
    rw [hf]
    infer_instance
  exact ext_of_apply_eq z ((pullback.snd x y).base ⁻¹' (V : Set Y))
    (V.isOpen.preimage (pullback.snd x y).base.hom.2).isLocallyClosed hSdense2 hagree hover
