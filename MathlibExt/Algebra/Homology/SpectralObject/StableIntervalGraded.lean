/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.SpectralObject.Page
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Stable intervals and ordered image quotients

For a spectral object over a bounded preorder, this file compares the stable
interval between two ordered cuts with the cokernel of the induced map
between their images in the bottom-to-top abutment object.  It makes no page,
first-quadrant, or convergence claim.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type u} [Category.{v} D] [Abelian D]
variable {ι : Type w} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (Y : SpectralObject D ι)

def stableIntervalLeft (i₁ : ι) : (⊥ : ι) ⟶ i₁ :=
  homOfLE bot_le

def stableIntervalMiddle {i₁ i₂ : ι} (h : i₁ ≤ i₂) : i₁ ⟶ i₂ :=
  homOfLE h

def stableIntervalRight (i₂ : ι) : i₂ ⟶ (⊤ : ι) :=
  homOfLE le_top

def stableIntervalLeftMiddle (i₂ : ι) : (⊥ : ι) ⟶ i₂ :=
  homOfLE bot_le

def stableIntervalFull : (⊥ : ι) ⟶ (⊤ : ι) :=
  homOfLE bot_le

omit [OrderTop ι] in
theorem stableIntervalLeft_comp_middle {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    stableIntervalLeft i₁ ≫ stableIntervalMiddle h =
      stableIntervalLeftMiddle i₂ :=
  Subsingleton.elim _ _

/-- The spectral step associated to the bottom-to-`i` interval. -/
noncomputable def stableIntervalStep (n : ℤ) (i : ι) : D :=
  (Y.H n).obj (mk₁ (stableIntervalLeftMiddle i))

/-- The bottom-to-top spectral object in degree `n`. -/
noncomputable def stableIntervalAbutment (n : ℤ) : D :=
  (Y.H n).obj (mk₁ stableIntervalFull)

/-- The map between spectral steps induced by an inequality of cuts. -/
noncomputable def stableIntervalStepMap
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStep n i₁ ⟶ Y.stableIntervalStep n i₂ :=
  (Y.H n).map
    (twoδ₂Toδ₁
      (stableIntervalLeft i₁)
      (stableIntervalMiddle h)
      (stableIntervalLeftMiddle i₂)
      (stableIntervalLeft_comp_middle h))

/-- The map from a spectral step to the bottom-to-top abutment object. -/
noncomputable def stableIntervalStepToAbutment (n : ℤ) (i : ι) :
    Y.stableIntervalStep n i ⟶ Y.stableIntervalAbutment n :=
  (Y.H n).map
    (homMk₁ (𝟙 _) (stableIntervalRight i) (by subsingleton))

@[reassoc]
theorem stableIntervalStepMap_comp_toAbutment
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToAbutment n i₂ =
      Y.stableIntervalStepToAbutment n i₁ := by
  dsimp only [stableIntervalStepMap, stableIntervalStepToAbutment]
  rw [← Functor.map_comp]
  apply (Y.H n).congr_map
  subsingleton

noncomputable abbrev stableIntervalStepImage (n : ℤ) (i : ι) : D :=
  Limits.image (Y.stableIntervalStepToAbutment n i)

/-- The canonical epimorphism from a step to its selected abutment image. -/
noncomputable def stableIntervalStepToImage (n : ℤ) (i : ι) :
    Y.stableIntervalStep n i ⟶
      Limits.image (Y.stableIntervalStepToAbutment n i) :=
  Limits.factorThruImage (Y.stableIntervalStepToAbutment n i)

instance stableIntervalStepToImage_epi (n : ℤ) (i : ι) :
    Epi (Y.stableIntervalStepToImage n i) := by
  dsimp only [stableIntervalStepToImage]
  infer_instance

/-- The map between selected abutment images at two ordered cuts. -/
noncomputable def stableIntervalImageMap
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Limits.image (Y.stableIntervalStepToAbutment n i₁) ⟶
      Limits.image (Y.stableIntervalStepToAbutment n i₂) :=
  (Limits.image.eqToIso
    (Y.stableIntervalStepMap_comp_toAbutment n h).symm).hom ≫
  Limits.image.preComp
    (Y.stableIntervalStepMap n h)
    (Y.stableIntervalStepToAbutment n i₂)

@[reassoc]
theorem stableIntervalImageMap_comp_ι
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫
        Limits.image.ι (Y.stableIntervalStepToAbutment n i₂) =
      Limits.image.ι (Y.stableIntervalStepToAbutment n i₁) := by
  dsimp only [stableIntervalImageMap]
  rw [Category.assoc, Limits.image.preComp_ι]
  exact (Limits.image.eq_fac
    (Y.stableIntervalStepMap_comp_toAbutment n h).symm).symm

@[reassoc]
theorem stableIntervalStepToImage_naturality
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToImage n i₂ =
      Y.stableIntervalStepToImage n i₁ ≫
        Y.stableIntervalImageMap n h := by
  apply (cancel_mono
    (Limits.image.ι (Y.stableIntervalStepToAbutment n i₂))).1
  simp only [stableIntervalStepToImage, Category.assoc, Limits.image.fac,
    Y.stableIntervalImageMap_comp_ι n h,
    Y.stableIntervalStepMap_comp_toAbutment n h]

/-- The direct stable interval between ordered cuts. -/
noncomputable def stableIntervalObj
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : D :=
  Y.E
    (stableIntervalLeft i₁)
    (stableIntervalMiddle h)
    (stableIntervalRight i₂)
    (n - 1) n (n + 1) (by omega) (by omega)

/-- The canonical cokernel sequence defining the stable interval. -/
noncomputable def stableIntervalCokernelSequence
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : ShortComplex D :=
  Y.cokernelSequenceE
    (stableIntervalLeft i₁)
    (stableIntervalMiddle h)
    (stableIntervalRight i₂)
    (stableIntervalLeftMiddle i₂)
    (stableIntervalLeft_comp_middle h)
    (n - 1) n (n + 1) (by omega) (by omega)

/-- The quotient from the current spectral step to the stable interval. -/
noncomputable def stableIntervalStepToStable
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStep n i₂ ⟶ Y.stableIntervalObj n h :=
  (Y.stableIntervalCokernelSequence n h).g

instance stableIntervalStepToStable_epi
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Epi (Y.stableIntervalStepToStable n h) := by
  change Epi (Y.cokernelSequenceE
      (stableIntervalLeft i₁)
      (stableIntervalMiddle h)
      (stableIntervalRight i₂)
      (stableIntervalLeftMiddle i₂)
      (stableIntervalLeft_comp_middle h)
      (n - 1) n (n + 1) (by omega) (by omega)).g
  infer_instance

@[reassoc]
theorem stableIntervalStepMap_comp_toStable_zero
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToStable n h = 0 := by
  let S := Y.stableIntervalCokernelSequence n h
  have hinl : biprod.inl ≫ S.f = Y.stableIntervalStepMap n h := by
    dsimp only [S, stableIntervalCokernelSequence, cokernelSequenceE,
      stableIntervalStepMap]
    simp only [biprod.inl_desc]
  change Y.stableIntervalStepMap n h ≫ S.g = 0
  rw [← hinl]
  exact (calc
    (biprod.inl ≫ S.f) ≫ S.g =
        biprod.inl ≫ (S.f ≫ S.g) := Category.assoc _ _ _
    _ = biprod.inl ≫ 0 := congrArg (fun k => biprod.inl ≫ k) S.zero
    _ = 0 := by simp)

@[reassoc]
theorem stableIntervalDelta_comp_toStable_zero
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) ≫
      Y.stableIntervalStepToStable n h = 0 := by
  let S := Y.stableIntervalCokernelSequence n h
  have hinr : biprod.inr ≫ S.f =
      Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) := by
    dsimp only [S, stableIntervalCokernelSequence, cokernelSequenceE]
    simp only [biprod.inr_desc]
  change _ ≫ S.g = 0
  rw [← hinr]
  exact (calc
    (biprod.inr ≫ S.f) ≫ S.g =
        biprod.inr ≫ (S.f ≫ S.g) := Category.assoc _ _ _
    _ = biprod.inr ≫ 0 := congrArg (fun k => biprod.inr ≫ k) S.zero
    _ = 0 := by simp)

/-- Implementation data for the stable quotient factored through the current
selected abutment image.  It is public because the transparent descended map
and characteristic below cannot depend on a private declaration under Lean's
module visibility rules. -/
noncomputable def stableIntervalImageToStableLift
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    { q : Limits.image (Y.stableIntervalStepToAbutment n i₂) ⟶
        Y.stableIntervalObj n h //
      Y.stableIntervalStepToImage n i₂ ≫ q =
        Y.stableIntervalStepToStable n h } := by
  let f₁₂ := stableIntervalLeftMiddle i₂
  let f₃ := stableIntervalRight i₂
  let f₁₂₃ : (⊥ : ι) ⟶ (⊤ : ι) := stableIntervalFull
  have hExact :=
    Y.exact₁ f₁₂ f₃ f₁₂₃ (Subsingleton.elim _ _)
      (n - 1) n (by omega)
  have hδ : Y.δ f₁₂ f₃ (n - 1) n (by omega) ≫
      Y.stableIntervalStepToStable n h = 0 :=
    Y.stableIntervalDelta_comp_toStable_zero n h
  let q := hExact.isColimitImage.desc
    (CokernelCofork.ofπ (Y.stableIntervalStepToStable n h) hδ)
  refine ⟨q, ?_⟩
  exact Cofork.IsColimit.π_desc hExact.isColimitImage

/-- The stable quotient descended through the current selected image. -/
noncomputable def stableIntervalImageToStable
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Limits.image (Y.stableIntervalStepToAbutment n i₂) ⟶
      Y.stableIntervalObj n h :=
  (Y.stableIntervalImageToStableLift n h).1

@[reassoc (attr := simp)]
theorem stableIntervalStepToImage_comp_imageToStable
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepToImage n i₂ ≫
        Y.stableIntervalImageToStable n h =
      Y.stableIntervalStepToStable n h :=
  (Y.stableIntervalImageToStableLift n h).2

instance stableIntervalImageToStable_epi
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Epi (Y.stableIntervalImageToStable n h) := by
  have hcomp : Epi
      (Y.stableIntervalStepToImage n i₂ ≫
        Y.stableIntervalImageToStable n h) := by
    rw [Y.stableIntervalStepToImage_comp_imageToStable n h]
    infer_instance
  let _ := hcomp
  exact epi_of_epi (Y.stableIntervalStepToImage n i₂)
    (Y.stableIntervalImageToStable n h)

/-- The connecting morphism for the current-to-top interval dies after
passing to the current selected abutment image. -/
@[reassoc]
theorem stableIntervalDelta_comp_toImage_zero
    (n : ℤ) (i₂ : ι) :
    Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) ≫
      Y.stableIntervalStepToImage n i₂ = 0 := by
  apply (cancel_mono
    (Limits.image.ι (Y.stableIntervalStepToAbutment n i₂))).1
  simp only [stableIntervalStepToImage, Category.assoc, Limits.image.fac,
    zero_comp]
  exact Y.zero₁
    (stableIntervalLeftMiddle i₂)
    (stableIntervalRight i₂)
    (stableIntervalFull (ι := ι))
    (Subsingleton.elim _ _) (n - 1) n

/-- The ordered image map followed by the stable quotient is zero. -/
@[reassoc]
theorem stableIntervalImageMap_comp_imageToStable_zero
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫
        Y.stableIntervalImageToStable n h = 0 := by
  apply (cancel_epi (Y.stableIntervalStepToImage n i₁)).1
  rw [← Category.assoc,
    ← Y.stableIntervalStepToImage_naturality n h,
    Category.assoc,
    Y.stableIntervalStepToImage_comp_imageToStable n h,
    Y.stableIntervalStepMap_comp_toStable_zero n h,
    comp_zero]

/-- The descended stable quotient is a cokernel of the ordered map between
selected abutment images. -/
noncomputable def stableIntervalImageToStableIsCokernel
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    IsColimit (CokernelCofork.ofπ
      (Y.stableIntervalImageToStable n h)
      (Y.stableIntervalImageMap_comp_imageToStable_zero n h)) := by
  let S := Y.stableIntervalCokernelSequence n h
  let eA := Y.stableIntervalStepToImage n i₁
  let eB := Y.stableIntervalStepToImage n i₂
  let _ : Epi S.g := by
    change Epi (Y.stableIntervalStepToStable n h)
    infer_instance
  let k : S.X₁ ⟶ Limits.image
      (Y.stableIntervalStepToAbutment n i₁) :=
    biprod.desc eA 0
  have hinl : biprod.inl ≫ S.f = Y.stableIntervalStepMap n h := by
    dsimp only [S, stableIntervalCokernelSequence, cokernelSequenceE,
      stableIntervalStepMap]
    simp only [biprod.inl_desc]
  have hinr : biprod.inr ≫ S.f =
      Y.δ (stableIntervalLeftMiddle i₂) (stableIntervalRight i₂)
        (n - 1) n (by omega) := by
    dsimp only [S, stableIntervalCokernelSequence, cokernelSequenceE]
    simp only [biprod.inr_desc]
  have hFac : S.f ≫ eB =
      k ≫ Y.stableIntervalImageMap n h := by
    apply biprod.hom_ext'
    · calc
        biprod.inl ≫ (S.f ≫ eB) =
            (biprod.inl ≫ S.f) ≫ eB :=
          (Category.assoc _ _ _).symm
        _ = Y.stableIntervalStepMap n h ≫ eB := by rw [hinl]
        _ = eA ≫ Y.stableIntervalImageMap n h :=
          Y.stableIntervalStepToImage_naturality n h
        _ = (biprod.inl ≫ k) ≫
            Y.stableIntervalImageMap n h := by
          dsimp only [k]
          rw [biprod.inl_desc]
        _ = biprod.inl ≫
            (k ≫ Y.stableIntervalImageMap n h) :=
          Category.assoc _ _ _
    · calc
        biprod.inr ≫ (S.f ≫ eB) =
            (biprod.inr ≫ S.f) ≫ eB :=
          (Category.assoc _ _ _).symm
        _ = Y.δ (stableIntervalLeftMiddle i₂)
              (stableIntervalRight i₂) (n - 1) n (by omega) ≫ eB := by
          rw [hinr]
        _ = 0 := Y.stableIntervalDelta_comp_toImage_zero n i₂
        _ = (biprod.inr ≫ k) ≫
            Y.stableIntervalImageMap n h := by
          dsimp only [k]
          simp only [biprod.inr_desc, zero_comp]
        _ = biprod.inr ≫
            (k ≫ Y.stableIntervalImageMap n h) :=
          Category.assoc _ _ _
  have hS : S.Exact := by
    dsimp only [S, stableIntervalCokernelSequence]
    exact Y.cokernelSequenceE_exact
      (stableIntervalLeft i₁)
      (stableIntervalMiddle h)
      (stableIntervalRight i₂)
      (stableIntervalLeftMiddle i₂)
      (stableIntervalLeft_comp_middle h)
      (n - 1) n (n + 1) (by omega) (by omega)
  refine CokernelCofork.IsColimit.ofπ'
    (Y.stableIntervalImageToStable n h)
    (Y.stableIntervalImageMap_comp_imageToStable_zero n h)
    (fun {A} t ht => ?_)
  have hbt : S.f ≫ (eB ≫ t) = 0 := by
    calc
      S.f ≫ (eB ≫ t) = (S.f ≫ eB) ≫ t :=
        (Category.assoc _ _ _).symm
      _ = (k ≫ Y.stableIntervalImageMap n h) ≫ t := by rw [hFac]
      _ = k ≫ (Y.stableIntervalImageMap n h ≫ t) :=
        Category.assoc _ _ _
      _ = 0 := by rw [ht, comp_zero]
  let l : S.X₃ ⟶ A :=
    hS.gIsCokernel.desc (CokernelCofork.ofπ (eB ≫ t) hbt)
  refine ⟨l, ?_⟩
  apply (cancel_epi eB).1
  rw [← Category.assoc,
    Y.stableIntervalStepToImage_comp_imageToStable n h]
  exact Cofork.IsColimit.π_desc hS.gIsCokernel

/-- The stable interval is canonically the cokernel of the ordered selected
image map. -/
noncomputable def stableIntervalImageCokernelIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ≅
      cokernel (Y.stableIntervalImageMap n h) :=
  (IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (Y.stableIntervalImageMap n h))
    (Y.stableIntervalImageToStableIsCokernel n h)).symm

/-- The stable/image-cokernel isomorphism identifies the descended quotient
with the canonical cokernel projection. -/
@[reassoc]
theorem stableIntervalImageToStable_comp_iso_hom
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageToStable n h ≫
        (Y.stableIntervalImageCokernelIso n h).hom =
      cokernel.π (Y.stableIntervalImageMap n h) := by
  simpa only [stableIntervalImageCokernelIso, Iso.symm_hom,
    parallelPair_obj_one, Cofork.app_one_eq_π, Cofork.ofπ_pt,
    Cofork.π_ofπ] using
    (IsColimit.comp_coconePointUniqueUpToIso_inv
      (cokernelIsCokernel (Y.stableIntervalImageMap n h))
      (Y.stableIntervalImageToStableIsCokernel n h)
      WalkingParallelPair.one)

end CategoryTheory.Abelian.SpectralObject

end
