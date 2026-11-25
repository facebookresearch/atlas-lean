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

public import MathlibExt.Algebra.Homology.SpectralObject.EndpointStabilization

/-!
# The actual endpoint abutment filtration

The spectral-object exact sequence identifies each endpoint image with the
kernel of restriction to the complementary interval. The ordered image
quotient therefore gives the associated graded of this actual kernel
filtration. Its object is the original bottom-to-top interval of the
spectral object.
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

/-- Restriction from the full endpoint interval to the interval above a cut. -/
def stableIntervalAbutmentRestriction (n : ℤ) (i : ι) :
    Y.stableIntervalAbutment n ⟶ (Y.H n).obj (mk₁ (stableIntervalRight i)) :=
  (Y.H n).map
    (twoδ₁Toδ₀ (stableIntervalLeftMiddle i) (stableIntervalRight i)
      (stableIntervalFull (ι := ι)) (by subsingleton))

/-- The kernel of the actual restriction from the full endpoint interval. -/
def stableIntervalKernelFiltration (n : ℤ) (i : ι) :
    Subobject (Y.stableIntervalAbutment n) :=
  kernelSubobject (Y.stableIntervalAbutmentRestriction n i)

/-- Exactness identifies the actual endpoint step image with the kernel of
restriction. The abutment object and both maps belong to the spectral object. -/
theorem stableIntervalImage_eq_kernel (n : ℤ) (i : ι) :
    imageSubobject (Y.stableIntervalStepToAbutment n i) =
      Y.stableIntervalKernelFiltration n i :=
  (ShortComplex.exact_iff_image_eq_kernel _).mp
    (Y.exact₂ (stableIntervalLeftMiddle i) (stableIntervalRight i)
      (stableIntervalFull (ι := ι)) (by subsingleton) n)

/-- The actual kernel filtration increases with the spectral cut. -/
theorem stableIntervalKernelFiltration_monotone (n : ℤ) :
    Monotone (Y.stableIntervalKernelFiltration n) := by
  intro i₁ i₂ h
  rw [← Y.stableIntervalImage_eq_kernel n i₁, ← Y.stableIntervalImage_eq_kernel n i₂,
    ← Y.stableIntervalStepMap_comp_toAbutment n h]
  exact imageSubobject_comp_le _ _

/-- The canonical comparison between a selected endpoint image and the
corresponding actual restriction kernel subobject. -/
def stableIntervalImageKernelIso (n : ℤ) (i : ι) :
    Y.stableIntervalStepImage n i ≅ (Y.stableIntervalKernelFiltration n i : D) :=
  (imageSubobjectIso (Y.stableIntervalStepToAbutment n i)).symm ≪≫
    Subobject.isoOfEq _ _ (Y.stableIntervalImage_eq_kernel n i)

@[reassoc]
theorem stableIntervalImageKernelIso_hom_arrow (n : ℤ) (i : ι) :
    (Y.stableIntervalImageKernelIso n i).hom ≫
        (Y.stableIntervalKernelFiltration n i).arrow =
      Limits.image.ι (Y.stableIntervalStepToAbutment n i) := by
  dsimp only [stableIntervalImageKernelIso, Iso.trans_hom, Iso.symm_hom, Subobject.isoOfEq]
  rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow']

/-- The selected image comparisons identify ordered image maps with the
actual kernel filtration inclusions. -/
@[reassoc]
theorem stableIntervalImageKernelIso_ordered
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫ (Y.stableIntervalImageKernelIso n i₂).hom =
      (Y.stableIntervalImageKernelIso n i₁).hom ≫
        Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h) := by
  apply (cancel_mono (Y.stableIntervalKernelFiltration n i₂).arrow).1
  simp only [Category.assoc, Y.stableIntervalImageKernelIso_hom_arrow,
    Y.stableIntervalImageMap_comp_ι, Subobject.ofLE_arrow]

/-- The associated graded of the actual restriction kernel filtration. -/
abbrev stableIntervalKernelGraded (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : D :=
  cokernel (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h))

/-- The actual image quotient identifies with the actual kernel-filtration
quotient, using the canonical subobject comparisons. -/
def stableIntervalImageKernelGradedIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel (Y.stableIntervalImageMap n h) ≅ Y.stableIntervalKernelGraded n h :=
  cokernel.mapIso (Y.stableIntervalImageMap n h)
    (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h))
    (Y.stableIntervalImageKernelIso n i₁) (Y.stableIntervalImageKernelIso n i₂)
    (Y.stableIntervalImageKernelIso_ordered n h)

/-- The stable interval is the associated graded of the actual restriction
kernel filtration of the original full endpoint object. -/
def stableIntervalKernelGradedIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ≅ Y.stableIntervalKernelGraded n h :=
  Y.stableIntervalImageCokernelIso n h ≪≫ Y.stableIntervalImageKernelGradedIso n h

/-- A finite-window object with vanishing omitted endpoint intervals is an
actual associated-graded quotient of the restriction kernel filtration. -/
def finiteIntervalKernelGradedIso
    (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    Y.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        (n - 1) n (n + 1) (by omega) (by omega) ≅
      Y.stableIntervalKernelGraded n h₁₂ :=
  Y.finiteIntervalImageCokernelIso n h₀₁ h₁₂ h₂₃ hleft hright ≪≫
    Y.stableIntervalImageKernelGradedIso n h₁₂

/-- A zero remainder makes the restriction kernel the full abutment. -/
theorem stableIntervalKernelFiltration_eq_top (n : ℤ) (i : ι)
    (h : IsZero ((Y.H n).obj (mk₁ (stableIntervalRight i)))) :
    Y.stableIntervalKernelFiltration n i = ⊤ := by
  have hzero : Y.stableIntervalAbutmentRestriction n i = 0 := h.eq_of_tgt _ _
  simp only [stableIntervalKernelFiltration, hzero, kernelSubobject_zero]

/-- A zero endpoint step makes the restriction kernel zero. -/
theorem stableIntervalKernelFiltration_eq_bot (n : ℤ) (i : ι)
    (h : IsZero (Y.stableIntervalStep n i)) :
    Y.stableIntervalKernelFiltration n i = ⊥ := by
  rw [← Y.stableIntervalImage_eq_kernel]
  have hzero : Y.stableIntervalStepToAbutment n i = 0 := h.eq_of_src _ _
  rw [hzero, imageSubobject_zero]

variable {Y Z : SpectralObject D ι}

namespace Hom

/-- The actual naturality square for the restriction from the endpoint object. -/
def stableIntervalRestrictionArrow (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    Arrow.mk (Y.stableIntervalAbutmentRestriction n i) ⟶
      Arrow.mk (Z.stableIntervalAbutmentRestriction n i) :=
  Arrow.homMk'
    ((φ.hom n).app (mk₁ (stableIntervalFull (ι := ι))))
    ((φ.hom n).app (mk₁ (stableIntervalRight i)))
    ((φ.hom n).naturality
      (twoδ₁Toδ₀ (stableIntervalLeftMiddle i) (stableIntervalRight i)
        (stableIntervalFull (ι := ι)) (by subsingleton))).symm

/-- The map on actual restriction kernel subobjects. -/
def stableIntervalKernelMap (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    (Y.stableIntervalKernelFiltration n i : D) ⟶
      (Z.stableIntervalKernelFiltration n i : D) :=
  kernelSubobjectMap (φ.stableIntervalRestrictionArrow n i)

@[reassoc]
theorem stableIntervalKernelMap_arrow (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    φ.stableIntervalKernelMap n i ≫ (Z.stableIntervalKernelFiltration n i).arrow =
      (Y.stableIntervalKernelFiltration n i).arrow ≫
        (φ.hom n).app (mk₁ (stableIntervalFull (ι := ι))) :=
  kernelSubobjectMap_arrow (φ.stableIntervalRestrictionArrow n i)

/-- Kernel maps commute with the ordered filtration inclusions. -/
@[reassoc]
theorem stableIntervalKernelMap_ordered (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h) ≫
        φ.stableIntervalKernelMap n i₂ =
      φ.stableIntervalKernelMap n i₁ ≫
        Subobject.ofLE _ _ (Z.stableIntervalKernelFiltration_monotone n h) := by
  apply (cancel_mono (Z.stableIntervalKernelFiltration n i₂).arrow).1
  simp only [Category.assoc, stableIntervalKernelMap_arrow,
    Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow, stableIntervalKernelMap_arrow]

/-- The canonical image-to-kernel comparison retains the actual maps on
images and on restriction kernels. -/
@[reassoc]
theorem stableIntervalImageKernelIso_naturality (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    φ.stableIntervalImageMap n i ≫ (Z.stableIntervalImageKernelIso n i).hom =
      (Y.stableIntervalImageKernelIso n i).hom ≫ φ.stableIntervalKernelMap n i := by
  apply (cancel_mono (Z.stableIntervalKernelFiltration n i).arrow).1
  simp only [Category.assoc, Z.stableIntervalImageKernelIso_hom_arrow,
    stableIntervalImageMap_ι, stableIntervalKernelMap_arrow,
    Y.stableIntervalImageKernelIso_hom_arrow_assoc]

/-- The map induced on the actual restriction-kernel associated graded. -/
def stableIntervalKernelGradedMap (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalKernelGraded n h ⟶ Z.stableIntervalKernelGraded n h :=
  cokernel.desc (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h))
    (φ.stableIntervalKernelMap n i₂ ≫
      cokernel.π (Subobject.ofLE _ _ (Z.stableIntervalKernelFiltration_monotone n h))) (by
      rw [← Category.assoc, φ.stableIntervalKernelMap_ordered n h,
        Category.assoc, cokernel.condition, comp_zero])

@[reassoc]
theorem stableIntervalKernelGradedMap_π (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h)) ≫
        φ.stableIntervalKernelGradedMap n h =
      φ.stableIntervalKernelMap n i₂ ≫
        cokernel.π (Subobject.ofLE _ _ (Z.stableIntervalKernelFiltration_monotone n h)) :=
  cokernel.π_desc _ _ _

end Hom

/-- The image-to-kernel graded comparison preserves the actual quotient map. -/
@[reassoc]
theorem stableIntervalImageKernelGradedIso_π (Y : SpectralObject D ι)
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel.π (Y.stableIntervalImageMap n h) ≫
        (Y.stableIntervalImageKernelGradedIso n h).hom =
      (Y.stableIntervalImageKernelIso n i₂).hom ≫
        cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h)) :=
  cokernel.π_desc _ _ _

/-- The image-quotient and kernel-quotient comparison is natural. -/
@[reassoc]
theorem Hom.stableIntervalImageKernelGradedIso_naturality (φ : Y ⟶ Z)
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    φ.stableIntervalGradedMap n h ≫ (Z.stableIntervalImageKernelGradedIso n h).hom =
      (Y.stableIntervalImageKernelGradedIso n h).hom ≫
        φ.stableIntervalKernelGradedMap n h := by
  apply (cancel_epi (cokernel.π (Y.stableIntervalImageMap n h))).1
  rw [← Category.assoc, φ.stableIntervalGradedMap_π, Category.assoc,
    Z.stableIntervalImageKernelGradedIso_π, ← Category.assoc,
    φ.stableIntervalImageKernelIso_naturality, Category.assoc,
    ← φ.stableIntervalKernelGradedMap_π,
    Y.stableIntervalImageKernelGradedIso_π_assoc]

/-- The stable interval/actual kernel graded comparison is natural for the
original spectral-object map. -/
@[reassoc]
theorem Hom.stableIntervalKernelGradedIso_naturality (φ : Y ⟶ Z)
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    φ.stableIntervalMap n h ≫ (Z.stableIntervalKernelGradedIso n h).hom =
      (Y.stableIntervalKernelGradedIso n h).hom ≫ φ.stableIntervalKernelGradedMap n h := by
  dsimp only [stableIntervalKernelGradedIso, Iso.trans_hom]
  rw [← Category.assoc, φ.stableIntervalImageCokernelIso_naturality,
    Category.assoc, φ.stableIntervalImageKernelGradedIso_naturality, ← Category.assoc]

/-- The finite-window comparison with the actual kernel-filtration graded
object is natural, including the native map on its finite `E` window. -/
@[reassoc]
theorem Hom.finiteIntervalKernelGradedIso_naturality
    (φ : Y ⟶ Z) (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleftY : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hrightY : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι))))))
    (hleftZ : IsZero ((Z.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hrightZ : IsZero ((Z.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        (n - 1) n (n + 1) (by omega) (by omega) ≫
        (Z.finiteIntervalKernelGradedIso n h₀₁ h₁₂ h₂₃ hleftZ hrightZ).hom =
      (Y.finiteIntervalKernelGradedIso n h₀₁ h₁₂ h₂₃ hleftY hrightY).hom ≫
        φ.stableIntervalKernelGradedMap n h₁₂ := by
  dsimp only [finiteIntervalKernelGradedIso, Iso.trans_hom]
  rw [← Category.assoc, φ.finiteIntervalImageCokernelIso_naturality,
    Category.assoc, φ.stableIntervalImageKernelGradedIso_naturality, ← Category.assoc]

end CategoryTheory.Abelian.SpectralObject

end
