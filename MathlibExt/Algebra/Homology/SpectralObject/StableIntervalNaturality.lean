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

public import MathlibExt.Algebra.Homology.SpectralObject.StableIntervalGraded
public import MathlibExt.Algebra.Homology.SpectralObjectCokernelENaturality

/-!
# Naturality of endpoint images and their stable interval quotient

Let φ:Y → Z be a morphism of spectral objects in an abelian category,
indexed by a preorder with endpoints. In degree n, the maps on
Hⁿ(⊥,i) and Hⁿ(⊥,⊤) induce maps between the endpoint images
I_i=Im(Hⁿ(⊥,i) → Hⁿ(⊥,⊤)).
These maps commute with the ordered image inclusions and therefore
induce maps on their quotients.

For i₁≤i₂, the stable interval Eⁿ(⊥,i₁,i₂,⊤) is canonically
I_{i₂}/I_{i₁}. This comparison is natural in φ, preserving both the
E-window map and the image-quotient map. The category and preorder
universes are independent.
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
variable {Y Z : SpectralObject D ι}

namespace Hom

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

The degree-n maps of φ on Hⁿ(⊥,i) and A form the commuting square between the two endpoint step maps Hⁿ(⊥,i) → A. -/
def stableIntervalImageArrow (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    Arrow.mk (Y.stableIntervalStepToAbutment n i) ⟶
      Arrow.mk (Z.stableIntervalStepToAbutment n i) :=
  Arrow.homMk'
    ((φ.hom n).app (mk₁ (stableIntervalLeftMiddle i)))
    ((φ.hom n).app (mk₁ (stableIntervalFull (ι := ι))))
    ((φ.hom n).naturality
      (homMk₁ (𝟙 _) (stableIntervalRight i) (by subsingleton) :
        mk₁ (stableIntervalLeftMiddle i) ⟶ mk₁ (stableIntervalFull (ι := ι)))).symm

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

The induced map I_i(Y) → I_i(Z) between selected endpoint images. -/
def stableIntervalImageMap (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    Y.stableIntervalStepImage n i ⟶ Z.stableIntervalStepImage n i :=
  Limits.image.map (φ.stableIntervalImageArrow n i)

@[reassoc]
theorem stableIntervalImageMap_ι (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    φ.stableIntervalImageMap n i ≫
        Limits.image.ι (Z.stableIntervalStepToAbutment n i) =
      Limits.image.ι (Y.stableIntervalStepToAbutment n i) ≫
        (φ.hom n).app (mk₁ (stableIntervalFull (ι := ι))) :=
  Limits.image.map_ι (φ.stableIntervalImageArrow n i)

@[reassoc]
theorem stableIntervalStepToImage_comp_map (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    Y.stableIntervalStepToImage n i ≫ φ.stableIntervalImageMap n i =
      (φ.hom n).app (mk₁ (stableIntervalLeftMiddle i)) ≫
        Z.stableIntervalStepToImage n i :=
  Limits.image.factor_map (φ.stableIntervalImageArrow n i)

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the maps I_i(Y) → I_i(Z) commute with the ordered inclusions I_{i₁}(W) → I_{i₂}(W). -/
@[reassoc]
theorem stableIntervalImageMap_ordered (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫ φ.stableIntervalImageMap n i₂ =
      φ.stableIntervalImageMap n i₁ ≫ Z.stableIntervalImageMap n h := by
  apply (cancel_mono (Limits.image.ι (Z.stableIntervalStepToAbutment n i₂))).1
  simp only [Category.assoc, stableIntervalImageMap_ι,
    Y.stableIntervalImageMap_comp_ι_assoc, Z.stableIntervalImageMap_comp_ι,
    stableIntervalImageMap_ι]

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the map I_{i₂}(Y)/I_{i₁}(Y) → I_{i₂}(Z)/I_{i₁}(Z) induced by the ordered image square. -/
def stableIntervalGradedMap (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel (Y.stableIntervalImageMap n h) ⟶
      cokernel (Z.stableIntervalImageMap n h) :=
  cokernel.desc (Y.stableIntervalImageMap n h)
    (φ.stableIntervalImageMap n i₂ ≫ cokernel.π (Z.stableIntervalImageMap n h)) (by
      rw [← Category.assoc, φ.stableIntervalImageMap_ordered n h,
        Category.assoc, cokernel.condition, comp_zero])

@[reassoc]
theorem stableIntervalGradedMap_π (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel.π (Y.stableIntervalImageMap n h) ≫ φ.stableIntervalGradedMap n h =
      φ.stableIntervalImageMap n i₂ ≫ cokernel.π (Z.stableIntervalImageMap n h) :=
  cokernel.π_desc _ _ _

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the stable interval map E_Yⁿ(⊥,i₁,i₂,⊤) → E_Zⁿ(⊥,i₁,i₂,⊤) induced by φ on the E-objects. -/
def stableIntervalMap (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ⟶ Z.stableIntervalObj n h :=
  φ.EMap (stableIntervalLeft i₁) (stableIntervalMiddle h) (stableIntervalRight i₂)
    (n - 1) n (n + 1) (by omega) (by omega)

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the quotient maps I_{i₂}(W) → E_Wⁿ(⊥,i₁,i₂,⊤) commute with the endpoint image map and the stable interval map induced by φ. -/
@[reassoc]
theorem stableIntervalImageToStable_naturality (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageToStable n h ≫ φ.stableIntervalMap n h =
      φ.stableIntervalImageMap n i₂ ≫ Z.stableIntervalImageToStable n h := by
  apply (cancel_epi (Y.stableIntervalStepToImage n i₂)).1
  calc
    Y.stableIntervalStepToImage n i₂ ≫
        (Y.stableIntervalImageToStable n h ≫ φ.stableIntervalMap n h) =
      Y.stableIntervalStepToStable n h ≫ φ.stableIntervalMap n h := by
        rw [← Category.assoc, Y.stableIntervalStepToImage_comp_imageToStable]
    _ = (φ.hom n).app (mk₁ (stableIntervalLeftMiddle i₂)) ≫
        Z.stableIntervalStepToStable n h :=
      φ.cokernelSequenceE_g_EMap
        (stableIntervalLeft i₁) (stableIntervalMiddle h) (stableIntervalRight i₂)
        (stableIntervalLeftMiddle i₂) (stableIntervalLeft_comp_middle h)
        (n - 1) n (n + 1) (by omega) (by omega)
    _ = (φ.hom n).app (mk₁ (stableIntervalLeftMiddle i₂)) ≫
        (Z.stableIntervalStepToImage n i₂ ≫ Z.stableIntervalImageToStable n h) := by
      rw [Z.stableIntervalStepToImage_comp_imageToStable]
    _ = (Y.stableIntervalStepToImage n i₂ ≫ φ.stableIntervalImageMap n i₂) ≫
        Z.stableIntervalImageToStable n h := by
      rw [φ.stableIntervalStepToImage_comp_map, Category.assoc]
    _ = Y.stableIntervalStepToImage n i₂ ≫
        (φ.stableIntervalImageMap n i₂ ≫ Z.stableIntervalImageToStable n h) :=
      Category.assoc _ _ _

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object morphism. For W=Y,Z in degree n define
A_W=H_Wⁿ(⊥,⊤) and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the isomorphisms E_Wⁿ(⊥,i₁,i₂,⊤) ≅ I_{i₂}(W)/I_{i₁}(W) commute with the E-window map and the induced image-quotient map of φ. -/
@[reassoc]
theorem stableIntervalImageCokernelIso_naturality (φ : Y ⟶ Z) (n : ℤ)
    {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    φ.stableIntervalMap n h ≫ (Z.stableIntervalImageCokernelIso n h).hom =
      (Y.stableIntervalImageCokernelIso n h).hom ≫ φ.stableIntervalGradedMap n h := by
  apply (cancel_epi (Y.stableIntervalImageToStable n h)).1
  calc
    Y.stableIntervalImageToStable n h ≫
        (φ.stableIntervalMap n h ≫ (Z.stableIntervalImageCokernelIso n h).hom) =
      (φ.stableIntervalImageMap n i₂ ≫ Z.stableIntervalImageToStable n h) ≫
        (Z.stableIntervalImageCokernelIso n h).hom := by
      rw [← Category.assoc, φ.stableIntervalImageToStable_naturality]
    _ = φ.stableIntervalImageMap n i₂ ≫ cokernel.π (Z.stableIntervalImageMap n h) := by
      rw [Category.assoc, Z.stableIntervalImageToStable_comp_iso_hom]
    _ = cokernel.π (Y.stableIntervalImageMap n h) ≫ φ.stableIntervalGradedMap n h :=
      (φ.stableIntervalGradedMap_π n h).symm
    _ = (Y.stableIntervalImageToStable n h ≫
        (Y.stableIntervalImageCokernelIso n h).hom) ≫ φ.stableIntervalGradedMap n h := by
      rw [Y.stableIntervalImageToStable_comp_iso_hom]
    _ = Y.stableIntervalImageToStable n h ≫
        ((Y.stableIntervalImageCokernelIso n h).hom ≫ φ.stableIntervalGradedMap n h) :=
      Category.assoc _ _ _

end Hom

end CategoryTheory.Abelian.SpectralObject

end
