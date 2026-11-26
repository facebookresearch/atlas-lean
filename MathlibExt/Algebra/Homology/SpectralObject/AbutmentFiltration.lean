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
# Restriction-kernel filtration of the endpoint abutment

Let Y be a spectral object in an abelian category D, indexed by a preorder
ι with least and greatest elements. Its degree-n abutment is
A=H_Yⁿ(⊥,⊤). Restriction to the upper interval gives maps
r_i:A → H_Yⁿ(i,⊤), and the kernels F_i form an increasing filtration.

Spectral-object exactness identifies F_i with the image I_i of
H_Yⁿ(⊥,i) → A. For i₁≤i₂ the stable endpoint E-window
E_Yⁿ(⊥≤i₁≤i₂≤⊤) is canonically the associated graded F_{i₂}/F_{i₁}.
An arbitrary four-cut window has the same comparison when its omitted
left interval vanishes in degree n+1 and its omitted right interval
vanishes in degree n−1.

All restriction, image, kernel and quotient comparisons are natural in
spectral-object maps. The coefficient-category object and morphism
universes and the preorder universe are independent.
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

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

The restriction r_i:A → H_Yⁿ(i,⊤) induced by the inclusion of the upper interval into the full endpoint interval. -/
def stableIntervalAbutmentRestriction (n : ℤ) (i : ι) :
    Y.stableIntervalAbutment n ⟶ (Y.H n).obj (mk₁ (stableIntervalRight i)) :=
  (Y.H n).map
    (twoδ₁Toδ₀ (stableIntervalLeftMiddle i) (stableIntervalRight i)
      (stableIntervalFull (ι := ι)) (by subsingleton))

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

The subobject F_i of the abutment A defined as the kernel of restriction r_i. -/
def stableIntervalKernelFiltration (n : ℤ) (i : ι) :
    Subobject (Y.stableIntervalAbutment n) :=
  kernelSubobject (Y.stableIntervalAbutmentRestriction n i)

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

The image subobject I_i equals the restriction kernel F_i by spectral-object exactness. -/
theorem stableIntervalImage_eq_kernel (n : ℤ) (i : ι) :
    imageSubobject (Y.stableIntervalStepToAbutment n i) =
      Y.stableIntervalKernelFiltration n i :=
  (ShortComplex.exact_iff_image_eq_kernel _).mp
    (Y.exact₂ (stableIntervalLeftMiddle i) (stableIntervalRight i)
      (stableIntervalFull (ι := ι)) (by subsingleton) n)

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

The filtration is increasing: i₁≤i₂ implies F_{i₁}≤F_{i₂} as subobjects of A. -/
theorem stableIntervalKernelFiltration_monotone (n : ℤ) :
    Monotone (Y.stableIntervalKernelFiltration n) := by
  intro i₁ i₂ h
  rw [← Y.stableIntervalImage_eq_kernel n i₁, ← Y.stableIntervalImage_eq_kernel n i₂,
    ← Y.stableIntervalStepMap_comp_toAbutment n h]
  exact imageSubobject_comp_le _ _

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

The canonical isomorphism from the selected image object of H_Yⁿ(⊥,i) → A to the object representing the kernel subobject F_i. -/
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

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

For i₁≤i₂, the image-to-kernel isomorphisms identify the ordered map I_{i₁} → I_{i₂} with the filtration inclusion F_{i₁}↪F_{i₂}. -/
@[reassoc]
theorem stableIntervalImageKernelIso_ordered
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫ (Y.stableIntervalImageKernelIso n i₂).hom =
      (Y.stableIntervalImageKernelIso n i₁).hom ≫
        Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h) := by
  apply (cancel_mono (Y.stableIntervalKernelFiltration n i₂).arrow).1
  simp only [Category.assoc, Y.stableIntervalImageKernelIso_hom_arrow,
    Y.stableIntervalImageMap_comp_ι, Subobject.ofLE_arrow]

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

For i₁≤i₂, the associated-graded object F_{i₂}/F_{i₁}, defined as the cokernel of the ordered filtration inclusion. -/
abbrev stableIntervalKernelGraded (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : D :=
  cokernel (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h))

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

For i₁≤i₂, the canonical isomorphism Coker(I_{i₁} → I_{i₂}) ≅ F_{i₂}/F_{i₁} induced by the two image-to-kernel comparisons. -/
def stableIntervalImageKernelGradedIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel (Y.stableIntervalImageMap n h) ≅ Y.stableIntervalKernelGraded n h :=
  cokernel.mapIso (Y.stableIntervalImageMap n h)
    (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h))
    (Y.stableIntervalImageKernelIso n i₁) (Y.stableIntervalImageKernelIso n i₂)
    (Y.stableIntervalImageKernelIso_ordered n h)

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

For i₁≤i₂, the stable endpoint window E_Yⁿ(⊥≤i₁≤i₂≤⊤) is canonically isomorphic to F_{i₂}/F_{i₁}. -/
def stableIntervalKernelGradedIso
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ≅ Y.stableIntervalKernelGraded n h :=
  Y.stableIntervalImageCokernelIso n h ≪≫ Y.stableIntervalImageKernelGradedIso n h

/-- Let D be abelian, ι a preorder with least and greatest elements,
Y a spectral object, and i₀≤i₁≤i₂≤i₃ cuts.
Assume H_Y^{n+1}(⊥,i₀)=0 and H_Y^{n−1}(i₃,⊤)=0.

The window E_Yⁿ(i₀≤i₁≤i₂≤i₃) is canonically isomorphic to F_{i₂}/F_{i₁}, where F_i=Ker(H_Yⁿ(⊥,⊤) → H_Yⁿ(i,⊤)). -/
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

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

If the upper-interval object H_Yⁿ(i,⊤) is zero, then F_i is the full abutment subobject. -/
theorem stableIntervalKernelFiltration_eq_top (n : ℤ) (i : ι)
    (h : IsZero ((Y.H n).obj (mk₁ (stableIntervalRight i)))) :
    Y.stableIntervalKernelFiltration n i = ⊤ := by
  have hzero : Y.stableIntervalAbutmentRestriction n i = 0 := h.eq_of_tgt _ _
  simp only [stableIntervalKernelFiltration, hzero, kernelSubobject_zero]

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

If the lower-interval object H_Yⁿ(⊥,i) is zero, then F_i is the zero subobject of A. -/
theorem stableIntervalKernelFiltration_eq_bot (n : ℤ) (i : ι)
    (h : IsZero (Y.stableIntervalStep n i)) :
    Y.stableIntervalKernelFiltration n i = ⊥ := by
  rw [← Y.stableIntervalImage_eq_kernel]
  have hzero : Y.stableIntervalStepToAbutment n i = 0 := h.eq_of_src _ _
  rw [hzero, imageSubobject_zero]

variable {Y Z : SpectralObject D ι}

namespace Hom

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

The induced maps A_Y → A_Z and H_Yⁿ(i,⊤) → H_Zⁿ(i,⊤) form the commuting square between the two restriction maps at i. -/
def stableIntervalRestrictionArrow (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    Arrow.mk (Y.stableIntervalAbutmentRestriction n i) ⟶
      Arrow.mk (Z.stableIntervalAbutmentRestriction n i) :=
  Arrow.homMk'
    ((φ.hom n).app (mk₁ (stableIntervalFull (ι := ι))))
    ((φ.hom n).app (mk₁ (stableIntervalRight i)))
    ((φ.hom n).naturality
      (twoδ₁Toδ₀ (stableIntervalLeftMiddle i) (stableIntervalRight i)
        (stableIntervalFull (ι := ι)) (by subsingleton))).symm

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

The induced map F_i(Y) → F_i(Z) between restriction kernels, determined by the degree-n map on the full endpoint interval. -/
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

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the maps F_i(Y) → F_i(Z) commute with the ordered filtration inclusions F_{i₁}↪F_{i₂}. -/
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

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

The image-to-kernel isomorphisms commute with the image maps I_i(Y) → I_i(Z) and the induced restriction-kernel maps F_i(Y) → F_i(Z). -/
@[reassoc]
theorem stableIntervalImageKernelIso_naturality (φ : Y ⟶ Z) (n : ℤ) (i : ι) :
    φ.stableIntervalImageMap n i ≫ (Z.stableIntervalImageKernelIso n i).hom =
      (Y.stableIntervalImageKernelIso n i).hom ≫ φ.stableIntervalKernelMap n i := by
  apply (cancel_mono (Z.stableIntervalKernelFiltration n i).arrow).1
  simp only [Category.assoc, Z.stableIntervalImageKernelIso_hom_arrow,
    stableIntervalImageMap_ι, stableIntervalKernelMap_arrow,
    Y.stableIntervalImageKernelIso_hom_arrow_assoc]

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the induced associated-graded map F_{i₂}(Y)/F_{i₁}(Y) → F_{i₂}(Z)/F_{i₁}(Z). -/
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

/-- Let D be abelian, ι a preorder with least and greatest elements, and
Y a spectral object indexed by ι. In degree n put A=H_Yⁿ(⊥,⊤),
F_i=Ker(A → H_Yⁿ(i,⊤)), and I_i=Im(H_Yⁿ(⊥,i) → A).

For i₁≤i₂, let α_i:I_i ≅ F_i and γ:Coker(I_{i₁} → I_{i₂}) ≅ F_{i₂}/F_{i₁}. With quotient maps π_I from I_{i₂} and π_F from F_{i₂}, their projection equation is γ∘π_I=π_F∘α_{i₂}. -/
@[reassoc]
theorem stableIntervalImageKernelGradedIso_π (Y : SpectralObject D ι)
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    cokernel.π (Y.stableIntervalImageMap n h) ≫
        (Y.stableIntervalImageKernelGradedIso n h).hom =
      (Y.stableIntervalImageKernelIso n i₂).hom ≫
        cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n h)) :=
  cokernel.π_desc _ _ _

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the comparisons Coker(I_{i₁}(W) → I_{i₂}(W)) ≅ F_{i₂}(W)/F_{i₁}(W) commute with the induced maps of the image and kernel quotients. -/
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

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₁≤i₂, the comparisons E_Wⁿ(⊥≤i₁≤i₂≤⊤) ≅ F_{i₂}(W)/F_{i₁}(W) commute with the stable-interval and associated-graded maps induced by φ. -/
@[reassoc]
theorem Hom.stableIntervalKernelGradedIso_naturality (φ : Y ⟶ Z)
    (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    φ.stableIntervalMap n h ≫ (Z.stableIntervalKernelGradedIso n h).hom =
      (Y.stableIntervalKernelGradedIso n h).hom ≫ φ.stableIntervalKernelGradedMap n h := by
  dsimp only [stableIntervalKernelGradedIso, Iso.trans_hom]
  rw [← Category.assoc, φ.stableIntervalImageCokernelIso_naturality,
    Category.assoc, φ.stableIntervalImageKernelGradedIso_naturality, ← Category.assoc]

/-- Let D be abelian, ι a preorder with least and greatest elements,
and φ:Y → Z a spectral-object morphism. In degree n, for W=Y,Z put
A_W=H_Wⁿ(⊥,⊤), F_i(W)=Ker(A_W → H_Wⁿ(i,⊤)),
and I_i(W)=Im(H_Wⁿ(⊥,i) → A_W).

For i₀≤i₁≤i₂≤i₃, assume H_W^{n+1}(⊥,i₀)=0 and H_W^{n−1}(i₃,⊤)=0 for both W=Y,Z. Their comparisons E_Wⁿ(i₀≤i₁≤i₂≤i₃) ≅ F_{i₂}(W)/F_{i₁}(W) commute with the E-window map and kernel-graded map induced by φ. -/
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
