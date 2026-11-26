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
public import MathlibExt.Algebra.Homology.SpectralObjectMapNaturality
public import MathlibExt.Algebra.Homology.SpectralObject.StableIntervalNaturality
public import Mathlib.Algebra.Homology.SpectralObject.EpiMono

/-!
# Endpoint stabilization of spectral-object windows

Let Y be a spectral object in an abelian category, indexed by a preorder
with least and greatest elements. For a window i₀≤i₁≤i₂≤i₃, vanishing
H_Y^{n+1}(⊥,i₀)=0 and H_Y^{n−1}(i₃,⊤)=0 makes extension of the
outer cuts a canonical isomorphism
E_Yⁿ(i₀≤i₁≤i₂≤i₃) ≅ E_Yⁿ(⊥≤i₁≤i₂≤⊤).

The endpoint window is the quotient of the images of
H_Yⁿ(⊥,i₁) and H_Yⁿ(⊥,i₂) in H_Yⁿ(⊥,⊤).
Both comparisons are natural in spectral-object morphisms satisfying the
same interval vanishings. The integer n is arbitrary.
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

/-- Let D be abelian, ι a preorder with least and greatest elements,
Y a spectral object, and i₀≤i₁≤i₂≤i₃ cuts.
Assume H_Y^{n+1}(⊥,i₀)=0 and H_Y^{n−1}(i₃,⊤)=0.

The canonical endpoint-padding isomorphism E_Yⁿ(i₀≤i₁≤i₂≤i₃) ≅ E_Yⁿ(⊥≤i₁≤i₂≤⊤), induced by extending the outer cuts to the endpoints. -/
def finiteIntervalPaddingIso
    (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    Y.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        (n - 1) n (n + 1) (by omega) (by omega) ≅
      Y.stableIntervalObj n h₁₂ :=
  (Y.isoMapFourδ₁Toδ₀' (⊥ : ι) i₀ i₁ i₂ i₃
    bot_le h₀₁ h₁₂ h₂₃ (n - 1) n (n + 1) hleft (by omega) (by omega)).symm ≪≫
  Y.isoMapFourδ₄Toδ₃' (⊥ : ι) i₁ i₂ i₃ (⊤ : ι)
    bot_le h₁₂ h₂₃ le_top (n - 1) n (n + 1) hright (by omega) (by omega)

/-- Let D be abelian, ι a preorder with least and greatest elements,
Y a spectral object, and i₀≤i₁≤i₂≤i₃ cuts.
Assume H_Y^{n+1}(⊥,i₀)=0 and H_Y^{n−1}(i₃,⊤)=0.

For I_i=Im(H_Yⁿ(⊥,i) → H_Yⁿ(⊥,⊤)), the canonical comparison E_Yⁿ(i₀≤i₁≤i₂≤i₃) ≅ Coker(I_{i₁} → I_{i₂}). -/
def finiteIntervalImageCokernelIso
    (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    Y.E (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        (n - 1) n (n + 1) (by omega) (by omega) ≅
      cokernel (Y.stableIntervalImageMap n h₁₂) :=
  Y.finiteIntervalPaddingIso n h₀₁ h₁₂ h₂₃ hleft hright ≪≫
    Y.stableIntervalImageCokernelIso n h₁₂

variable {Y Z : SpectralObject D ι}

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object map. For i₀≤i₁≤i₂≤i₃, suppose
H_W^{n+1}(⊥,i₀)=0 and H_W^{n−1}(i₃,⊤)=0 for W=Y,Z.
The endpoint-padding isomorphisms commute with φ on the four-cut
windows and on the full endpoint windows. -/
@[reassoc]
theorem Hom.finiteIntervalPaddingIso_naturality
    (φ : Y ⟶ Z) (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleftY : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hrightY : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι))))))
    (hleftZ : IsZero ((Z.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hrightZ : IsZero ((Z.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        (n - 1) n (n + 1) (by omega) (by omega) ≫
        (Z.finiteIntervalPaddingIso n h₀₁ h₁₂ h₂₃ hleftZ hrightZ).hom =
      (Y.finiteIntervalPaddingIso n h₀₁ h₁₂ h₂₃ hleftY hrightY).hom ≫
        φ.stableIntervalMap n h₁₂ := by
  let LY := Y.isoMapFourδ₁Toδ₀' (⊥ : ι) i₀ i₁ i₂ i₃
    bot_le h₀₁ h₁₂ h₂₃ (n - 1) n (n + 1) hleftY (by omega) (by omega)
  let LZ := Z.isoMapFourδ₁Toδ₀' (⊥ : ι) i₀ i₁ i₂ i₃
    bot_le h₀₁ h₁₂ h₂₃ (n - 1) n (n + 1) hleftZ (by omega) (by omega)
  let RY := Y.isoMapFourδ₄Toδ₃' (⊥ : ι) i₁ i₂ i₃ (⊤ : ι)
    bot_le h₁₂ h₂₃ le_top (n - 1) n (n + 1) hrightY (by omega) (by omega)
  let RZ := Z.isoMapFourδ₄Toδ₃' (⊥ : ι) i₁ i₂ i₃ (⊤ : ι)
    bot_le h₁₂ h₂₃ le_top (n - 1) n (n + 1) hrightZ (by omega) (by omega)
  let middle := φ.EMap
    (homOfLE (bot_le : (⊥ : ι) ≤ i₁)) (homOfLE h₁₂) (homOfLE h₂₃)
    (n - 1) n (n + 1) (by omega) (by omega)
  have hL : LY.hom ≫ φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
      (n - 1) n (n + 1) (by omega) (by omega) = middle ≫ LZ.hom :=
    φ.map_EMap
      (homOfLE (bot_le : (⊥ : ι) ≤ i₁)) (homOfLE h₁₂) (homOfLE h₂₃)
      (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
      (fourδ₁Toδ₀' (⊥ : ι) i₀ i₁ i₂ i₃ bot_le h₀₁ h₁₂ h₂₃)
      (n - 1) n (n + 1) (by omega) (by omega)
  have hR : RY.hom ≫ φ.stableIntervalMap n h₁₂ = middle ≫ RZ.hom :=
    φ.map_EMap
      (homOfLE (bot_le : (⊥ : ι) ≤ i₁)) (homOfLE h₁₂) (homOfLE h₂₃)
      (stableIntervalLeft i₁) (stableIntervalMiddle h₁₂) (stableIntervalRight i₂)
      (fourδ₄Toδ₃' (⊥ : ι) i₁ i₂ i₃ (⊤ : ι) bot_le h₁₂ h₂₃ le_top)
      (n - 1) n (n + 1) (by omega) (by omega)
  have hLinv : φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
      (n - 1) n (n + 1) (by omega) (by omega) ≫ LZ.inv = LY.inv ≫ middle := by
    apply (cancel_epi LY.hom).1
    rw [← Category.assoc, hL, Category.assoc, LZ.hom_inv_id, Category.comp_id,
      ← Category.assoc, LY.hom_inv_id, Category.id_comp]
  change φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
      (n - 1) n (n + 1) (by omega) (by omega) ≫ (LZ.inv ≫ RZ.hom) =
    (LY.inv ≫ RY.hom) ≫ φ.stableIntervalMap n h₁₂
  rw [← Category.assoc, hLinv, Category.assoc, ← hR, ← Category.assoc]

/-- Let D be abelian, ι a preorder with endpoints, and φ:Y → Z a
spectral-object map. For i₀≤i₁≤i₂≤i₃, suppose
H_W^{n+1}(⊥,i₀)=0 and H_W^{n−1}(i₃,⊤)=0 for W=Y,Z.
The four-cut comparisons with Coker(I_{i₁}(W) → I_{i₂}(W)) commute
with φ on E-windows and on the image quotients, where
I_i(W)=Im(H_Wⁿ(⊥,i) → H_Wⁿ(⊥,⊤)). -/
@[reassoc]
theorem Hom.finiteIntervalImageCokernelIso_naturality
    (φ : Y ⟶ Z) (n : ℤ) {i₀ i₁ i₂ i₃ : ι}
    (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃)
    (hleftY : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hrightY : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι))))))
    (hleftZ : IsZero ((Z.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ i₀)))))
    (hrightZ : IsZero ((Z.H (n - 1)).obj (mk₁ (homOfLE (le_top : i₃ ≤ (⊤ : ι)))))) :
    φ.EMap (homOfLE h₀₁) (homOfLE h₁₂) (homOfLE h₂₃)
        (n - 1) n (n + 1) (by omega) (by omega) ≫
        (Z.finiteIntervalImageCokernelIso n h₀₁ h₁₂ h₂₃ hleftZ hrightZ).hom =
      (Y.finiteIntervalImageCokernelIso n h₀₁ h₁₂ h₂₃ hleftY hrightY).hom ≫
        φ.stableIntervalGradedMap n h₁₂ := by
  dsimp only [finiteIntervalImageCokernelIso, Iso.trans_hom]
  rw [← Category.assoc, φ.finiteIntervalPaddingIso_naturality,
    Category.assoc, φ.stableIntervalImageCokernelIso_naturality, ← Category.assoc]

end CategoryTheory.Abelian.SpectralObject

end
