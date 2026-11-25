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
# Endpoint stabilization for the skeletal spectral object

An actual spectral-object window identifies with its endpoint interval when
the two omitted outer intervals vanish. The comparison uses the canonical
indexing maps on `E`, followed by the existing image-cokernel comparison.
There is no bound on the cohomological degree and no convergence datum is
supplied.

The intended skeletal application has extended integer indices: the bottom
space is the full CW complex and the top space is empty. Its filtration
levels are indexed by all integers.
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

/-- Padding an actual window to the endpoints is an isomorphism when the
omitted left interval in degree `n + 1` and right interval in degree `n - 1`
are zero. Both comparisons are the native spectral-object indexing maps. -/
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

/-- An endpoint-stable actual window is the quotient of its two actual
images in the full endpoint object. -/
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

/-- Endpoint padding is natural for the native maps on actual `E` windows. -/
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

/-- The finite-window comparison is natural on the actual associated image
quotients, with no quotient map supplied as an input. -/
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
