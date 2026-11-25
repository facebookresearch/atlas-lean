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

import MathlibExt.Algebra.Homology.SpectralObject.StableIntervalGraded

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type u} [Category.{v} D] [Abelian D]
variable {ι : Type w} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (Y : SpectralObject D ι)

example (n : ℤ) (i : ι) : D := Y.stableIntervalStep n i

example (n : ℤ) : D := Y.stableIntervalAbutment n

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStep n i₁ ⟶ Y.stableIntervalStep n i₂ :=
  Y.stableIntervalStepMap n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToAbutment n i₂ =
      Y.stableIntervalStepToAbutment n i₁ :=
  Y.stableIntervalStepMap_comp_toAbutment n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Limits.image (Y.stableIntervalStepToAbutment n i₁) ⟶
      Limits.image (Y.stableIntervalStepToAbutment n i₂) :=
  Y.stableIntervalImageMap n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫
        Limits.image.ι (Y.stableIntervalStepToAbutment n i₂) =
      Limits.image.ι (Y.stableIntervalStepToAbutment n i₁) :=
  Y.stableIntervalImageMap_comp_ι n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToImage n i₂ =
      Y.stableIntervalStepToImage n i₁ ≫
        Y.stableIntervalImageMap n h :=
  Y.stableIntervalStepToImage_naturality n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) : D :=
  Y.stableIntervalObj n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStep n i₂ ⟶ Y.stableIntervalObj n h :=
  Y.stableIntervalStepToStable n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Limits.image (Y.stableIntervalStepToAbutment n i₂) ⟶
      Y.stableIntervalObj n h :=
  Y.stableIntervalImageToStable n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepMap n h ≫
        Y.stableIntervalStepToStable n h = 0 :=
  Y.stableIntervalStepMap_comp_toStable_zero n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalStepToImage n i₂ ≫
        Y.stableIntervalImageToStable n h =
      Y.stableIntervalStepToStable n h :=
  Y.stableIntervalStepToImage_comp_imageToStable n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageMap n h ≫
        Y.stableIntervalImageToStable n h = 0 :=
  Y.stableIntervalImageMap_comp_imageToStable_zero n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    IsColimit (CokernelCofork.ofπ
      (Y.stableIntervalImageToStable n h)
      (Y.stableIntervalImageMap_comp_imageToStable_zero n h)) :=
  Y.stableIntervalImageToStableIsCokernel n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalObj n h ≅
      cokernel (Y.stableIntervalImageMap n h) :=
  Y.stableIntervalImageCokernelIso n h

example (n : ℤ) {i₁ i₂ : ι} (h : i₁ ≤ i₂) :
    Y.stableIntervalImageToStable n h ≫
        (Y.stableIntervalImageCokernelIso n h).hom =
      cokernel.π (Y.stableIntervalImageMap n h) :=
  Y.stableIntervalImageToStable_comp_iso_hom n h

example (i : ι) : D :=
  Y.stableIntervalObj 0 (show i ≤ i from le_rfl)

example : D :=
  Y.stableIntervalObj (-1) (show (⊥ : ι) ≤ ⊤ from bot_le)

example (i : ι) :
    IsColimit (CokernelCofork.ofπ
      (Y.stableIntervalImageToStable 0 (show i ≤ i from le_rfl))
      (Y.stableIntervalImageMap_comp_imageToStable_zero
        0 (show i ≤ i from le_rfl))) :=
  Y.stableIntervalImageToStableIsCokernel 0 (show i ≤ i from le_rfl)

example :
    Y.stableIntervalObj (-1) (show (⊥ : ι) ≤ ⊤ from bot_le) ≅
      cokernel (Y.stableIntervalImageMap (-1)
        (show (⊥ : ι) ≤ ⊤ from bot_le)) :=
  Y.stableIntervalImageCokernelIso (-1)
    (show (⊥ : ι) ≤ ⊤ from bot_le)

end CategoryTheory.Abelian.SpectralObject

end
