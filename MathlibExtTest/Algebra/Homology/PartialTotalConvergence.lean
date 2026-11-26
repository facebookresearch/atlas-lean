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

import MathlibExt.Algebra.Homology.PartialTotalConvergence

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (n : ℕ) :
    B.partialTotalSpectralObject.stableIntervalAbutment (-(n : ℤ)) ≅
      (B.total (ComplexShape.down ℕ)).homology n :=
  B.partialTotalStableAbutmentHomologyIso n

example (n s : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStep
        (-(n : ℤ)) ((s : ℤ) : EInt) ⟶
      (B.total (ComplexShape.down ℕ)).homology n :=
  B.partialTotalSpectralObject.stableIntervalStepToAbutment
      (-(n : ℤ)) ((s : ℤ) : EInt) ≫
    (B.partialTotalStableAbutmentHomologyIso n).hom

example (n s : ℕ) :
    B.partialTotalSpectralStepToFiltration n s ≫
        (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
      (B.partialTotalSpectralStepHomologyIso n s).hom ≫
        HomologicalComplex.homologyMap (B.partialTotalι s) n :=
  B.partialTotalSpectralStepToFiltration_comp_ι n s

example :
    B.partialTotalSpectralStepToFiltration 0 0 ≫
        (B.partialTotalHomologyFiltration 0).ι.app ((0 : ℤ) : EInt) =
      (B.partialTotalSpectralStepHomologyIso 0 0).hom ≫
        HomologicalComplex.homologyMap (B.partialTotalι 0) 0 :=
  B.partialTotalSpectralStepToFiltration_comp_ι 0 0

example :
    B.partialTotalSpectralStepToFiltration 1 0 ≫
        (B.partialTotalHomologyFiltration 1).ι.app ((0 : ℤ) : EInt) =
      (B.partialTotalSpectralStepHomologyIso 1 0).hom ≫
        HomologicalComplex.homologyMap (B.partialTotalι 0) 1 :=
  B.partialTotalSpectralStepToFiltration_comp_ι 1 0

example :
    B.partialTotalSpectralStepToFiltration 1 1 ≫
        (B.partialTotalHomologyFiltration 1).ι.app ((1 : ℤ) : EInt) =
      (B.partialTotalSpectralStepHomologyIso 1 1).hom ≫
        HomologicalComplex.homologyMap (B.partialTotalι 1) 1 :=
  B.partialTotalSpectralStepToFiltration_comp_ι 1 1

example (n : ℕ) :=
  HomologicalComplex₂.partialTotalStableAbutmentHomologyIso
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n

example (n s : ℕ) :=
  HomologicalComplex₂.partialTotalSpectralStepToFiltration_comp_ι
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) n s

example (n s : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStepImage
        (-(n : ℤ)) ((s : ℤ) : EInt) ≅
      (B.partialTotalHomologyFiltration n).obj ((s : ℤ) : EInt) :=
  B.partialTotalStableStepImageFiltrationIso n s

example (n s : ℕ) :
    (B.partialTotalStableStepImageFiltrationIso n s).hom ≫
        (B.partialTotalHomologyFiltration n).ι.app ((s : ℤ) : EInt) =
      Limits.image.ι
          (B.partialTotalSpectralObject.stableIntervalStepToAbutment
            (-(n : ℤ)) ((s : ℤ) : EInt)) ≫
        (B.partialTotalSpectralAbutmentHomologyIso n).hom :=
  B.partialTotalStableStepImageFiltrationIso_hom_comp_ι n s

example (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStepImage
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex p) ≅
      (B.partialTotalHomologyFiltration n).obj
        (partialTotalHomologyPreviousIndex p) :=
  B.partialTotalStablePreviousImageFiltrationIso n p

example (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalImageMap
          (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) ≫
        (B.partialTotalStableStepImageFiltrationIso n p).hom =
      (B.partialTotalStablePreviousImageFiltrationIso n p).hom ≫
        B.partialTotalHomologyFiltrationAdjacentHom n p :=
  B.partialTotalStableImageMap_comp_currentIso_hom n p

example (n p : ℕ) : C := B.partialTotalStableObj n p

example (n p : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStep
        (-(n : ℤ)) ((p : ℤ) : EInt) ⟶
      (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) :=
  B.partialTotalSpectralStepToFiltration n p

example (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) ⟶
      B.partialTotalStableObj n p :=
  B.partialTotalHomologyFiltrationToStable n p

example (n p : ℕ) :
    B.partialTotalSpectralStepToFiltration n p ≫
        B.partialTotalHomologyFiltrationToStable n p =
      B.partialTotalSpectralObject.stableIntervalStepToStable
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) :=
  B.partialTotalSpectralStepToFiltration_comp_toStable n p

example (n p : ℕ) :
    (B.partialTotalStableStepImageFiltrationIso n p).hom ≫
        B.partialTotalHomologyFiltrationToStable n p =
      B.partialTotalSpectralObject.stableIntervalImageToStable
        (-(n : ℤ)) (partialTotalHomologyPreviousIndex_le p) :=
  B.partialTotalStableStepImageFiltrationIso_hom_comp_toStable n p

example (n : ℕ) :
    B.partialTotalSpectralObject.stableIntervalStepImage
        (-(n : ℤ)) (((-1 : ℤ) : EInt)) ≅
      (B.partialTotalHomologyFiltration n).obj (((-1 : ℤ) : EInt)) :=
  B.partialTotalStablePreviousImageFiltrationIso n 0

example (n p : ℕ) :
    B.partialTotalHomologyFiltrationAdjacentHom n p ≫
        B.partialTotalHomologyFiltrationToStable n p = 0 :=
  B.partialTotalHomologyFiltrationAdjacentHom_comp_toStable_zero n p

example (n p : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (B.partialTotalHomologyFiltrationToStable n p)
      (B.partialTotalHomologyFiltrationAdjacentHom_comp_toStable_zero n p)) :=
  B.partialTotalHomologyFiltrationToStableIsCokernel n p

example (n p : ℕ) :
    B.partialTotalStableObj n p ≅
      B.partialTotalHomologyGradedPiece n p :=
  B.partialTotalStableGradedIso n p

example (n p : ℕ) :
    B.partialTotalHomologyFiltrationToStable n p ≫
        (B.partialTotalStableGradedIso n p).hom =
      B.partialTotalHomologyGradedπ n p :=
  B.partialTotalHomologyFiltrationToStable_comp_stableGradedIso_hom n p

example : B.partialTotalStableObj 0 0 ≅
    B.partialTotalHomologyGradedPiece 0 0 :=
  B.partialTotalStableGradedIso 0 0

example : B.partialTotalStableObj 1 0 ≅
    B.partialTotalHomologyGradedPiece 1 0 :=
  B.partialTotalStableGradedIso 1 0

example : B.partialTotalStableObj 1 1 ≅
    B.partialTotalHomologyGradedPiece 1 1 :=
  B.partialTotalStableGradedIso 1 1

example : B.partialTotalStableObj 0 1 ≅
    B.partialTotalHomologyGradedPiece 0 1 :=
  B.partialTotalStableGradedIso 0 1

end HomologicalComplex₂

end
