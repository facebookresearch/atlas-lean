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

import MathlibExt.Algebra.Homology.PartialTotalHomologyCoordinates

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (p : ℕ) :
    B.partialTotalCochainFiltration.obj ((p : ℤ) : EInt) ≅
      (B.partialTotal p).extend ComplexShape.embeddingDownNat :=
  B.partialTotalCochainFiltrationStageIso p

example :
    B.partialTotalCochainFiltration.obj ⊤ ≅
      (B.total (ComplexShape.down ℕ)).extend
        ComplexShape.embeddingDownNat :=
  B.partialTotalCochainFiltrationTopIso

example : IsZero (B.partialTotalCochainFiltration.obj ⊥) :=
  B.isZero_partialTotalCochainFiltration_obj_bot

example {p p' : ℕ} (h : p ≤ p') :
    ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp)) ⟶
      ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p' : ℤ) : EInt) by simp)) :=
  B.partialTotalSpectralStepArrow h

example (p : ℕ) :
    ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp)) ⟶
      ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ⊤ by simp)) :=
  B.partialTotalSpectralStepToAbutmentArrow p

example (n p : ℕ) :
    ((B.partialTotalSpectralObject.H (-(n : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp)))) ≅
      (B.partialTotal p).homology n :=
  B.partialTotalSpectralStepHomologyIso n p

example (n : ℕ) :
    ((B.partialTotalSpectralObject.H (-(n : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ⊤ by simp)))) ≅
      (B.total (ComplexShape.down ℕ)).homology n :=
  B.partialTotalSpectralAbutmentHomologyIso n

example :
    ((B.partialTotalSpectralObject.H 0).obj
      (ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
      (B.partialTotal 0).homology 0 :=
  B.partialTotalSpectralStepHomologyIso 0 0

example (n p : ℕ) :
    (B.partialTotalSpectralStepHomologyIso n p).inv =
      ((B.partialTotal p).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).inv ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalCochainFiltrationStageIso p) (-(n : ℤ))).inv ≫
      (CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltrationBottomStageMap p)
        B.isZero_partialTotalCochainFiltration_obj_bot (-(n : ℤ))).inv ≫
      (B.partialTotalSpectralObjectHObjIso (-(n : ℤ)) (by simp)).inv :=
  B.partialTotalSpectralStepHomologyIso_inv n p

example :
    (B.partialTotalSpectralStepHomologyIso 0 0).inv =
      ((B.partialTotal 0).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).inv ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalCochainFiltrationStageIso 0) 0).inv ≫
      (CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltrationBottomStageMap 0)
        B.isZero_partialTotalCochainFiltration_obj_bot 0).inv ≫
      (B.partialTotalSpectralObjectHObjIso 0 (by simp)).inv := by
  simpa using B.partialTotalSpectralStepHomologyIso_inv 0 0

example (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    (B.partialTotalSpectralObject.H (-(n : ℤ))).map
        (B.partialTotalSpectralStepArrow h) ≫
      (B.partialTotalSpectralStepHomologyIso n p').hom =
    (B.partialTotalSpectralStepHomologyIso n p).hom ≫
      HomologicalComplex.homologyMap (B.partialTotalMap h) n :=
  B.partialTotalSpectralStepHomologyIso_hom_naturality n h

example (n p : ℕ) :
    (B.partialTotalSpectralObject.H (-(n : ℤ))).map
        (B.partialTotalSpectralStepToAbutmentArrow p) ≫
      (B.partialTotalSpectralAbutmentHomologyIso n).hom =
    (B.partialTotalSpectralStepHomologyIso n p).hom ≫
      HomologicalComplex.homologyMap (B.partialTotalι p) n :=
  B.partialTotalSpectralStepToAbutment_comp_iso_hom n p

example (s k : ℕ) (h : k ≤ s) :
    Epi (HomologicalComplex.homologyMap (B.partialTotalι s) k) :=
  B.epi_homologyMap_partialTotalι_of_le s k h

example (s k : ℕ) (h : k < s) :
    Mono (HomologicalComplex.homologyMap (B.partialTotalι s) k) :=
  B.mono_homologyMap_partialTotalι_of_lt s k h

example (s : ℕ) :
    Epi (HomologicalComplex.homologyMap (B.partialTotalι s) s) :=
  B.epi_homologyMap_partialTotalι_of_le s s le_rfl

example (k : ℕ) :
    Mono (HomologicalComplex.homologyMap (B.partialTotalι (k + 1)) k) :=
  B.mono_homologyMap_partialTotalι_of_lt (k + 1) k (by omega)

example :
    Mono (HomologicalComplex.homologyMap (B.partialTotalι 1) 0) :=
  B.mono_homologyMap_partialTotalι_of_lt 1 0 (by omega)

example :
    Epi (HomologicalComplex.homologyMap (B.partialTotalι 0) 0) :=
  B.epi_homologyMap_partialTotalι_of_le 0 0 le_rfl

end HomologicalComplex₂

end
