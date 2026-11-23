/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
import MathlibExt.CategoryTheory.DGSource.CochainBraiding

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts

set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MathlibExtTest.CategoryTheory.DGCategoryTraceKoszul

abbrev flat : Cochains ℚ where
  X _ := ModuleCat.of ℚ ℚ
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def oddPair : (flat ⊗ flat).X 2 :=
  (HomologicalComplex.ιTensorObj flat flat 1 1 2 rfl).hom
    (TensorProduct.tmul ℚ (1 : ℚ) (1 : ℚ))

/-! Two actual odd coefficients acquire the Koszul minus sign used by the
DG cyclic word rotation; the underlying coefficient tensor is nonzero. -/
example : ((β_ flat flat).hom.f 2).hom oddPair = -oddPair := by
  unfold oddPair
  change ((HomologicalComplex.ιTensorObj flat flat 1 1 2 rfl ≫ (β_ flat flat).hom.f 2).hom
      (TensorProduct.tmul ℚ (1 : ℚ) (1 : ℚ))) =
    -(HomologicalComplex.ιTensorObj flat flat 1 1 2 rfl).hom (TensorProduct.tmul ℚ (1 : ℚ) (1 : ℚ))
  rw [braiding_eq_koszulBraiding, koszulBraiding_hom,
    ι_koszulBraidingHom, koszulBraidingSummand_def]
  simp
  have hb : (β_ (flat.X 1) (flat.X 1)).hom.hom (TensorProduct.tmul ℚ (1 : ℚ) (1 : ℚ)) =
      TensorProduct.tmul ℚ (1 : ℚ) (1 : ℚ) := rfl
  rw [hb]
  rfl

example : TensorProduct.tmul ℚ (1 : ℚ) (1 : ℚ) ≠ 0 := by
  intro h
  have hm := congrArg (TensorProduct.lid ℚ ℚ) h
  norm_num at hm

end MathlibExtTest.CategoryTheory.DGCategoryTraceKoszul
