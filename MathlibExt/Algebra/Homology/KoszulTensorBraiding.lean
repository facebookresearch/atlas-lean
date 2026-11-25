/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import MathlibExt.Algebra.Homology.BifunctorBraiding

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive]
  [∀ T : C, ((curriedTensor C).obj T).Additive]
variable {I : Type w} [AddCommMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns] [TotalComplexShapeSymmetry c c c]

section Braided

variable [BraidedCategory C]

noncomputable def koszulTensorBraidingIso
    (K L : HomologicalComplex C c) [HasTensor K L] [HasTensor L K] :
    tensorObj K L ≅ tensorObj L K :=
  (mapBifunctorFlipIso K L (curriedTensor C) c).symm ≪≫
    HomologicalComplex₂.total.mapIso
      (mapBifunctorFlipBraidingIso L K) c

@[reassoc]
theorem ιTensorObj_koszulTensorBraidingIso_hom
    (K L : HomologicalComplex C c) [HasTensor K L] [HasTensor L K]
    (p q n : I) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (koszulTensorBraidingIso K L).hom.f n =
      c.σ c c p q •
        ((β_ (K.X p) (L.X q)).hom ≫
          ιTensorObj L K q p n (by rw [add_comm, h])) := by
  unfold koszulTensorBraidingIso
  simp only [Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ι_mapBifunctorFlipIso_inv, Linear.units_smul_comp]
  change c.σ c c p q •
    (((((curriedTensor C).flip.mapBifunctorHomologicalComplex c c).obj L).obj K).ιTotal
      c q p n _ ≫
      (HomologicalComplex₂.total.map
        (mapBifunctorFlipBraidingIso L K).hom c).f n) = _
  rw [HomologicalComplex₂.ιTotal_map]
  rw [mapBifunctorFlipBraidingIso_hom_f_f]
  congr

@[reassoc]
theorem koszulTensorBraidingIso_hom_naturality
    {K L K' L' : HomologicalComplex C c}
    [HasTensor K L] [HasTensor L K] [HasTensor K' L'] [HasTensor L' K']
    (f : K ⟶ K') (g : L ⟶ L') :
    tensorHom f g ≫ (koszulTensorBraidingIso K' L').hom =
      (koszulTensorBraidingIso K L).hom ≫ tensorHom g f := by
  ext n p q h
  simp only [HomologicalComplex.comp_f]
  rw [ι_mapBifunctorMap_assoc]
  rw [ιTensorObj_koszulTensorBraidingIso_hom]
  rw [ιTensorObj_koszulTensorBraidingIso_hom_assoc]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul,
    Category.assoc]
  rw [ι_mapBifunctorMap]
  congr 1
  simpa only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
    curriedTensor_obj_map, Category.assoc] using
    BraidedCategory.braiding_naturality_assoc (f.f p) (g.f q)
      (ιTensorObj L' K' q p n (by simpa [add_comm] using h))

end Braided

section Symmetric

variable [SymmetricCategory C]

@[simp]
theorem koszulTensorBraidingIso_hom_hom
    (K L : HomologicalComplex C c)
    [HasTensor K L] [HasTensor L K]
    [TotalComplexShapeSymmetrySymmetry c c c] :
    (koszulTensorBraidingIso K L).hom ≫
        (koszulTensorBraidingIso L K).hom = 𝟙 _ := by
  ext n p q h
  simp only [HomologicalComplex.comp_f]
  rw [ιTensorObj_koszulTensorBraidingIso_hom_assoc]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [ιTensorObj_koszulTensorBraidingIso_hom]
  simp only [Linear.comp_units_smul]
  rw [ComplexShape.σ_symm]
  rw [← mul_smul, Int.units_mul_self, one_smul]
  simp only [SymmetricCategory.symmetry_assoc,
    HomologicalComplex.id_f, Category.comp_id]

end Symmetric

end HomologicalComplex
