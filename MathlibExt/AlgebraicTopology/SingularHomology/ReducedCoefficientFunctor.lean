/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced

/-!
# Reduced singular homology as a coefficient functor

The augmentation from singular homology to the homology of a point is natural
jointly in spaces and coefficients. Its kernel defines reduced homology as a
coefficient functor, with comparison to the fixed-coefficient construction.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The homology of a point, constant in the space and functorial in coefficients. -/
noncomputable def pointSingularHomologyCoefficientFunctor (n : ℕ) :
    C ⥤ TopCat.{w} ⥤ C :=
  singularHomologyFunctor C n ⋙
    (evaluation TopCat.{w} C).obj (TopCat.of PUnit) ⋙
    Functor.const TopCat.{w}

@[simp]
theorem pointSingularHomologyCoefficientFunctor_obj (n : ℕ) (R : C) :
    (pointSingularHomologyCoefficientFunctor C n).obj R =
      pointSingularHomologyFunctor C R n :=
  rfl

/-- The augmentation, natural jointly in coefficients and spaces. -/
noncomputable def singularHomologyAugmentationCoefficient (n : ℕ) :
    singularHomologyFunctor C n ⟶ pointSingularHomologyCoefficientFunctor C n where
  app R := singularHomologyAugmentation C R n
  naturality R S f := by
    ext X
    change ((singularHomologyFunctor C n).map f).app X ≫
          ((singularHomologyFunctor C n).obj S).map (TopCat.isTerminalPUnit.from X) =
        ((singularHomologyFunctor C n).obj R).map (TopCat.isTerminalPUnit.from X) ≫
          ((singularHomologyFunctor C n).map f).app (TopCat.of PUnit)
    exact (((singularHomologyFunctor C n).map f).naturality
      (TopCat.isTerminalPUnit.from X)).symm

/-- The pointwise kernel functor underlying coefficient-natural reduced homology. -/
noncomputable def reducedSingularHomologyCoefficientKernelFunctor (n : ℕ) :
    C ⥤ TopCat.{w} ⥤ C :=
  kernel (singularHomologyAugmentationCoefficient C n)

/-- Evaluation of the coefficient-kernel functor is canonically the existing
fixed-coefficient reduced homology functor. -/
noncomputable def reducedSingularHomologyCoefficientObjIso (n : ℕ) (R : C) :
    (reducedSingularHomologyCoefficientKernelFunctor C n).obj R ≅
      reducedSingularHomologyFunctor C R n :=
  PreservesKernel.iso ((evaluation C (TopCat.{w} ⥤ C)).obj R)
    (singularHomologyAugmentationCoefficient C n)

@[reassoc]
theorem reducedSingularHomologyCoefficientObjIso_hom_ι (n : ℕ) (R : C) :
    (reducedSingularHomologyCoefficientObjIso C n R).hom ≫
        reducedSingularHomologyι C R n =
      (kernel.ι (singularHomologyAugmentationCoefficient C n)).app R := by
  change (PreservesKernel.iso ((evaluation C (TopCat.{w} ⥤ C)).obj R)
      (singularHomologyAugmentationCoefficient C n)).hom ≫
        kernel.ι (((evaluation C (TopCat.{w} ⥤ C)).obj R).map
          (singularHomologyAugmentationCoefficient C n)) =
      ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
        (kernel.ι (singularHomologyAugmentationCoefficient C n))
  rw [← cancel_epi (PreservesKernel.iso ((evaluation C (TopCat.{w} ⥤ C)).obj R)
      (singularHomologyAugmentationCoefficient C n)).inv]
  simp only [Iso.inv_hom_id_assoc]
  change kernel.ι (((evaluation C (TopCat.{w} ⥤ C)).obj R).map
      (singularHomologyAugmentationCoefficient C n)) =
    (PreservesKernel.iso ((evaluation C (TopCat.{w} ⥤ C)).obj R)
      (singularHomologyAugmentationCoefficient C n)).inv ≫
      ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
        (kernel.ι (singularHomologyAugmentationCoefficient C n))
  exact (PreservesKernel.iso_inv_ι ((evaluation C (TopCat.{w} ⥤ C)).obj R)
    (singularHomologyAugmentationCoefficient C n)).symm

/-- The coefficient map on the existing fixed-coefficient reduced homology objects. -/
noncomputable def reducedSingularHomologyCoefficientMap
    (n : ℕ) {R S : C} (f : R ⟶ S) :
    reducedSingularHomologyFunctor C R n ⟶
      reducedSingularHomologyFunctor C S n :=
  (reducedSingularHomologyCoefficientObjIso C n R).inv ≫
    (reducedSingularHomologyCoefficientKernelFunctor C n).map f ≫
    (reducedSingularHomologyCoefficientObjIso C n S).hom

@[reassoc (attr := simp)]
theorem reducedSingularHomologyCoefficientMap_comp_ι
    (n : ℕ) {R S : C} (f : R ⟶ S) :
    reducedSingularHomologyCoefficientMap C n f ≫ reducedSingularHomologyι C S n =
      reducedSingularHomologyι C R n ≫ (singularHomologyFunctor C n).map f := by
  simp only [reducedSingularHomologyCoefficientMap, Category.assoc]
  rw [reducedSingularHomologyCoefficientObjIso_hom_ι]
  have h : (reducedSingularHomologyCoefficientKernelFunctor C n).map f ≫
        (kernel.ι (singularHomologyAugmentationCoefficient C n)).app S =
      (kernel.ι (singularHomologyAugmentationCoefficient C n)).app R ≫
        (singularHomologyFunctor C n).map f := by
    simpa only [reducedSingularHomologyCoefficientKernelFunctor] using
      (kernel.ι (singularHomologyAugmentationCoefficient C n)).naturality f
  rw [h]
  have hR : (reducedSingularHomologyCoefficientObjIso C n R).inv ≫
          ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
            (kernel.ι (singularHomologyAugmentationCoefficient C n)) =
        reducedSingularHomologyι C R n := by
    change (PreservesKernel.iso ((evaluation C (TopCat.{w} ⥤ C)).obj R)
        (singularHomologyAugmentationCoefficient C n)).inv ≫
          ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
            (kernel.ι (singularHomologyAugmentationCoefficient C n)) =
        kernel.ι (((evaluation C (TopCat.{w} ⥤ C)).obj R).map
          (singularHomologyAugmentationCoefficient C n))
    exact (PreservesKernel.iso_inv_ι ((evaluation C (TopCat.{w} ⥤ C)).obj R)
      (singularHomologyAugmentationCoefficient C n))
  change (reducedSingularHomologyCoefficientObjIso C n R).inv ≫
          ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
            (kernel.ι (singularHomologyAugmentationCoefficient C n)) ≫
          (singularHomologyFunctor C n).map f =
        reducedSingularHomologyι C R n ≫ (singularHomologyFunctor C n).map f
  calc (reducedSingularHomologyCoefficientObjIso C n R).inv ≫
          ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
            (kernel.ι (singularHomologyAugmentationCoefficient C n)) ≫
          (singularHomologyFunctor C n).map f
      = ((reducedSingularHomologyCoefficientObjIso C n R).inv ≫
          ((evaluation C (TopCat.{w} ⥤ C)).obj R).map
            (kernel.ι (singularHomologyAugmentationCoefficient C n))) ≫
          (singularHomologyFunctor C n).map f := by
        rw [Category.assoc]
      _ = reducedSingularHomologyι C R n ≫ (singularHomologyFunctor C n).map f := by
        rw [hR]

/-- Reduced singular homology, with the existing fixed-coefficient functors as objects. -/
noncomputable def reducedSingularHomologyCoefficientFunctor (n : ℕ) :
    C ⥤ TopCat.{w} ⥤ C :=
  (reducedSingularHomologyCoefficientKernelFunctor C n).copyObj
    (fun R => reducedSingularHomologyFunctor C R n)
    (fun R => reducedSingularHomologyCoefficientObjIso C n R)

end AlgebraicTopology
