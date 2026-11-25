/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.ProjectiveFlatTargetTensor
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorAugmentation
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import MathlibExt.Algebra.Homology.ChainComplexAugmentationHomology
public import MathlibExt.Algebra.Homology.ChainComplex.ToSingleHomologyZero

/-!
# Degree-zero tensor homology and coefficient universe transport

For a projective resolution and an arbitrary coefficient module, the tensor
augmentation identifies degree-zero homology with the tensor product of the
resolved module. Componentwise unlifting compares coefficient tensor complexes
formed in different carrier universes.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]
  (M : ModuleCat.{v} R) {X : ModuleCat.{max u w} R}
  (P : ProjectiveResolution X)

/-- The tensor augmentation identifies degree-zero homology with the tensor product. -/
def projectiveCoefficientHomologyZeroIso :
    (projectiveCoefficientComplex R M P).homology 0 ≅
      ((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X := by
  let F := (tensorBifunctorAt.{u, v, max u w} R).obj M
  let _ : PreservesFiniteColimits F := projectiveCoefficientTensor_preservesFiniteColimits R M
  exact ChainComplex.homologyZeroIsoOfPreservedAugmentation F P.π

/-- The degree-zero comparison sends the homology class map to the tensor augmentation. -/
@[reassoc]
theorem projectiveCoefficientHomologyZeroIso_class :
    ChainComplex.homologyZeroClass (projectiveCoefficientComplex R M P) ≫
      (projectiveCoefficientHomologyZeroIso R M P).hom =
        ((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0) := by
  let F := (tensorBifunctorAt.{u, v, max u w} R).obj M
  let _ : PreservesFiniteColimits F := projectiveCoefficientTensor_preservesFiniteColimits R M
  exact ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom F P.π

/-- Homology of the tensor augmentation agrees with the degree-zero comparison. -/
@[reassoc]
theorem projectiveCoefficientAugmentation_homology_zero :
    HomologicalComplex.homologyMap (projectiveCoefficientAugmentation R M P) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0
        (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X)).hom =
      (projectiveCoefficientHomologyZeroIso R M P).hom := by
  apply Cofork.IsColimit.hom_ext
    (ChainComplex.homologyZeroCoforkIsColimit (projectiveCoefficientComplex R M P))
  exact (ChainComplex.homologyZeroClass_toSingle (projectiveCoefficientAugmentation R M P)).trans
    ((projectiveCoefficientAugmentation_f_zero R M P).trans
      (projectiveCoefficientHomologyZeroIso_class R M P).symm)

/-- The coefficient module lifted to the common coefficient and target universe. -/
def auxiliaryCoefficient : ModuleCat.{max u v w} R :=
  ModuleCat.of R (ULift.{max u w} M)

/-- Unlifting the coefficient gives a natural isomorphism of tensor functors. -/
def coefficientUnliftNatIso :
    (tensorBifunctorAt.{u, max u v w, max u w} R).obj (auxiliaryCoefficient.{u, v, w} R M) ≅
      (tensorBifunctorAt.{u, v, max u w} R).obj M :=
  NatIso.ofComponents (fun Y =>
    (TensorProduct.congr (ULift.moduleEquiv : ULift.{max u w} M ≃ₗ[R] M)
      (LinearEquiv.refl R Y)).toModuleIso) (by
        intro Y Z g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m y
        change m.down ⊗ₜ[R] g.hom y = m.down ⊗ₜ[R] g.hom y
        rfl)

/-- Componentwise coefficient unlifting identifies the two tensor complexes. -/
def coefficientUnliftComplexIso :
    ((((tensorBifunctorAt.{u, max u v w, max u w} R).obj (auxiliaryCoefficient.{u, v, w} R M)).mapHomologicalComplex
      (.down ℕ)).obj P.complex) ≅ projectiveCoefficientComplex R M P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientUnliftNatIso.{u, v, w} R M).app (P.complex.X n))
    (by
      intro i j _h
      exact ((coefficientUnliftNatIso.{u, v, w} R M).hom.naturality (P.complex.d i j)).symm)

end ModuleCat
