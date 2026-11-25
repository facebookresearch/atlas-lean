/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationRelative

/-!
# Unitization cokernel Hochschild homology

Regular Hochschild homology of the
unitization receives the scalar inclusion.
Its cokernel defines this nonunital
Hochschild model. The scalar projector
splits that inclusion and compares the
model with the relative complex and
its reduced normalization.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The source extension HH(A) is the cokernel of the original scalar inclusion HH(k)→HH(A⁺). -/
abbrev unitizationHochschildHomology (n : ℕ) : ModuleCat.{max u v} k :=
  cokernel (HomologicalComplex.homologyMap (unitizationScalarComplexInclusion k A) n)

/-- The source cokernel agrees with homology of the original relative kernel.
Both comparisons are from the original augmentation and scalar section. -/
def unitizationHochschildRelativeIso (n : ℕ) :
    unitizationHochschildHomology k A n ≅ (unitizationRelativeComplex k A).homology n := by
  let F := homologyFunctor (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n
  let p := unitizationScalarComplexProjector k A
  let j := kernel.ι p
  let ρ := projectorKernelRetraction p (unitizationScalarComplexProjector_idempotent k A)
  let s := unitizationScalarComplexInclusion k A
  let r := unitizationScalarComplexAugmentation k A
  have hsr : s ≫ r = 𝟙 _ := unitizationScalarComplexInclusion_augmentation k A
  have hrsp : r ≫ s = p := unitizationScalarComplexAugmentation_inclusion k A
  have hjρ : j ≫ ρ = 𝟙 _ :=
    ι_projectorKernelRetraction p (unitizationScalarComplexProjector_idempotent k A)
  have hρj : ρ ≫ j = 𝟙 _ - p :=
    projectorKernelRetraction_ι p (unitizationScalarComplexProjector_idempotent k A)
  letI : IsSplitEpi (F.map r) := ⟨⟨
    { section_ := F.map s
      id := by rw [← F.map_comp, hsr, F.map_id] }⟩⟩
  have hpF : F.map r ≫ F.map s = F.map p := by
    rw [← F.map_comp, hrsp]
  have hjρF : F.map j ≫ F.map ρ = 𝟙 _ := by
    rw [← F.map_comp, hjρ, F.map_id]
  have hqF : F.map p = 𝟙 _ - F.map ρ ≫ F.map j := by
    rw [← F.map_comp, hρj, Functor.map_sub, F.map_id]
    abel
  exact (cokernelEpiComp (F.map r) (F.map s)).symm ≪≫
    cokernelIsoOfEq hpF ≪≫
    cokernelSplitComplementIso (F.map p) (F.map j) (F.map ρ) hjρF hqF

/-- The original restricted normalization supplies the homology isomorphism. -/
def unitizationHochschildReducedNormalizedIso (n : ℕ) :
    unitizationHochschildHomology k A n ≅
      (unitizationReducedNormalizedComplex k A).homology n :=
  unitizationHochschildRelativeIso k A n ≪≫
    asIso (HomologicalComplex.homologyMap (unitizationRelativeNormalization k A) n)

/-- The source cokernel projection computes the original complementary retraction on homology. -/
@[reassoc]
theorem unitizationHochschildRelativeIso_π_hom (n : ℕ) :
    cokernel.π (HomologicalComplex.homologyMap (unitizationScalarComplexInclusion k A) n) ≫
        (unitizationHochschildRelativeIso k A n).hom =
      HomologicalComplex.homologyMap
        (projectorKernelRetraction (unitizationScalarComplexProjector k A)
          (unitizationScalarComplexProjector_idempotent k A)) n := by
  unfold unitizationHochschildRelativeIso
  erw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, cokernelEpiComp_inv,
    cokernel.π_desc_assoc,
    π_comp_cokernelIsoOfEq_hom_assoc, cokernelSplitComplementIso_π_hom]
  rfl

/-- The source comparison really uses the original normalization map on relative homology. -/
theorem unitizationHochschildReducedNormalizedIso_hom (n : ℕ) :
    (unitizationHochschildReducedNormalizedIso k A n).hom =
      (unitizationHochschildRelativeIso k A n).hom ≫
        HomologicalComplex.homologyMap (unitizationRelativeNormalization k A) n := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
