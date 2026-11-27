/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitizationRelative

/-!
# Hochschild homology defined by the unitization cokernel

Let `k` be a commutative ring and `A` a nonunital ground algebra. The scalar section `k → A⁺ =
k ⊕ A` induces a map on regular Hochschild homology. Define the unitization Hochschild model
in degree `n` as its cokernel `coker(HH_n(k) → HH_n(A⁺))`.

The scalar section and augmentation split the scalar projector on the chain complex of `A⁺`.
Its complementary kernel is the relative complex. The cokernel model is naturally isomorphic
to homology of this kernel and to homology of its reduced normalized complex. The comparisons
use the complementary retraction and the restricted normalization map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The unitization cokernel model of nonunital Hochschild homology.

In degree `n`, this is the cokernel of the homology map induced by the scalar inclusion into
the regular Hochschild complex of `A⁺`. -/
abbrev unitizationHochschildHomology (n : ℕ) : ModuleCat.{max u v} k :=
  cokernel (HomologicalComplex.homologyMap (unitizationScalarComplexInclusion k A) n)

/-- The comparison of unitization cokernel homology with relative homology.

The scalar augmentation and section identify `coker(HH_n(k) → HH_n(A⁺))` with the homology of
the complementary kernel of the scalar chain projector. -/
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

/-- The comparison of unitization cokernel homology with reduced normalization.

The relative homology comparison followed by the restricted normalization isomorphism
identifies the unitization cokernel model with homology of the reduced normalized complex. -/
def unitizationHochschildReducedNormalizedIso (n : ℕ) :
    unitizationHochschildHomology k A n ≅
      (unitizationReducedNormalizedComplex k A).homology n :=
  unitizationHochschildRelativeIso k A n ≪≫
    asIso (HomologicalComplex.homologyMap (unitizationRelativeNormalization k A) n)

/-- The cokernel projection in relative homology coordinates.

The cokernel projection followed by the relative comparison is the homology map of the
complementary chain retraction from the unitization complex to the kernel of its scalar
projector. -/
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

/-- The map of the unitization reduced-normalization comparison.

The forward isomorphism is the relative homology comparison followed by the homology map of
the relative normalization chain map. -/
theorem unitizationHochschildReducedNormalizedIso_hom (n : ℕ) :
    (unitizationHochschildReducedNormalizedIso k A n).hom =
      (unitizationHochschildRelativeIso k A n).hom ≫
        HomologicalComplex.homologyMap (unitizationRelativeNormalization k A) n := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
