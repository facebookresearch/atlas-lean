/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.SignedAugmentedAcyclicResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor

/-!
# right-derived coefficient boundaries under the proved scalar normalization
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.ProjectiveResolution
/-- Adjacent normalization scalars multiply to the original kernel-tail cross sign. -/
theorem acyclicResolutionNormalizationSign_adjacent_product (n : ℕ) :
    acyclicResolutionNormalizationSign n * acyclicResolutionNormalizationSign (n + 1) =
      normalizationCrossSign n := by
  change acyclicResolutionNormalizationSign n *
    (normalizationCrossSign n * acyclicResolutionNormalizationSign n) = normalizationCrossSign n
  rw [← mul_assoc, Int.mul_comm (acyclicResolutionNormalizationSign n) (normalizationCrossSign n),
    mul_assoc, acyclicResolutionNormalizationSign_mul_self, mul_one]
end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/--
Conjugating the SAME canonical coefficient boundary by the source and target normalization isos
gives its proved adjacent-degree cross sign.
-/
theorem rightDerivedConnecting_normalization_conjugate (F : C ⥤ D) [F.Additive]
    (S : ShortComplex.ShortExactSequences C) (n : ℕ) :
    ((F.rightDerived n).acyclicResolutionNormalizationIso n).hom.app S.obj.X₃ ≫
      (F.rightDerivedConnecting n).app S ≫
      ((F.rightDerived (n + 1)).acyclicResolutionNormalizationIso (n + 1)).inv.app S.obj.X₁ =
    ProjectiveResolution.normalizationCrossSign n • (F.rightDerivedConnecting n).app S := by
  let δ : (F.rightDerived n).obj S.obj.X₃ ⟶ (F.rightDerived (n + 1)).obj S.obj.X₁ :=
    (F.rightDerivedConnecting n).app S
  change (ProjectiveResolution.acyclicResolutionNormalizationSign n •
    𝟙 ((F.rightDerived n).obj S.obj.X₃)) ≫ δ ≫
    (ProjectiveResolution.acyclicResolutionNormalizationSign (n + 1) •
      𝟙 ((F.rightDerived (n + 1)).obj S.obj.X₁)) =
    ProjectiveResolution.normalizationCrossSign n • δ
  rw [zsmul_comp, Category.id_comp, comp_zsmul, Category.comp_id, smul_smul,
    ProjectiveResolution.acyclicResolutionNormalizationSign_adjacent_product]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient boundary formula has its literal exponent (-1)^(n+1). -/
theorem rightDerivedConnecting_normalization_conjugate_closed (F : C ⥤ D) [F.Additive]
    (S : ShortComplex.ShortExactSequences C) (n : ℕ) :
    ((F.rightDerived n).acyclicResolutionNormalizationIso n).hom.app S.obj.X₃ ≫
      (F.rightDerivedConnecting n).app S ≫
      ((F.rightDerived (n + 1)).acyclicResolutionNormalizationIso (n + 1)).inv.app S.obj.X₁ =
    ((-1 : ℤ) ^ (n + 1)) • (F.rightDerivedConnecting n).app S := by
  exact F.rightDerivedConnecting_normalization_conjugate S n

end CategoryTheory.Functor
