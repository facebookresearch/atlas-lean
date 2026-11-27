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
# Adjacent triangular signs in right-derived connecting maps

The triangular signs `σ_n=(-1)^(n(n+1)/2)` satisfy
`σ_n σ_(n+1)=(-1)^(n+1)`. In an additive right-derived family,
conjugating a connecting map by the degree-`n` source normalization
and degree-`n+1` inverse target normalization multiplies it by
that adjacent-degree sign.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.ProjectiveResolution
/-- For `n ∈ ℕ`, the normalization signs satisfy
`σ_n σ_(n+1)=normalizationCrossSign(n)=(-1)^(n+1)`, where
`σ_n=(-1)^(n(n+1)/2)`. -/
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
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For short exact `S : X₁ → X₂ → X₃`,
conjugating `δ_n : R^nF(X₃) → R^(n+1)F(X₁)` by the degree-`n`
source normalization and inverse degree-`n+1` target normalization gives
`normalizationCrossSign(n) • δ_n`. -/
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
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For short exact `S : X₁ → X₂ → X₃`,
the normalized conjugate of its boundary
`δ_n : R^nF(X₃) → R^(n+1)F(X₁)` is `(-1)^(n+1) • δ_n`. -/
theorem rightDerivedConnecting_normalization_conjugate_closed (F : C ⥤ D) [F.Additive]
    (S : ShortComplex.ShortExactSequences C) (n : ℕ) :
    ((F.rightDerived n).acyclicResolutionNormalizationIso n).hom.app S.obj.X₃ ≫
      (F.rightDerivedConnecting n).app S ≫
      ((F.rightDerived (n + 1)).acyclicResolutionNormalizationIso (n + 1)).inv.app S.obj.X₁ =
    ((-1 : ℤ) ^ (n + 1)) • (F.rightDerivedConnecting n).app S := by
  exact F.rightDerivedConnecting_normalization_conjugate S n

end CategoryTheory.Functor
