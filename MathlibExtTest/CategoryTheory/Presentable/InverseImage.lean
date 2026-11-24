/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Presentable.InverseImage
import MathlibExt.CategoryTheory.Presentable.SurjectiveArrow

/-!
The original inverse image retains a genuinely nonidentity comparison and
both its maps. The identity inverse image of the actual surjection category
exercises the complete accessibility construction with its actual inclusion.
-/

set_option autoImplicit false
noncomputable section

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Presentable

section IndependentUniverses

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

example [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (F : C ⥤ D) [Functor.IsAccessible.{w} F]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [IsAccessibleCategory.{w} P.FullSubcategory] [Functor.IsAccessible.{w} P.ι] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory (P.inverseImage F).FullSubcategory κ ∧
        (P.inverseImage F).ι.IsCardinalAccessible κ := inverseImage_accessible F P

end IndependentUniverses

/-- The actual exchange of the two original points. -/
def flipPair : ULift.{w} Bool ≃ ULift.{w} Bool where
  toFun b := ⟨!b.down⟩
  invFun b := ⟨!b.down⟩
  left_inv b := by rcases b with ⟨b⟩; cases b <;> rfl
  right_inv b := by rcases b with ⟨b⟩; cases b <;> rfl

/-- The nonidentity automorphism of the original fold arrow. -/
def flipFoldIso : relationArrow.{w}.obj ≅ relationArrow.{w}.obj :=
  Arrow.isoMk flipPair.toIso (Iso.refl (PUnit.{w + 1})) (by ext; rfl)

/-- The original nonidentity comparison in the isomorphism-comma category. -/
def originalFlipComparison :
    IsomorphismComma (𝟭 (Arrow (Type w))) surjectiveArrows.{w}.ι :=
  ⟨{ left := relationArrow.obj, right := relationArrow, hom := flipFoldIso.hom },
    (inferInstance : IsIso flipFoldIso.hom)⟩

example : ((inverseImageEquivalence (𝟭 (Arrow (Type w))) surjectiveArrows).inverse.obj
    originalFlipComparison).obj = relationArrow.obj := rfl

example : (((inverseImageEquivalence (𝟭 (Arrow (Type w))) surjectiveArrows).counitIso.hom.app
    originalFlipComparison).hom.right.hom).left ⟨false⟩ = ⟨true⟩ := rfl

example : (((inverseImageEquivalence (𝟭 (Arrow (Type w))) surjectiveArrows).counitIso.inv.app
    originalFlipComparison).hom.right.hom).left ⟨false⟩ = ⟨true⟩ := by
  have h := congrFun
    (inverseImageEquivalence_counit_inv_right (𝟭 (Arrow (Type w))) surjectiveArrows)
    originalFlipComparison
  rw [h]
  change (inv flipFoldIso.{w}.hom).left ⟨false⟩ = ⟨true⟩
  have hInv : inv flipFoldIso.{w}.hom = flipFoldIso.{w}.inv :=
    (IsIso.eq_inv_of_hom_inv_id flipFoldIso.{w}.hom_inv_id).symm
  rw [hInv]
  rfl

/-- The actual surjection inclusion supplies the inverse-image hypotheses internally. -/
example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory
      (surjectiveArrows.inverseImage (𝟭 (Arrow (Type w)))).FullSubcategory κ ∧
        (surjectiveArrows.inverseImage (𝟭 (Arrow (Type w)))).ι.IsCardinalAccessible κ := by
  have : IsAccessibleCategory.{w} SurjectiveArrow.{w} := surjectiveArrow_accessible.1
  have : Functor.IsAccessible.{w} surjectiveArrows.{w}.ι := surjectiveArrow_accessible.2
  exact inverseImage_accessible (𝟭 (Arrow (Type w))) surjectiveArrows
