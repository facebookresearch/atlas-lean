/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentCardinalColimits

/-! Supplied original cocones and their two projection equations. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s v v'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SmallObject.PresheafAttachmentCardinalColimitsTest
variable {D : Type w} [SmallCategory D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
    (μ : Cardinal.{max u w}) [Fact μ.IsRegular] [∀ i, Mono (j i)]
    [∀ i, IsCardinalPresentable.{max u w} (A i) μ]
    [∀ i, IsCardinalPresentable.{max u w} (B i) μ]

/-- An actual original cocone, including larger essentially-small shapes. -/
def original_supplied_cocone
    {J : Type v} [Category.{v'} J] [EssentiallySmall.{max u w} J] [IsCardinalFiltered J μ]
    {F : J ⥤ Arrow (Dᵒᵖ ⥤ Type (max u w))} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((SmallObject.functor j).mapCocone c) := by
  let _ : (SmallObject.functor j).IsCardinalAccessible μ :=
    presheafAttachment_isCardinalAccessible j μ
  let _ : PreservesColimitsOfShape J (SmallObject.functor j) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
      (SmallObject.functor j) μ J
  exact isColimitOfPreserves (SmallObject.functor j) hc

/-- The mapped cocone's factorization equations use the prescribed original injections. -/
theorem original_injection_factorizations
    {J : Type v} [Category.{v'} J] [EssentiallySmall.{max u w} J] [IsCardinalFiltered J μ]
    {F : J ⥤ Arrow (Dᵒᵖ ⥤ Type (max u w))} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone (F ⋙ SmallObject.functor j)) (k : J) :
    ((SmallObject.functor j).map (c.ι.app k)).left ≫
        ((original_supplied_cocone j μ hc).desc s).left = (s.ι.app k).left ∧
    ((SmallObject.functor j).map (c.ι.app k)).right ≫
        ((original_supplied_cocone j μ hc).desc s).right = (s.ι.app k).right := by
  have h := (original_supplied_cocone j μ hc).fac s k
  exact ⟨congrArg Arrow.Hom.left h, congrArg Arrow.Hom.right h⟩

/-- Equality of whole original maps is reflected through the preserved cocone. -/
theorem original_whole_map_uniqueness
    {J : Type v} [Category.{v'} J] [EssentiallySmall.{max u w} J] [IsCardinalFiltered J μ]
    {F : J ⥤ Arrow (Dᵒᵖ ⥤ Type (max u w))} {c : Cocone F} (hc : IsColimit c)
    {Z : Arrow (Dᵒᵖ ⥤ Type (max u w))}
    (a b : (SmallObject.functor j).obj c.pt ⟶ Z)
    (h : ∀ k, (SmallObject.functor j).map (c.ι.app k) ≫ a =
      (SmallObject.functor j).map (c.ι.app k) ≫ b) : a = b :=
  (original_supplied_cocone j μ hc).hom_ext h
end CategoryTheory.SmallObject.PresheafAttachmentCardinalColimitsTest
