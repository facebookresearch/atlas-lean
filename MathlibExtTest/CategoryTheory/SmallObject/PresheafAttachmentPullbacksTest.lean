/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentPullbacks

/-! Original-square consumers of the native Arrow pullback preservation theorem. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.SmallObject.PresheafAttachmentPullbacksTest
variable {D : Type w} [SmallCategory D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)

theorem original_supplied_square [∀ i, Mono (j i)]
    {P X V Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
    {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
    (h : IsPullback a b f g) :
    IsPullback ((SmallObject.functor j).map a) ((SmallObject.functor j).map b)
      ((SmallObject.functor j).map f) ((SmallObject.functor j).map g) := by
  let _ : PreservesLimitsOfShape WalkingCospan (SmallObject.functor j) :=
    presheafAttachment_preservesPullbacks j
  exact h.map (SmallObject.functor j)

theorem original_right_components
    {P X V Y : Arrow (Dᵒᵖ ⥤ Type (max u w))}
    {a : P ⟶ X} {b : P ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y} :
    ((SmallObject.functor j).map a).right = a.right ∧
    ((SmallObject.functor j).map b).right = b.right ∧
    ((SmallObject.functor j).map f).right = f.right ∧
    ((SmallObject.functor j).map g).right = g.right :=
  ⟨rfl, rfl, rfl, rfl⟩

end CategoryTheory.SmallObject.PresheafAttachmentPullbacksTest
