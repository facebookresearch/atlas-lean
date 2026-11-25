/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Local presentability on an essentially small original presheaf site

The coefficient category and working cardinal universe remain fixed. The native
small-model equivalence transports the original diagrams, including all their
natural maps, to the small site where Mathlib's presheaf theorem applies.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w vD uD vA uA

namespace CategoryTheory

open Limits

variable (D : Type uD) [Category.{vD} D] [EssentiallySmall.{w} D]
  (A : Type uA) [Category.{vA} A]

/-- The actual index equivalence acts on the original coefficient-valued presheaves. -/
def presheafSmallModelEquivalence :
    (Dᵒᵖ ⥤ A) ≌ ((SmallModel.{w} D)ᵒᵖ ⥤ A) :=
  (equivSmallModel.{w} D).op.congrLeft

/-- The native coefficient presheaf theorem retains the same original cardinal. -/
theorem isCardinalLocallyPresentable_presheaf_of_essentiallySmall
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable A κ] [HasPullbacks A] :
    IsCardinalLocallyPresentable (Dᵒᵖ ⥤ A) κ := by
  let _ : IsCardinalLocallyPresentable ((SmallModel.{w} D)ᵒᵖ ⥤ A) κ := inferInstance
  exact (presheafSmallModelEquivalence D A).symm.isCardinalLocallyPresentable κ

/-- A fixed-universe locally presentable coefficient gives the same property on the
original essentially small site, without resizing its object or Hom representation. -/
theorem isLocallyPresentable_presheaf_of_essentiallySmall
    [IsLocallyPresentable.{w} A] [HasPullbacks A] :
    IsLocallyPresentable.{w} (Dᵒᵖ ⥤ A) := by
  let _ : IsLocallyPresentable.{w} ((SmallModel.{w} D)ᵒᵖ ⥤ A) := inferInstance
  exact (presheafSmallModelEquivalence D A).symm.isLocallyPresentable

end CategoryTheory
