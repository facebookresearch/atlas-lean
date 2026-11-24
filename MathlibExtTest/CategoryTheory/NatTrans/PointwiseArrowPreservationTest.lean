/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation

/-!
# Tests for preservation by pointwise arrow functors
-/

@[expose] public section

noncomputable section

universe vB uB vC uC vJ uJ w

open CategoryTheory Limits

namespace CategoryTheory.NatTransPreservationTest

variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {J : Type uJ} [Category.{vJ} J]
variable {F G : B ⥤ C} (α : F ⟶ G)

example [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (NatTrans.arrow α) :=
  NatTrans.arrow_preservesLimitsOfShape α J

example [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G]
    {D : J ⥤ B} (c : Cone D) (hc : IsLimit c) :
    IsLimit ((NatTrans.arrow α).mapCone c) := by
  let _ : PreservesLimitsOfShape J (NatTrans.arrow α) :=
    NatTrans.arrow_preservesLimitsOfShape α J
  exact isLimitOfPreserves (NatTrans.arrow α) hc

example [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (NatTrans.arrow α) :=
  NatTrans.arrow_preservesColimitsOfShape α J

example [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G]
    {D : J ⥤ B} (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((NatTrans.arrow α).mapCocone c) := by
  let _ : PreservesColimitsOfShape J (NatTrans.arrow α) :=
    NatTrans.arrow_preservesColimitsOfShape α J
  exact isColimitOfPreserves (NatTrans.arrow α) hc

example (μ : Cardinal.{w}) [Fact μ.IsRegular]
    [F.IsCardinalAccessible μ] [G.IsCardinalAccessible μ] :
    (NatTrans.arrow α).IsCardinalAccessible μ :=
  NatTrans.arrow_isCardinalAccessible α μ

example {X Y : B} (f : X ⟶ Y) :
    ((NatTrans.arrow α).map f).left = F.map f ∧
      ((NatTrans.arrow α).map f).right = G.map f :=
  ⟨rfl, rfl⟩

section Terminal

variable [HasTerminal C]

example : PreservesLimitsOfShape J (terminal.arrowFunctor C) :=
  terminal.arrowFunctor_preservesLimitsOfShape C J

example (μ : Cardinal.{w}) [Fact μ.IsRegular] :
    (terminal.arrowFunctor C).IsCardinalAccessible μ :=
  terminal.arrowFunctor_isCardinalAccessible C μ

example :
    PreservesLimitsOfShape (Discrete PEmpty) (terminal.arrowFunctor C) :=
  terminal.arrowFunctor_preservesLimitsOfShape C (Discrete PEmpty)

example {K : WalkingCospan ⥤ C}
    (c : Cone K) (hc : IsLimit c) :
    IsLimit ((terminal.arrowFunctor C).mapCone c) := by
  let _ : PreservesLimitsOfShape WalkingCospan (terminal.arrowFunctor C) :=
    terminal.arrowFunctor_preservesLimitsOfShape C WalkingCospan
  exact isLimitOfPreserves (terminal.arrowFunctor C) hc

example (X : C) :
    ((terminal.arrowFunctor C).obj X).left = X ∧
      ((terminal.arrowFunctor C).obj X).right = (⊤_ C) ∧
      ((terminal.arrowFunctor C).obj X).hom = terminal.from X :=
  ⟨rfl, rfl, rfl⟩

end Terminal

section Initial

variable [HasInitial C]

example : PreservesColimitsOfShape J (initial.arrowFunctor C) :=
  initial.arrowFunctor_preservesColimitsOfShape C J

example (μ : Cardinal.{w}) [Fact μ.IsRegular] :
    (initial.arrowFunctor C).IsCardinalAccessible μ :=
  initial.arrowFunctor_isCardinalAccessible C μ

example :
    PreservesColimitsOfShape (Discrete PEmpty) (initial.arrowFunctor C) :=
  initial.arrowFunctor_preservesColimitsOfShape C (Discrete PEmpty)

example (X : C) :
    ((initial.arrowFunctor C).obj X).left = (⊥_ C) ∧
      ((initial.arrowFunctor C).obj X).right = X ∧
      ((initial.arrowFunctor C).obj X).hom = initial.to X :=
  ⟨rfl, rfl, rfl⟩

end Initial

section Filtered

variable (K : Type w) [SmallCategory K]
variable (μ : Cardinal.{w}) [Fact μ.IsRegular] [IsCardinalFiltered K μ]

example [HasTerminal C] {D : K ⥤ C} (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((terminal.arrowFunctor C).mapCocone c) := by
  let _ : (terminal.arrowFunctor C).IsCardinalAccessible μ :=
    terminal.arrowFunctor_isCardinalAccessible C μ
  let _ : PreservesColimitsOfShape K (terminal.arrowFunctor C) :=
    (terminal.arrowFunctor C).preservesColimitsOfShape_of_isCardinalAccessible μ K
  exact isColimitOfPreserves (terminal.arrowFunctor C) hc

example [HasInitial C] {D : K ⥤ C} (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((initial.arrowFunctor C).mapCocone c) := by
  let _ : (initial.arrowFunctor C).IsCardinalAccessible μ :=
    initial.arrowFunctor_isCardinalAccessible C μ
  let _ : PreservesColimitsOfShape K (initial.arrowFunctor C) :=
    (initial.arrowFunctor C).preservesColimitsOfShape_of_isCardinalAccessible μ K
  exact isColimitOfPreserves (initial.arrowFunctor C) hc

end Filtered

end CategoryTheory.NatTransPreservationTest
