/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Base change between small étale sites

For a scheme morphism `f : X ⟶ Y`, base change sends étale objects over
`Y` to their fiber products with `X`. It preserves finite limits and
has identity and composition comparisons.
Milne, *Lectures on Étale Cohomology*,
§8, page 58, Lemma 8.1, proves this covering and fiber-product argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.Scheme.DerivedSections

set_option backward.isDefEq.respectTransparency.types false in
/-- Base change on the actual original small étale categories. -/
abbrev smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale.{u}) ⊤ f

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical identity comparison, lifted from the stock over-category
identity comparison through the actual fully faithful étale forgetful functor. -/
def smallEtaleBaseChangeId (X : Scheme.{u}) :
    smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  let G := Scheme.Etale.forget X
  let H := (Functor.whiskeringRight X.Etale X.Etale (CategoryTheory.Over X)).obj G
  H.preimageIso
    (MorphismProperty.Over.pullbackCompForgetIso
        (P := @AlgebraicGeometry.Etale.{u}) (Q := ⊤) (𝟙 X) ≪≫
      Functor.isoWhiskerLeft G (CategoryTheory.Over.pullbackId (X := X)) ≪≫
      Functor.rightUnitor G ≪≫ (Functor.leftUnitor G).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical composition comparison between the actual single and
iterated fiber products on the original small étale categories. -/
def smallEtaleBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleBaseChange (f ≫ g) ≅ smallEtaleBaseChange g ⋙ smallEtaleBaseChange f :=
  MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale.{u}) (Q := ⊤) f g

set_option backward.isDefEq.respectTransparency.types false in
/-- The stock morphism-property provider applies to every scheme morphism. -/
theorem smallEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleBaseChange f) := by
  exact inferInstanceAs
    (PreservesFiniteLimits
      (MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale.{u}) ⊤ f))

end AlgebraicGeometry.Scheme.DerivedSections
