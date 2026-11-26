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
# Base change of small étale sites

For a morphism f : X → Y of schemes in universe u, base change gives
G_f : Etale(Y) → Etale(X), sending U → Y to X ×_Y U → X.
This functor preserves finite limits. It has the canonical comparisons
G_id ≅ id and G_(g∘f) ≅ G_f ∘ G_g, which identify the corresponding
single and iterated fiber products.

Milne, Lectures on Étale Cohomology, §8, p. 58, Lemma 8.1, gives the
base-change argument for fiber products and étale covering families.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.Scheme.DerivedSections

set_option backward.isDefEq.respectTransparency.types false in
/-- For a morphism f : X → Y of schemes in universe u, this is the
functor Etale(Y) → Etale(X) sending an étale Y-scheme U to X ×_Y U,
and sending an étale-over-Y morphism to its base change. -/
abbrev smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale.{u}) ⊤ f

set_option backward.isDefEq.respectTransparency.types false in
/-- For a scheme X, base change along id_X is naturally isomorphic
to the identity functor of Etale(X). On an étale X-scheme U, the comparison
is the canonical identification X ×_X U ≅ U. -/
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
/-- For scheme morphisms f : X → Y and g : Y → Z, base change
along g ∘ f is naturally isomorphic to first base changing along g
and then along f. On U ∈ Etale(Z), this identifies
X ×_Z U with X ×_Y (Y ×_Z U). -/
def smallEtaleBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleBaseChange (f ≫ g) ≅ smallEtaleBaseChange g ⋙ smallEtaleBaseChange f :=
  MorphismProperty.Over.pullbackComp
    (P := @AlgebraicGeometry.Etale.{u}) (Q := ⊤) f g

set_option backward.isDefEq.respectTransparency.types false in
/-- For every morphism f : X → Y of schemes in universe u,
the functor Etale(Y) → Etale(X), U ↦ X ×_Y U, preserves finite limits.
Thus terminal étale objects and finite fiber-product diagrams are preserved. -/
theorem smallEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleBaseChange f) := by
  exact inferInstanceAs
    (PreservesFiniteLimits
      (MorphismProperty.Over.pullback (@AlgebraicGeometry.Etale.{u}) ⊤ f))

end AlgebraicGeometry.Scheme.DerivedSections
