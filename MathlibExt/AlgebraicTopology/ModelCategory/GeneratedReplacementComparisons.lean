/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements

/-!
# Natural weak comparison zigzags between original generated choices

The two generation cardinals, cell universes and original ordinal bottoms
may be independent. Composing the actual Q or R functors gives cofibrant or
fibrant centers. Both weak natural comparison maps and their compatibility
with the original counits/units are derived from the same original maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w₁ w₂ uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedFunctorialReplacements

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ₁ : Cardinal.{w₁}} [Fact κ₁.IsRegular] [OrderBot κ₁.ord.ToType]
  {κ₂ : Cardinal.{w₂}} [Fact κ₂.IsRegular] [OrderBot κ₂.ord.ToType]
  (d : CofibrantGenerationData C κ₁) (e : CofibrantGenerationData C κ₂)

/-- The actual second Q counit gives the left map of the natural weak comparison span. -/
def qComparisonLeft : Q d ⋙ Q e ⟶ Q d :=
  Functor.whiskerLeft (Q d) (counit e) ≫ (Q d).rightUnitor.hom

/-- The actual second Q functor on the first counit gives the right map of the same span. -/
def qComparisonRight : Q d ⋙ Q e ⟶ Q e :=
  Functor.whiskerRight (counit d) (Q e) ≫ (Q e).leftUnitor.hom

/-- Every left Q comparison component is the original second generated counit at the first
replacement. -/
theorem Q_comparison_left_app (X : C) :
    (qComparisonLeft d e).app X = (counit e).app ((Q d).obj X) := by
  change (counit e).app ((Q d).obj X) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Every right Q comparison component is the original second generated functor on the first counit.
-/
theorem Q_comparison_right_app (X : C) :
    (qComparisonRight d e).app X = (Q e).map ((counit d).app X) := by
  change (Q e).map ((counit d).app X) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The complete left Q comparison is weak at every original input object. -/
theorem Q_comparison_left_weak (X : C) : weakEquivalences C ((qComparisonLeft d e).app X) := by
  rw [Q_comparison_left_app]
  exact counit_weak e ((Q d).obj X)

/-- The complete right Q comparison is weak by the same original counit and derived Q preservation.
-/
theorem Q_comparison_right_weak (X : C) : weakEquivalences C ((qComparisonRight d e).app X) := by
  rw [Q_comparison_right_app]
  exact Q_map_weak e ((counit d).app X) (counit_weak d X)

/-- Both Q comparison arrows are compatible with the complete original weak counits. -/
theorem Q_comparison_counits :
    qComparisonLeft d e ≫ counit d = qComparisonRight d e ≫ counit e := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, Q_comparison_left_app, Q_comparison_right_app]
  exact ((counit e).naturality ((counit d).app X)).symm

/-- The actual comparison center is cofibrant at every object for both generated choices. -/
theorem Q_comparison_center_isCofibrant (X : C) : IsCofibrant ((Q d ⋙ Q e).obj X) :=
  Q_isCofibrant e ((Q d).obj X)

/-- Every original morphism is compatible with the full left weak Q comparison. -/
theorem Q_comparison_left_naturality {X Y : C} (f : X ⟶ Y) :
    (Q d ⋙ Q e).map f ≫ (qComparisonLeft d e).app Y =
      (qComparisonLeft d e).app X ≫ (Q d).map f := (qComparisonLeft d e).naturality f

/-- Every original morphism is compatible with the full right weak Q comparison. -/
theorem Q_comparison_right_naturality {X Y : C} (f : X ⟶ Y) :
    (Q d ⋙ Q e).map f ≫ (qComparisonRight d e).app Y =
      (qComparisonRight d e).app X ≫ (Q e).map f := (qComparisonRight d e).naturality f

/-- The actual second R unit gives the left arrow into the natural fibrant comparison center. -/
def rComparisonLeft : R d ⟶ R d ⋙ R e :=
  (R d).rightUnitor.inv ≫ Functor.whiskerLeft (R d) (unit e)

/-- The actual second R functor on the first unit gives the right arrow into the same center. -/
def rComparisonRight : R e ⟶ R d ⋙ R e :=
  (R e).leftUnitor.inv ≫ Functor.whiskerRight (unit d) (R e)

/-- Every left R comparison component is the original second generated unit at the first
replacement. -/
theorem R_comparison_left_app (X : C) :
    (rComparisonLeft d e).app X = (unit e).app ((R d).obj X) := by
  change 𝟙 _ ≫ (unit e).app ((R d).obj X) = _
  exact Category.id_comp _

/-- Every right R comparison component is the original second generated functor on the first unit.
-/
theorem R_comparison_right_app (X : C) :
    (rComparisonRight d e).app X = (R e).map ((unit d).app X) := by
  change 𝟙 _ ≫ (R e).map ((unit d).app X) = _
  exact Category.id_comp _

/-- The complete left R comparison is weak at every original input object. -/
theorem R_comparison_left_weak (X : C) : weakEquivalences C ((rComparisonLeft d e).app X) := by
  rw [R_comparison_left_app]
  exact unit_weak e ((R d).obj X)

/-- The complete right R comparison is weak by the same original unit and derived R preservation. -/
theorem R_comparison_right_weak (X : C) : weakEquivalences C ((rComparisonRight d e).app X) := by
  rw [R_comparison_right_app]
  exact R_map_weak e ((unit d).app X) (unit_weak d X)

/-- Both R comparison arrows are compatible with the complete original weak units. -/
theorem R_comparison_units :
    unit d ≫ rComparisonLeft d e = unit e ≫ rComparisonRight d e := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, R_comparison_left_app, R_comparison_right_app]
  exact (unit e).naturality ((unit d).app X)

/-- The actual comparison center is fibrant at every object for both generated choices. -/
theorem R_comparison_center_isFibrant (X : C) : IsFibrant ((R d ⋙ R e).obj X) :=
  R_isFibrant e ((R d).obj X)

/-- Every original morphism is compatible with the full left weak R comparison. -/
theorem R_comparison_left_naturality {X Y : C} (f : X ⟶ Y) :
    (R d).map f ≫ (rComparisonLeft d e).app Y =
      (rComparisonLeft d e).app X ≫ (R d ⋙ R e).map f := (rComparisonLeft d e).naturality f

/-- Every original morphism is compatible with the full right weak R comparison. -/
theorem R_comparison_right_naturality {X Y : C} (f : X ⟶ Y) :
    (R e).map f ≫ (rComparisonRight d e).app Y =
      (rComparisonRight d e).app X ≫ (R d ⋙ R e).map f := (rComparisonRight d e).naturality f

end HomotopicalAlgebra.GeneratedFunctorialReplacements
