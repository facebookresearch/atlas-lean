/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerHornReplacement

/-!
# Inner Horn Replacement Test
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.InnerHornReplacementTest

/-- Both displayed components are the same native terminal-arrow factorization. -/
theorem original_components (X : SSet.{u}) :
    innerHornReplacementUnit.app X =
        innerHornFactorization.i.app (Arrow.mk (terminal.from X)) ∧
      innerHornReplacementProjection.app X =
        innerHornFactorization.p.app (Arrow.mk (terminal.from X)) :=
  ⟨rfl, rfl⟩

/-- Both strict natural squares retain the original arbitrary map and chosen terminal. -/
theorem original_squares {X Y : SSet.{u}} (f : X ⟶ Y) :
    innerHornReplacementUnit.app X ≫ innerHornReplacement.map f =
        f ≫ innerHornReplacementUnit.app Y ∧
      innerHornReplacement.map f ≫ innerHornReplacementProjection.app Y =
        innerHornReplacementProjection.app X ≫ 𝟙 (⊤_ SSet.{u}) :=
  ⟨innerHornReplacementUnit_naturality f,
    innerHornReplacementProjection_naturality f⟩

/-- All three unit classes are genuine predicates on the same original map. -/
theorem original_unit_classes (X : SSet.{u}) :
    innerAnodyneExtensions (innerHornReplacementUnit.app X) ∧
      categoricalEquivalences (innerHornReplacementUnit.app X) ∧
      trivialCofibrations SSet.{u} (innerHornReplacementUnit.app X) ∧
      realizationWeakEquivalences (innerHornReplacementUnit.app X) :=
  ⟨innerHornReplacementUnit_innerAnodyne X,
    innerHornReplacementUnit_categorical X,
    innerHornReplacementUnit_trivialCofibration X,
    innerHornReplacementUnit_realizationWeak X⟩

/-- The full original terminal factor, all inner RLP and actual QC are retained. -/
theorem original_terminal_target (X : SSet.{u}) :
    innerHornReplacementUnit.app X ≫ innerHornReplacementProjection.app X =
        terminal.from X ∧
      innerHornReplacementProjection.app X = terminal.from (innerHornReplacement.obj X) ∧
      innerHornInclusions.rlp (innerHornReplacementProjection.app X) ∧
      Quasicategory (innerHornReplacement.obj X) :=
  ⟨innerHornReplacement_fac X, innerHornReplacementProjection_eq_terminal X,
    innerHornReplacementProjection_rlp X, innerHornReplacement_quasicategory X⟩

/-- General original Ho equivalence needs no original quasicategory premise. -/
theorem original_unit_Ho (X : SSet.{u}) :
    (mapHomotopyCategory (innerHornReplacementUnit.app X)).IsEquivalence :=
  innerHornReplacementUnit_mapHo_isEquivalence X

/-- Only the original Ho groupoid hypothesis supplies the Kan conclusion. -/
theorem original_groupoidal_target (X : SSet.{u}) [IsGroupoid X.HomotopyCategory] :
    IsGroupoid (innerHornReplacement.obj X).HomotopyCategory ∧
      core (innerHornReplacement.obj X) = ⊤ ∧
      KanComplex (innerHornReplacement.obj X) :=
  ⟨innerHornReplacement_isGroupoid_of_isGroupoid X,
    innerHornReplacement_core_eq_top_of_isGroupoid X,
    innerHornReplacement_kanComplex_of_isGroupoid X⟩

/-- The extension keeps both original strict equations. -/
theorem original_extension {X Y : SSet.{u}} (f : X ⟶ Y) [Quasicategory Y] :
    ∃ g : innerHornReplacement.obj X ⟶ Y,
      innerHornReplacementUnit.app X ≫ g = f ∧
      g ≫ terminal.from Y = innerHornReplacementProjection.app X :=
  exists_innerHornReplacement_extension f

end SSet.InnerHornReplacementTest
