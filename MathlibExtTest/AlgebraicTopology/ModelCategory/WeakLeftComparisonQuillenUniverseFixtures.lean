/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenWeakLeftComparison

noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory HomotopicalAlgebra

namespace WeakLeftComparisonQuillenUniverseFixtures

/-- Independent source/target and Hom universes retain the original weak natural comparison and actual cofibration
input. -/
theorem original_weak_comparison_quillen
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [Adjunction.IsQuillenAdjunction adj₂]
    (α : L₁ ⟶ L₂) (hα : ∀ X : C, WeakEquivalence (α.app X))
    (hL : PreservesCofibrations L₁) : Adjunction.IsQuillenAdjunction adj₁ :=
  Adjunction.IsQuillenAdjunction.of_weak_left_comparison adj₁ adj₂ α hα hL

end WeakLeftComparisonQuillenUniverseFixtures
