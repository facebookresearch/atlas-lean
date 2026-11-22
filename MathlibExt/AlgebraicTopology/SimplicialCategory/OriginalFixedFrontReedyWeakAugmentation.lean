/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontAugmentationWeak

/-!
# The same original Reedy replacement augmentation is degreewise categorical weak

The actual generated right factor is pointwise weak in the original
opposite Reedy model. Its same unop components retain the original
pointed Joyal weak class. The exact original factorization and
constant-front augmentation then prove weakness of the actual generated
projection in every degree.
-/

noncomputable section

universe u

open CategoryTheory Opposite HomotopicalAlgebra MorphismProperty
open scoped Simplicial CategoryTheory.SimplicialObject.reedyModelCategory

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- Every same original generated replacement-map component is weak in the actual named pointed Joyal model. -/
theorem reedyReplacementMap_app_weak (n : SimplexCategory) :
    WeakEquivalence (reedyReplacementMap.{u}.app n) := by
  have hp := reversedFactorization.{u}.hp.2 (op n)
  have hop : WeakEquivalence (reversedFactorization.{u}.p.app (op n)) := (weakEquivalence_iff _).mpr hp
  exact (weakEquivalences_unop_iff _).mpr hop

/-- Every same actual replacement-map component retains its original underlying categorical weak map. -/
theorem reedyReplacementMap_app_categorical (n : SimplexCategory) :
    SSet.categoricalEquivalences (JoyalSSet.forget.map (reedyReplacementMap.{u}.app n).right) := by
  have hu := (weakEquivalences_under_iff _ _).mp (reedyReplacementMap_app_weak n)
  have h := (weakEquivalence_iff _).mp hu
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
  rw [JoyalSSet.modelCategory_weakEquivalences] at h
  exact h

/-- Every same original generated projection to the actual zero quotient is categorical weak. -/
theorem reedyReplacementProjection_app_categorical (n : SimplexCategory) :
    SSet.categoricalEquivalences (JoyalSSet.forget.map (reedyReplacementProjection.{u}.app n).right) := by
  let p := JoyalSSet.forget.map (reedyReplacementMap.{u}.app n).right
  let q := JoyalSSet.forget.map (reedyReplacementProjection.{u}.app n).right
  have hf : p ≫ q = toZero n.len := by
    have h := congrArg (fun t => JoyalSSet.forget.map t.right) (congr_app reedyReplacement_factor n)
    exact (JoyalSSet.forget.map_comp _ _).symm.trans h
  exact SSet.categoricalEquivalences.of_precomp p q
    (reedyReplacementMap_app_categorical n) (hf.symm ▸ toZero_categoricalEquivalence n.len)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
