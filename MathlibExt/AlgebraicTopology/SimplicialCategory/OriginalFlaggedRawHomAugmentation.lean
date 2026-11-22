/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedRawHomSourceNaturality

/-!
# The full original flagged diagonal augments weakly to the SAME raw Hom

The complete original diagonal component projection followed by the
actual original evaluation inverse is a weak map for every simplicial
input. Every entire diagonal chain reads its original first necklace,
complete coefficient lift and input map in the SAME raw quotient.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

/-- The full original flagged diagonal evaluates in its SAME original raw coherent Hom. -/
def rawAugmentation (K : SSet.{u}) (x y : K _⦋0⦌) : diagonal K x y ⟶ hom K x y :=
  diagonalProjection K x y ≫ rawEvaluationMap K x y

/-- The SAME entire original flagged diagonal augments weakly to the actual original raw Hom. -/
theorem rawAugmentation_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (rawAugmentation K x y) :=
  RespectsIso.postcomp SSet.realizationWeakEquivalences (rawHomIso K x y).inv
    (diagonalProjection K x y) (diagonalProjection_weak K x y)

/-- Every SAME full diagonal chain reads its original full coefficient lift and entire input map. -/
theorem rawAugmentation_app (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (X : (nerve (Object K x y q)).obj q) :
    (rawAugmentation K x y).app q X = evaluation (X.obj 0) := rfl

/-- The actual original raw diagonal augmentation retains the SAME full component projection. -/
theorem rawAugmentation_rawHomMap (K : SSet.{u}) (x y : K _⦋0⦌) :
    rawAugmentation K x y ≫ rawHomMap K x y = diagonalProjection K x y :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun e => diagonalProjection K x y ≫ e) (rawEvaluationMap_rawHomMap K x y)).trans
      (Category.comp_id _))

/-- The complete original raw diagonal augmentation is natural for EVERY original source simplicial map. -/
theorem rawAugmentation_source {K L : SSet.{u}} (f : K ⟶ L) (x y : K _⦋0⦌) :
    diagonalSourceMap f x y ≫ rawAugmentation L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      rawAugmentation K x y ≫ (CoherentRealization.realizationMap f).map x y := by
  change _ = (diagonalProjection K x y ≫ rawEvaluationMap K x y) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≫ rawEvaluationMap L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y))
      (diagonalProjection_source f x y)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun e => diagonalProjection K x y ≫ e) (rawEvaluationMap_source f x y).symm).trans
            (Category.assoc _ _ _).symm)))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
