/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceFlankingFunctor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Genuine nerve weakness of original flanking

The actual original flanking functor lifts through the native full
subcategory of flanked objects. The two original inclusion natural
transformations give actual simplicial nerve homotopies. Both same nerve
maps are realization weak equivalences.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking

/-- The exact original first-joint and last-vertex property. -/
def property (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    ObjectProperty (Object K x y q) := IsFlanked

/-- The native full subcategory of the actual original flanked objects. -/
abbrev Flanked (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :=
  (property K x y q).FullSubcategory

/-- The same original full-subcategory inclusion. -/
def inclusionFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Flanked K x y q ⥤ Object K x y q := (property K x y q).ι

/-- The whole original flanking functor with its genuinely proved target property. -/
def toFlanked (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ Flanked K x y q :=
  (property K x y q).lift (functor K x y q) functor_obj_isFlanked

/-- The same whole original inclusion on the original flagged-necklace category. -/
def fullInclusion (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    toFlanked K x y q ⋙ inclusionFunctor K x y q ⟶ 𝟭 (Object K x y q) :=
  inclusionTransformation K x y q

/-- The same inclusion also lives in the full original flanked subcategory. -/
def flankedInclusion (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    inclusionFunctor K x y q ⋙ toFlanked K x y q ⟶ 𝟭 (Flanked K x y q) where
  app T := ObjectProperty.homMk (inclusion T.obj)
  naturality _T _U f := by
    apply ObjectProperty.hom_ext
    exact inclusion_naturality f.hom

/-- The same full-subcategory nerve inclusion. -/
def inclusionNerveMap (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Flanked K x y q) ⟶ nerve (Object K x y q) :=
  nerveMap (inclusionFunctor K x y q)

/-- The same whole original flanking map on nerves. -/
def flankingNerveMap (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Object K x y q) ⟶ nerve (Flanked K x y q) :=
  nerveMap (toFlanked K x y q)

/-- The original composite contracts by the original inclusion inside the flanked category. -/
def flankedHomotopy (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.Homotopy (inclusionNerveMap K x y q ≫ flankingNerveMap K x y q)
      (𝟙 (nerve (Flanked K x y q))) := by
  simpa only [inclusionNerveMap, flankingNerveMap, nerveMap_comp, nerveMap_id] using
    NatTrans.nerveHomotopy (flankedInclusion K x y q)

/-- The original composite contracts by the original full native inclusion. -/
def fullHomotopy (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.Homotopy (flankingNerveMap K x y q ≫ inclusionNerveMap K x y q)
      (𝟙 (nerve (Object K x y q))) := by
  simpa only [inclusionNerveMap, flankingNerveMap, nerveMap_comp, nerveMap_id] using
    NatTrans.nerveHomotopy (fullInclusion K x y q)

/-- The actual original nerve maps give a genuine equivalence of the realized spaces. -/
def realizedComparison (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (Flanked K x y q)))
      (SSet.toTop.obj (nerve (Object K x y q))) :=
  SSet.realizedHomotopyEquiv _ _ (inclusionNerveMap K x y q) (flankingNerveMap K x y q)
    (flankedHomotopy K x y q) (fullHomotopy K x y q)

/-- The same original inclusion is genuinely weak, for every input and every scalar degree. -/
theorem inclusionNerveMap_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (inclusionNerveMap K x y q) := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (inclusionNerveMap K x y q))
  exact TopCat.mem_of_eq_toFun (realizedComparison K x y q) rfl

/-- The same actual original flanking map is genuinely weak. -/
theorem flankingNerveMap_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (flankingNerveMap K x y q) := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (flankingNerveMap K x y q))
  exact TopCat.mem_of_eq_toFun (realizedComparison K x y q).symm rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking
