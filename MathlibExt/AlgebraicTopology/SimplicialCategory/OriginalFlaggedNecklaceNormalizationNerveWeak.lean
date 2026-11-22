/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceNormalizationFunctor

/-!
# Genuine original normalization nerve weakness

The SAME original normalization and inclusion maps give an actual
homotopy equivalence of realized nerves. The original unit's direction
is retained; its realized homotopy is reversed only in topological
spaces. Both actual nerve maps are genuine realization weak maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization

open Flanking

/-- The SAME whole original normalization map on actual original nerves. -/
def nerveMap (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Flanked K x y q) ⟶ nerve (Normalized K x y q) := CategoryTheory.nerveMap (functor K x y q)

/-- The SAME full original inclusion map on actual original nerves. -/
def inclusionNerveMap (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Normalized K x y q) ⟶ nerve (Flanked K x y q) := CategoryTheory.nerveMap (inclusion K x y q)

/-- The actual original unit gives the SAME native nerve homotopy in its original direction. -/
def unitHomotopy (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.Homotopy (𝟙 (nerve (Flanked K x y q)))
      (nerveMap K x y q ≫ inclusionNerveMap K x y q) := by
  simpa only [nerveMap, inclusionNerveMap, CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_id] using
    NatTrans.nerveHomotopy (unit K x y q)

/-- The actual original counit gives the SAME native nerve contraction on nondegenerate objects. -/
def counitHomotopy (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.Homotopy (inclusionNerveMap K x y q ≫ nerveMap K x y q)
      (𝟙 (nerve (Normalized K x y q))) := by
  simpa only [nerveMap, inclusionNerveMap, CategoryTheory.nerveMap_comp, CategoryTheory.nerveMap_id] using
    NatTrans.nerveHomotopy (counit K x y q)

/-- BOTH SAME original nerve maps give a genuine homotopy equivalence of their actual realized spaces. -/
def realizedComparison (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (Flanked K x y q))) (SSet.toTop.obj (nerve (Normalized K x y q))) where
  toFun := (SSet.toTop.map (nerveMap K x y q)).hom
  invFun := (SSet.toTop.map (inclusionNerveMap K x y q)).hom
  left_inv := by
    have h := SSet.realizeHomotopy (nerve (Flanked K x y q)) (nerve (Flanked K x y q))
      (𝟙 _) (nerveMap K x y q ≫ inclusionNerveMap K x y q) (unitHomotopy K x y q)
    have h' : ContinuousMap.Homotopy
        ((SSet.toTop.map (inclusionNerveMap K x y q)).hom.comp (SSet.toTop.map (nerveMap K x y q)).hom)
        (ContinuousMap.id _) := by
      simpa only [CategoryTheory.Functor.map_comp, TopCat.hom_comp,
        CategoryTheory.Functor.map_id, TopCat.hom_id] using h.symm
    exact ⟨h'⟩
  right_inv := by
    have h := SSet.realizeHomotopy (nerve (Normalized K x y q)) (nerve (Normalized K x y q))
      (inclusionNerveMap K x y q ≫ nerveMap K x y q) (𝟙 _) (counitHomotopy K x y q)
    have h' : ContinuousMap.Homotopy
        ((SSet.toTop.map (nerveMap K x y q)).hom.comp (SSet.toTop.map (inclusionNerveMap K x y q)).hom)
        (ContinuousMap.id _) := by
      simpa only [CategoryTheory.Functor.map_comp, TopCat.hom_comp,
        CategoryTheory.Functor.map_id, TopCat.hom_id] using h
    exact ⟨h'⟩

/-- The SAME original normalization nerve map is genuinely weak for EVERY input and scalar degree. -/
theorem nerveMap_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (nerveMap K x y q) := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (nerveMap K x y q))
  exact TopCat.mem_of_eq_toFun (realizedComparison K x y q) rfl

/-- The SAME full original inclusion nerve map is genuinely weak for EVERY input and scalar degree. -/
theorem inclusionNerveMap_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (inclusionNerveMap K x y q) := by
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (inclusionNerveMap K x y q))
  exact TopCat.mem_of_eq_toFun (realizedComparison K x y q).symm rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization
