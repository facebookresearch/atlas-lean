/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorUniversal
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorReplacementIso
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorReplacementMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorDerivedMappingSpaces

/-!
# The actual first-JT one-fold functor-category presentation

The CSS internal functor object is sent through the original first-JT right
functor. Its canonical closed comparison lands in the native Joyal carrier
of the actual scalar power. Genuine completeness proves both objects
fibrant and their specified comparison weak in the original chosen model.
The core interpretation keeps the same original Q/R-derived end.
-/

noncomputable section
universe u

open CategoryTheory HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen
open SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialSpace.FirstProjection

private local instance sourceLocallySmall : LocallySmall.{u} (CategoryTheory.FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- The actual first-JT presentation of the whole CSS internal functor object. -/
def cssFunctorCategory (W V : SimplicialSpace.{u}) : JoyalSSet.{u} :=
  comparisonRight.obj ((ihom W).obj V)

/-- The actual native Joyal functor quasicategory on the same right-image carriers. -/
def nativeFunctorCategory (W V : SimplicialSpace.{u}) : JoyalSSet.{u} :=
  JoyalSSet.ofSSet.obj ((ihom (right.obj W)).obj (right.obj V))

/-- The specified comparison on the original Joyal model carriers. -/
def functorCategoryComparison (W V : SimplicialSpace.{u}) :
    cssFunctorCategory W V ⟶ nativeFunctorCategory W V :=
  JoyalSSet.ofSSet.map (comparison W V)

/-- Forgetting the carrier wrapper retains the literal original exponential comparison. -/
theorem functorCategoryComparison_underlying (W V : SimplicialSpace.{u}) :
    JoyalSSet.forget.map (functorCategoryComparison W V) = comparison W V := rfl

/-- The CSS functor-category presentation is fibrant in the actual chosen Joyal model. -/
theorem cssFunctorCategory_isFibrant (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    IsFibrant (cssFunctorCategory W V) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  exact (JoyalSSet.isFibrant_iff_quasicategory _).mpr (comparison_source_quasicategory W V hV)

/-- The target is the actual native fibrant Joyal functor object at every complete CSS target. -/
theorem nativeFunctorCategory_isFibrant (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    IsFibrant (nativeFunctorCategory W V) := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  exact (JoyalSSet.isFibrant_iff_quasicategory _).mpr (comparison_target_quasicategory W V hV)

/-- The actual functor-category comparison is weak in that same original Joyal model. -/
theorem functorCategoryComparison_weak (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    JoyalSSet.modelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences (functorCategoryComparison W V) := by
  rw [JoyalSSet.modelCategory_weakEquivalences]
  exact comparison_categoricalEquivalence W V hW hV

/-- Its evaluation mate is exactly the original product Iso and the original CSS evaluation. -/
theorem functorCategoryComparison_evaluation (W V : SimplicialSpace.{u}) :
    MonoidalClosed.uncurry (JoyalSSet.forget.map (functorCategoryComparison W V)) =
      (rightProductIso W ((ihom W).obj V)).inv ≫ right.map ((ihom.ev W).app V) :=
  comparison_evaluation W V

/-- The actual Joyal functor core classifies the same checked original-zero/Q/R end. -/
def functorCategoryCoreMappingIso (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.realizationWeakEquivalences.{u}.Q.obj (SSet.coreFunctor.obj (nativeFunctorCategory W V).toSSet) ≅
      SSet.realizationWeakEquivalences.{u}.Q.obj
        (((localDerivedEnd (SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1)).obj
          (op (originalImage W))).obj (originalImage V)) :=
  functorCoreMappingIso W V hW hV

end SimplicialSpace.FirstProjection
