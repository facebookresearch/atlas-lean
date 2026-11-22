/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# The SAME completed scalar category and its actual native groupoid

The full original-object completion enrichment has each scalar Hom
literally the native FreeGroupoid Hom at the same original endpoints.
The complete inverse scalar functors retain those original Homs and
all operators. The original scalar unit is the SAME native category
unit after this exact coordinate equivalence.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
variable (C : Carrier.{u})

/-- Read the SAME original completed scalar object and every native completed Hom literally. -/
def toNativeScalar (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject (object C) q ⥤ category C q where
  obj x := vertex C q x.obj
  map a := a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every actual native completed object is the SAME original object with its scalar wrapper restored. -/
def fromNativeScalar (q : SimplexCategoryᵒᵖ) : category C q ⥤ SSet.ScalarObject (object C) q where
  obj x := SSet.ScalarObject.mk x.as.as.obj
  map a := a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both full original scalar coordinate functors recover every original completed scalar object and Hom. -/
theorem toNativeScalar_fromNative (q : SimplexCategoryᵒᵖ) :
    toNativeScalar C q ⋙ fromNativeScalar C q = 𝟭 (SSet.ScalarObject (object C) q) :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- Both full native scalar coordinate functors recover every original native groupoid object and Hom. -/
theorem fromNativeScalar_toNative (q : SimplexCategoryᵒᵖ) :
    fromNativeScalar C q ⋙ toNativeScalar C q = 𝟭 (category C q) :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The SAME complete original scalar category is equivalent to its actual native groupoid coordinates. -/
def nativeScalarEquivalence (q : SimplexCategoryᵒᵖ) : SSet.ScalarObject (object C) q ≌ category C q :=
  CategoryTheory.Equivalence.mk (toNativeScalar C q) (fromNativeScalar C q)
    (eqToIso (toNativeScalar_fromNative C q).symm) (eqToIso (fromNativeScalar_toNative C q))

/-- Every actual original completion-unit scalar map is the SAME native category unit. -/
theorem unit_scalar_toNative (q : SimplexCategoryᵒᵖ) :
    SSet.scalarFunctor (unit C) q ⋙ toNativeScalar C q = scalarUnit C q := rfl

/-- The entire original completed scalar operator retains the SAME native completion operator. -/
theorem operator_toNative {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    SSet.scalarOperator (C := object C) f ⋙ toNativeScalar C r =
      toNativeScalar C q ⋙ operator C f := rfl

/-- Each SAME full original scalar coordinate map induces genuine nerve weakness. -/
theorem toNativeScalar_nerve_weak (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (nerveMap (toNativeScalar C q)) := by
  let _ : (toNativeScalar C q).IsEquivalence := (nativeScalarEquivalence C q).isEquivalence_functor
  exact CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence _

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
