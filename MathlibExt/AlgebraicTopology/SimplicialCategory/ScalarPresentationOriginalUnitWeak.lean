/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePresentationCompletionUnitWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionCategoryEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarNerveDiagrams
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionFixedFunctor
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidEquivalence

/-!
# The actual original unit from a constructed scalar free presentation

The genuine fixed-label scalar equivalence retains every original Hom
simplex and object. Completing that actual equivalence keeps the full
native unit square. A constructed full free presentation therefore
proves weakness of the SAME original enriched unit's scalar nerve.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects
open ScalarGroupoidCompletion RelativeWords
variable {O : Type u} (C : FixedObjects O) (q : SimplexCategoryᵒᵖ)

/-- The actual original native scalar category unit is weak from the full constructed scalar presentation. -/
theorem scalarNativeUnit_weak (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    SSet.realizationWeakEquivalences (nerveMap (FreeGroupoid.of (SSet.ScalarObject C.val q))) := by
  let E := labelsScalarEquivalence C q
  let CE := FreeGroupoid.mapEquivalence E
  let _ : (FreeGroupoid.map E.functor).IsEquivalence := CE.isEquivalence_functor
  have hE := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence E.functor
  have hCE := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (FreeGroupoid.map E.functor)
  have hP := P.unit_nerve_weak
  have hsquare : nerveMap E.functor ≫ nerveMap (FreeGroupoid.of (SSet.ScalarObject C.val q)) =
      nerveMap (FreeGroupoid.of (scalarCat C q)) ≫ nerveMap (FreeGroupoid.map E.functor) := by
    ext d w
    rfl
  exact SSet.realizationWeakEquivalences.of_precomp (nerveMap E.functor) _ hE
    (hsquare.symm ▸ SSet.realizationWeakEquivalences.comp_mem _ _ hP hCE)

/-- The SAME full original enriched unit has weak scalar nerve from its actual constructed presentation. -/
theorem originalUnit_scalar_weak (P : FreePresentation.{u,u,u} (scalarCategory C q)) :
    SSet.realizationWeakEquivalences (nerveMap (SSet.scalarFunctor (unit C.val) q)) := by
  have hcoord := toNativeScalar_nerve_weak C.val q
  have hsquare : nerveMap (SSet.scalarFunctor (unit C.val) q) ≫ nerveMap (toNativeScalar C.val q) =
      nerveMap (scalarUnit C.val q) := by
    ext d w
    rfl
  exact SSet.realizationWeakEquivalences.of_postcomp _ _ hcoord
    (hsquare.symm ▸ scalarNativeUnit_weak C q P)

end CategoryTheory.SimplicialEnrichment.FixedObjects
