/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalSpaces

/-!
# The genuine all-complete-Segal-space weak class and basic closures
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite
open scoped SimplicialSpace.Inner
namespace SimplicialSpace

/-- Test every complete Segal space in the original fixed universe. -/
def rezkWeakEquivalences : MorphismProperty SimplicialSpace.{u} :=
  fun {X Y} (f : X ⟶ Y) => ∀ Z : SimplicialSpace.{u}, completeSegalSpaces Z →
    SSet.realizationWeakEquivalences ((innerHomFunctor.map f.op).app Z)

-- Private exact representation, not a second public mapping functor or CSS carrier.
private theorem rezkWeakEquivalences_eq_testing :
    rezkWeakEquivalences.{u} =
      ((SSet.realizationWeakEquivalences.{u}.functorCategory
        completeSegalSpaces.FullSubcategory).inverseImage
        (innerHomFunctor ⋙
          (Functor.whiskeringLeft completeSegalSpaces.FullSubcategory
            SimplicialSpace.{u} SSet.{u}).obj completeSegalSpaces.ι)).unop := by
  funext X Y f
  apply propext
  change (∀ Z : SimplicialSpace.{u}, completeSegalSpaces Z →
    SSet.realizationWeakEquivalences ((innerHomFunctor.map f.op).app Z)) ↔
    ∀ Z : completeSegalSpaces.FullSubcategory,
      SSet.realizationWeakEquivalences ((innerHomFunctor.map f.op).app Z.obj)
  constructor
  · intro h Z
    exact h Z.obj Z.property
  · intro h Z hZ
    exact h ⟨Z, hZ⟩

instance rezkWeakEquivalences_isMultiplicative :
    rezkWeakEquivalences.{u}.IsMultiplicative := by
  -- IsMultiplicative is not synthesized merely from its parent classes.
  -- This local constructor combines the two already-proved scalar facts.
  let _ : SSet.realizationWeakEquivalences.{u}.IsMultiplicative :=
    { id_mem := fun X => SSet.realizationWeakEquivalences.id_mem X
      comp_mem := fun f g hf hg =>
        SSet.realizationWeakEquivalences.comp_mem f g hf hg }
  rw [rezkWeakEquivalences_eq_testing]
  infer_instance

instance rezkWeakEquivalences_hasTwoOutOfThreeProperty :
    rezkWeakEquivalences.{u}.HasTwoOutOfThreeProperty := by
  rw [rezkWeakEquivalences_eq_testing]
  infer_instance

instance rezkWeakEquivalences_isStableUnderRetracts :
    rezkWeakEquivalences.{u}.IsStableUnderRetracts := by
  rw [rezkWeakEquivalences_eq_testing]
  infer_instance

instance rezkWeakEquivalences_respectsIso :
    rezkWeakEquivalences.{u}.RespectsIso := by
  rw [rezkWeakEquivalences_eq_testing]
  infer_instance

end SimplicialSpace
