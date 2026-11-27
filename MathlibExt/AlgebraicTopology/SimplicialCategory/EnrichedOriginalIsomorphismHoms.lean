/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryAdjunction
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Equivalence

/-!
# Every full original Hom map of a genuine carrier isomorphism is an isomorphism

The canonical scalar functor reads each complete original Hom component.
Its image of the genuine whole enriched isomorphism is a Cat isomorphism,
whose original functor is fully faithful. Every original coefficient map
is therefore bijective, retaining all original objects and operators.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment

/-- A genuine whole original carrier isomorphism retains an isomorphism on every SAME full Hom. -/
theorem originalIso_hom_isIso {C D : Carrier.{u}} (e : C ≅ D) (x y : C) : IsIso (e.hom.map
  x y) := by
  have hq (q : SimplexCategoryᵒᵖ) : IsIso ((e.hom.map x y).app q) := by
    let E := Cat.equivOfIso ((ScalarCategoryAdjunction.scalar q).mapIso e)
    have h := E.fullyFaithfulFunctor.map_bijective (⟨x⟩ : SSet.ScalarObject C q)
      (⟨y⟩ : SSet.ScalarObject C q)
    exact (isIso_iff_bijective _).mpr h
  let _ : ∀ q, IsIso ((e.hom.map x y).app q) := hq
  exact NatIso.isIso_of_isIso_app _

/-- The SAME full original Hom map is invertible from the actual whole original functor inverse. -/
theorem originalMap_hom_isIso {C D : Carrier.{u}} (F : C ⟶ D) [IsIso F] (x y : C) : IsIso
  (F.map x y) :=
  originalIso_hom_isIso (asIso F) x y

end CategoryTheory.SimplicialEnrichment
