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
# Every Hom map of a carrier isomorphism is an isomorphism

The canonical scalar functor reads each complete Hom component.
Its image of the enriched isomorphism is a Cat isomorphism,
whose functor is fully faithful. Every coefficient map
is therefore bijective, retaining all objects and operators.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment

/-- A carrier isomorphism retains an isomorphism on every same Hom. -/
theorem originalIso_hom_isIso {C D : Carrier.{u}} (e : C ≅ D) (x y : C) : IsIso (e.hom.map
  x y) := by
  have hq (q : SimplexCategoryᵒᵖ) : IsIso ((e.hom.map x y).app q) := by
    let E := Cat.equivOfIso ((ScalarCategoryAdjunction.scalar q).mapIso e)
    have h := E.fullyFaithfulFunctor.map_bijective (⟨x⟩ : SSet.ScalarObject C q)
      (⟨y⟩ : SSet.ScalarObject C q)
    exact (isIso_iff_bijective _).mpr h
  let _ : ∀ q, IsIso ((e.hom.map x y).app q) := hq
  exact NatIso.isIso_of_isIso_app _

/-- The same Hom map is invertible from the functor inverse. -/
theorem originalMap_hom_isIso {C D : Carrier.{u}} (F : C ⟶ D) [IsIso F] (x y : C) : IsIso
  (F.map x y) :=
  originalIso_hom_isIso (asIso F) x y

end CategoryTheory.SimplicialEnrichment
