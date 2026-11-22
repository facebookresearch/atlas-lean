/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamily

/-!
# Whole original family recognition of the fixed-front insertion

The distinguished simplex is the actual enriched simplex constructed
from its original last-interval maps. The proof retains every original
vertex and uses the proved whole front identities, target diagonal
identity and empty reverse intervals. No comparison outcome is input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontFamilyRecognition
open SimplicialEnrichment FixedFrontCollapse FixedFrontInsertion FixedFrontCubeMap

/-- The genuine family of original distinguished last-interval maps. -/
def family (n : ℕ) : HomFrontFamily.Family (C := realization (FixedFrontCollapse.object.{u} n)) (source n)
    (target n) n where
  map := intervalMap n
  map_comp := interval_union n

private theorem whole_ext {A B : Carrier.{u}} (F G : A ⟶ B)
    (ho : ∀ a, F.obj a = G.obj a) (hm : ∀ a b, F.map a b ≍ G.map a b) : F = G := by
  refine EnrichedFunctor.ext SSet.{u} ho ?_
  intro a b
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hm a b))

/-- The distinguished original insertion is exactly the genuine whole enriched simplex built from its actual
  last-interval family. -/
theorem functor_eq (n : ℕ) : FixedFrontInsertion.functor.{u} n =
    HomFrontFamily.simplex (C := realization (FixedFrontCollapse.object.{u} n)) (source n) (target n) (family n) := by
  let F := FixedFrontInsertion.functor.{u} n
  let G := HomFrontFamily.simplex (C := realization (FixedFrontCollapse.object.{u} n)) (source n) (target n) (family n)
  have ho : ∀ a : coherentSimplex.{u} ⦋n + 1⦌, F.obj a = G.obj a := by
    rintro ⟨⟨a⟩⟩
    cases a using Fin.lastCases with
    | last => exact (last_obj n).trans (HomFrontFamily.simplex_last (C := realization
      (FixedFrontCollapse.object.{u} n)) _ _ _).symm
    | cast i => exact (front_obj n i).trans (HomFrontFamily.simplex_front (C := realization
      (FixedFrontCollapse.object.{u} n)) _ _ _ i).symm
  apply whole_ext F G ho
  rintro ⟨⟨a⟩⟩ ⟨⟨b⟩⟩
  cases a using Fin.lastCases with
  | last =>
    cases b using Fin.lastCases with
    | last =>
      have hF := FixedFrontHomUnits.last_hom.{u} n
      have hG := HomFrontFamily.homMap_last_last (C := realization (FixedFrontCollapse.object.{u} n))
        (source n) (target n) (family n)
      exact (comp_eqToHom_heq _ _).symm.trans
        ((heq_of_eq (hF.trans hG.symm)).trans (comp_eqToHom_heq _ _))
    | cast j =>
      apply (conj_eqToHom_iff_heq _ _ rfl (congrArg₂
        (fun a b : realization (FixedFrontCollapse.object.{u} n) => a ⟶[SSet.{u}] b)
        (ho (.mk (ULift.up (Fin.last (n + 1))))) (ho (.mk (ULift.up j.castSucc))))).mp
      rw [eqToHom_refl, Category.id_comp]
      apply HomUnitsAndEmpty.empty_hom_ext
        (show ¬(ULift.up.{u} (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2))) ≤ ULift.up j.castSucc
          from not_le.mpr (Fin.castSucc_lt_last j))
  | cast i =>
    cases b using Fin.lastCases with
    | last =>
      have hF : F.map (.mk (ULift.up i.castSucc)) (.mk (ULift.up (Fin.last (n + 1)))) ≫
          EqualityTransport.hom (front_obj n i) (last_obj n) = intervalMap n i := rfl
      have hG := HomFrontFamily.homMap_last (C := realization (FixedFrontCollapse.object.{u} n)) (source n)
        (target n) (family n) i
      exact (comp_eqToHom_heq _ _).symm.trans
        ((heq_of_eq (hF.trans hG.symm)).trans (comp_eqToHom_heq _ _))
    | cast j =>
      have hF := FixedFrontHomUnits.front_hom.{u} n i j
      have hG := HomFrontFamily.homMap_front (C := realization (FixedFrontCollapse.object.{u} n)) (source n)
        (target n) (family n) i j
      exact (comp_eqToHom_heq _ _).symm.trans
        ((heq_of_eq (hF.trans hG.symm)).trans (comp_eqToHom_heq _ _))

end CategoryTheory.CoherentRealization.FixedFrontFamilyRecognition
