/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectSequentialSourcePushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFilteredColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Genuine weak source comparison on the SAME full sequential boundary-cell colimit

The two actual original sequential diagrams retain every whole stage,
cell occurrence and original pushout projection. All their full Hom
transition maps are monic. The native underlying and source-pushout
functors preserve the SAME whole enriched colimits, and Hom evaluation
preserves those actual filtered colimits. The original sequential-mono
theorem proves weakness of the SAME terminal pushout inclusion.
-/

noncomputable section
universe u v w
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.SequentialSourcePushout
variable {O : Type u} {C D : FixedObjects O} (U : ℕ ⥤ Under C) (F : C ⟶ D)

private theorem map_property_of_successors {T : Type v} [Category.{w} T]
    (V : ℕ ⥤ T) (W : MorphismProperty T) [W.ContainsIdentities] [W.IsStableUnderComposition]
    (h : ∀ (n : ℕ), W (V.map (homOfLE (n.le_add_right 1)))) {i j : ℕ} (g : i ⟶ j) :
    W (V.map g) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom g)
  subst j
  induction k with
  | zero =>
    have hg : g = 𝟙 i := Subsingleton.elim _ _
    rw [hg, V.map_id]
    exact W.id_mem _
  | succ k ih =>
    have hg : g = homOfLE (Nat.le_add_right i k) ≫ homOfLE ((i+k).le_add_right 1) :=
      Subsingleton.elim _ _
    rw [hg, V.map_comp]
    exact W.comp_mem _ _ (ih _) (h (i+k))

/-- Every full original source Hom transition is monic from its SAME boundary-cell successor maps. -/
theorem source_homMap_mono (a : ∀ (n : ℕ), AttachCells.{u} (boundaryFamily O).homFamily
    ((source U).map (homOfLE (n.le_add_right 1)))) (x y : O) {i j : ℕ} (g : i ⟶ j) :
    Mono (homMap ((source U).map g) x y) :=
  map_property_of_successors (source U ⋙ evaluation x y) (MorphismProperty.monomorphisms _)
    (fun n => FreeBoundaryCells.leftHom_mono (a n) x y) g

/-- Every full original pushed Hom transition is monic on its SAME retained boundary-cell occurrences. -/
theorem changed_homMap_mono (a : ∀ (n : ℕ), AttachCells.{u} (boundaryFamily O).homFamily
    ((source U).map (homOfLE (n.le_add_right 1)))) (x y : O) {i j : ℕ} (g : i ⟶ j) :
    Mono (homMap ((changed U F).map g) x y) :=
  map_property_of_successors (changed U F ⋙ evaluation x y) (MorphismProperty.monomorphisms _)
    (fun n => FreeBoundaryCells.leftHom_mono (changedCells U F a n) x y) g

/-- The full terminal source pushout retains the SAME original enriched colimit and all original maps. -/
theorem terminal_comparison_weak [IsIso (U.obj 0).hom]
    (a : ∀ (n : ℕ), AttachCells.{u} (boundaryFamily O).homFamily
      ((source U).map (homOfLE (n.le_add_right 1))))
    (hF : FixedObjectModel.weakEquivalences O F) (s : Cocone U) (hs : IsColimit s) :
    FixedObjectModel.weakEquivalences O (pushout.inl s.pt.hom F) := by
  let _ : PreservesColimits (Under.pushout F) :=
    (Under.mapPushoutAdj F).leftAdjoint_preservesColimits
  let sC := (Under.forget C).mapCocone s
  let sD := (Under.forget D).mapCocone ((Under.pushout F).mapCocone s)
  have hsC : IsColimit sC := isColimitOfPreserves (Under.forget C) hs
  have hsD : IsColimit sD := isColimitOfPreserves (Under.forget D)
    (isColimitOfPreserves (Under.pushout F) hs)
  apply (FixedObjectModel.weakEquivalences_iff _).mpr
  intro x y
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    (Functor.whiskerRight (comparison U F) (evaluation x y))
    (isColimitOfPreserves (evaluation x y) hsC)
    (isColimitOfPreserves (evaluation x y) hsD) (homMap (pushout.inl s.pt.hom F) x y)
  · intro n
    have hn : (s.ι.app n).right ≫ pushout.inl s.pt.hom F =
        ((comparison U F).app n) ≫ ((Under.pushout F).map (s.ι.app n)).right := by
      exact (pushout.inl_desc _ _ _).symm
    exact (homMap_comp _ _ x y).symm.trans
      ((congrArg (fun f => homMap f x y) hn).trans (homMap_comp _ _ x y))
  · intro i j g
    exact source_homMap_mono U a x y g
  · intro i j g
    exact changed_homMap_mono U F a x y g
  · intro n
    exact (FixedObjectModel.weakEquivalences_iff _).mp (comparison_weak U F a hF n) x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.SequentialSourcePushout
