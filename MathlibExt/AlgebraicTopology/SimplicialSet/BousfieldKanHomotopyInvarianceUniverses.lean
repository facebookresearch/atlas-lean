/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvariance
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakCoproductUniverses

/-!
# Actual Bousfield--Kan weak invariance at independent native universes

For arbitrary original index object and Hom universes, each full native
weighted-bar row is its actual coproduct of coefficient maps. Genuine
coproduct weak stability and the original diagonal theorem prove weak
invariance of the SAME full Bousfield--Kan map. The larger coefficient
universe uses the existing original bkHocolimMapOf carrier and maps.
-/

@[expose] public section


noncomputable section
universe uJ vJ w
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace SSet

/-- Every original native weighted-bar row is weak when all SAME original coefficient maps are weak. -/
theorem bkHocolimMap_row_weak_universes
    {J : Type uJ} [Category.{vJ} J] {D E : J ⥤ SSet.{max uJ vJ w}}
    (α : D ⟶ E) (hα : ∀ j, realizationWeakEquivalences (α.app j)) (n : ℕ) :
    realizationWeakEquivalences
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF (CategoryBar.replUnit J) α).app (op ⦋n⦌)) := by
  let I : Type (max uJ vJ) := StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n
  let X : I → SSet.{max uJ vJ w} := fun p => D.obj p.1.left
  let Y : I → SSet.{max uJ vJ w} := fun p => E.obj p.1.left
  let f : ∀ p : I, X p ⟶ Y p := fun p => α.app p.1.left
  have hf : ∀ p : I, realizationWeakEquivalences (f p) := fun p => hα p.1.left
  have hsum : realizationWeakEquivalences (Limits.Sigma.map f) :=
    sigma_map_weak_universes (I := I) (X := X) (Y := Y) f hf
  have he : (StrictOrdinaryWeightedBar.wbarSimplicialMapF (CategoryBar.replUnit J) α).app (op ⦋n⦌) =
      Limits.Sigma.map f :=
    StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk (CategoryBar.replUnit J) α n
  exact he ▸ hsum

/-- The SAME original full larger-universe Bousfield--Kan map is weak from its actual coefficient maps. -/
theorem bkHocolimMapOf_weak_universes
    {J : Type uJ} [Category.{vJ} J] {D E : J ⥤ SSet.{max uJ vJ w}}
    (α : D ⟶ E) (hα : ∀ j, realizationWeakEquivalences (α.app j)) :
    realizationWeakEquivalences (bkHocolimMapOf.{uJ, vJ, w} α) := by
  apply simplicialDiagonal_map_mem_realizationWeakEquivalences
  intro n
  exact bkHocolimMap_row_weak_universes α hα n

/-- The SAME original inferable Bousfield--Kan map is weak at arbitrary original index Hom levels. -/
theorem bkHocolimMap_weak_universes
    {J : Type uJ} [Category.{vJ} J] {D E : J ⥤ SSet.{max uJ vJ}}
    (α : D ⟶ E) (hα : ∀ j, realizationWeakEquivalences (α.app j)) :
    realizationWeakEquivalences (bkHocolimMap α) :=
  bkHocolimMapOf_weak_universes.{uJ, vJ, 0} α hα

end SSet
