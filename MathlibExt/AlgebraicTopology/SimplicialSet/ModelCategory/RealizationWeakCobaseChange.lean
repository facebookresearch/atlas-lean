/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import MathlibExt.CategoryTheory.MorphismProperty.Limits

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Cobase change for realization weak equivalences

A realization weak equivalence of simplicial sets in any universe remains a
realization weak equivalence after pushout along a simplicial monomorphism.
The proof assembles the exact TopCat model structure only locally, observes
that realizations of simplicial sets are cofibrant in that model, and applies
the cofibrant cube lemma.

This file also packages the point theorem as stability under cobase change
against simplicial monomorphisms. It installs no global TopCat model-category
instance and makes no claim for arbitrary closed embeddings, filtered
colimits, or unrestricted cobase change.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe u

namespace SSet

/-- A realization weak equivalence remains one after pushout along a
simplicial monomorphism. In Mathlib's `IsPushout` orientation, `i` is the
monomorphism, `f` is the weak leg, and `f'` is the resulting weak leg. -/
theorem realizationWeakEquivalences.of_isPushout_mono
    {A B X Y : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Mono i]
    (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences f' := by
  let : ModelCategory TopCat.{u} := TopCat.modelCategory
  have sqTop : IsPushout (toTop.map i) (toTop.map f)
      (toTop.map f') (toTop.map j) :=
    toTop.map_isPushout sq
  let : Cofibration (toTop.map i) := by
    rw [cofibration_iff]
    exact SSet.toTop_map_mem_realizedBoundaryLLP i
  let : WeakEquivalence (toTop.map f) := by
    rw [weakEquivalence_iff]
    change TopCat.weakHomotopyEquivalences (toTop.map f)
    exact hf
  have hCofibrant (Z : SSet.{u}) : IsCofibrant (toTop.obj Z) := by
    let : Cofibration (toTop.map (initial.to Z)) := by
      rw [cofibration_iff]
      exact SSet.toTop_map_mem_realizedBoundaryLLP (initial.to Z)
    have hInit : IsInitial (toTop.obj (⊥_ SSet.{u})) :=
      initialIsInitial.isInitialObj (G := toTop.{u})
    exact (isCofibrant_iff_of_isInitial
      (toTop.map (initial.to Z)) hInit).2 (by infer_instance)
  let : IsCofibrant (toTop.obj A) := hCofibrant A
  let : IsCofibrant (toTop.obj X) := hCofibrant X
  have hPush : WeakEquivalence (toTop.map f') :=
    weakEquivalence_of_isPushout_of_cofibrant sqTop
  change TopCat.weakHomotopyEquivalences (toTop.map f')
  exact (weakEquivalence_iff (f := toTop.map f')).mp hPush

/-- Realization weak equivalences are stable under cobase change against
simplicial monomorphisms. -/
instance realizationWeakEquivalences_isStableUnderCobaseChangeAgainst_monomorphisms :
    realizationWeakEquivalences.IsStableUnderCobaseChangeAgainst
      (MorphismProperty.monomorphisms SSet.{u}) where
  isStableUnderCobaseChangeAlong := by
    intro A B i hi
    exact
      { of_isPushout := fun sq hf => by
          let _ : Mono i := hi
          exact realizationWeakEquivalences.of_isPushout_mono sq hf }

end SSet

end
