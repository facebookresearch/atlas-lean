/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import Mathlib.CategoryTheory.Equivalence

/-!
# Mapping-fibre weakness and the original intrinsic Ho functor

The original functor acts on homs by the component map of the same mapping-fibre
arrow. Full realization weakness therefore gives its full and faithful
properties. Actual essential surjectivity of that same functor completes
the native category-equivalence structure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.SegalHomotopy

/-- Full weakness of every original mapping-fibre map makes the original intrinsic Ho functor
full. -/
theorem map_full_of_mappingFibreWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl)) :
    (map f hW hV).Full := by
  constructor
  intro a b
  change Function.Surjective (SSet.mapπ₀
      (mappingFibre.map f (x := a.vertex) (y := b.vertex) rfl rfl))
  exact (hm a.vertex b.vertex).bijective_mapπ₀.2

/-- The same full original mapping-fibre hypothesis makes that intrinsic Ho functor faithful. -/
theorem map_faithful_of_mappingFibreWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl)) :
    (map f hW hV).Faithful := by
  constructor
  intro a b
  change Function.Injective (SSet.mapπ₀
      (mappingFibre.map f (x := a.vertex) (y := b.vertex) rfl rfl))
  exact (hm a.vertex b.vertex).bijective_mapπ₀.1

/-- The proved full and faithful original functor is an equivalence when it is actually essentially
surjective. -/
theorem map_isEquivalence_of_mappingFibreWeak_of_essSurj
    {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
      SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl))
    (hE : (map f hW hV).EssSurj) :
    (map f hW hV).IsEquivalence where
  faithful := map_faithful_of_mappingFibreWeak f hW hV hm
  full := map_full_of_mappingFibreWeak f hW hV hm
  essSurj := hE

end SimplicialSpace.SegalHomotopy
