/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero

/-! # Original component preimages and full relation reflection -/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.RealizationWeakPiZeroTest

/-- Every original target component has a unique original preimage component. -/
theorem unique_component_preimage
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (q : π₀ Y) :
    ∃! p : π₀ X, mapπ₀ f p = q :=
  (realizationWeakEquivalences.bijective_mapπ₀ hf).existsUnique q

/-- Equality of image components reflects the full original edge-generated relation. -/
theorem reflect_component_relation
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (a b : X _⦋0⦌)
    (h : π₀.mk (f.app (op ⦋0⦌) a) = π₀.mk (f.app (op ⦋0⦌) b)) :
    Relation.EqvGen (π₀Rel (X := X)) a b := by
  have hab : mapπ₀ f (π₀.mk a) = mapπ₀ f (π₀.mk b) := by
    simpa only [mapπ₀_mk] using h
  exact (π₀.mk_eq_mk_iff a b).1
    ((realizationWeakEquivalences.bijective_mapπ₀ hf).1 hab)

/-- A target vertex has an original source vertex in its component; literal vertex
surjectivity is not asserted. -/
theorem vertex_component_preimage
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f)
    (b : Y _⦋0⦌) :
    ∃ a : X _⦋0⦌, Relation.EqvGen (π₀Rel (X := Y))
      (f.app (op ⦋0⦌) a) b := by
  obtain ⟨p, hp⟩ := (realizationWeakEquivalences.bijective_mapπ₀ hf).2 (π₀.mk b)
  obtain ⟨a, rfl⟩ := π₀.mk_surjective p
  refine ⟨a, (π₀.mk_eq_mk_iff _ _).1 ?_⟩
  simpa only [mapπ₀_mk] using hp

end SSet.RealizationWeakPiZeroTest
