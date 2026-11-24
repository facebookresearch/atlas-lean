/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Identity
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# Actual Cartesian and cocartesian fibration carriers

The inner-fibration map is retained together with lifts of every original
base edge. A lift is required to satisfy the literal relative slice
condition, and its source/target equality and whole mapped edge are
recorded. These are genuine fibration predicates, not assumed straightening
or model equivalence certificates.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- An inner fibration with original target-prescribed p-cartesian lifts. -/
class CartesianFibration {X B : SSet.{u}} (p : X ⟶ B) : Prop extends InnerFibration p where
  /-- Lift the whole original base edge to the supplied original target vertex. -/
  lift (y : X _⦋0⦌) (b : B _⦋0⦌) (e : Edge b (p.app (op ⦋0⦌) y)) :
    ∃ (x : X _⦋0⦌) (_ : p.app (op ⦋0⦌) x = b) (a : Edge x y),
      CartesianEdge.IsPCartesian p (yonedaEquiv.symm a.edge) ∧ (a.map p).edge = e.edge

/-- An inner fibration with original source-prescribed p-cocartesian lifts. -/
class CocartesianFibration {X B : SSet.{u}} (p : X ⟶ B) : Prop extends InnerFibration p where
  /-- Lift the whole original base edge from the supplied original source vertex. -/
  lift (x : X _⦋0⦌) (b : B _⦋0⦌) (e : Edge (p.app (op ⦋0⦌) x) b) :
    ∃ (y : X _⦋0⦌) (_ : p.app (op ⦋0⦌) y = b) (a : Edge x y),
      CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm a.edge) ∧ (a.map p).edge = e.edge

/-- A Cartesian fibration over a genuine quasicategory has the actual quasicategory source. -/
theorem CartesianFibration.quasicategory_source {X B : SSet.{u}} (p : X ⟶ B)
    [CartesianFibration p] [Quasicategory B] : Quasicategory X :=
  quasicategory_of_innerFibration p

/-- A cocartesian fibration over a genuine quasicategory has the actual quasicategory source. -/
theorem CocartesianFibration.quasicategory_source {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] [Quasicategory B] : Quasicategory X :=
  quasicategory_of_innerFibration p

/-- The identity map has its original Cartesian edge lifts in every value universe. -/
theorem CartesianFibration.identity (X : SSet.{u}) : CartesianFibration (𝟙 X) where
  toInnerFibration := ⟨innerHornInclusions.rlp_of_isIso (𝟙 X)⟩
  lift y b e := ⟨b, rfl, e, CartesianEdge.isPCartesian_id X _, by simp⟩

/-- The identity map has its original cocartesian edge lifts in every value universe. -/
theorem CocartesianFibration.identity (X : SSet.{u}) : CocartesianFibration (𝟙 X) where
  toInnerFibration := ⟨innerHornInclusions.rlp_of_isIso (𝟙 X)⟩
  lift x b e := ⟨b, rfl, e, CocartesianEdge.isPCocartesian_id X _, by simp⟩

end SSet
