/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# The literal relative slice comparison for (co)cartesian edges

Restriction of an edge to its target (respectively source) vertex and the
original base map give a specified pullback comparison of join slices.
The relative edge condition is lifting against every actual standard
boundary inclusion by this comparison. The diagrams and both projections
retain their original maps. No straightening/model equivalence is assumed.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet
namespace CartesianEdge

variable {X B : SSet.{u}}

/-- The actual over-slice comparison at the target endpoint of the original edge. -/
abbrev comparison (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    sliceOver X e ⟶
      pullback (sliceOver.map X (stdSimplex.δ (0 : Fin 2) ≫ e) p)
        (sliceOver.restrict B (e ≫ p) (stdSimplex.δ (0 : Fin 2))) :=
  sliceOver.restrictionComparison (stdSimplex.δ (0 : Fin 2)) e p

/-- The first leg is precisely the original edge-to-target restriction. -/
theorem comparison_fst (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    comparison p e ≫ pullback.fst _ _ = sliceOver.restrict X e (stdSimplex.δ (0 : Fin 2)) :=
  sliceOver.restrictionComparison_fst (stdSimplex.δ (0 : Fin 2)) e p

/-- The second leg is precisely the original base map on the edge slice. -/
theorem comparison_snd (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    comparison p e ≫ pullback.snd _ _ = sliceOver.map X e p :=
  sliceOver.restrictionComparison_snd (stdSimplex.δ (0 : Fin 2)) e p

/-- The actual p-cartesian edge condition, expressed by the specified over-slice boundary lifting. -/
def IsPCartesian (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) : Prop :=
  ∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι (comparison p e)

/-- The same Cartesian boundary lifts are the native structured pushout-join lifts. -/
theorem isPCartesian_iff_joinLifting (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    IsPCartesian p e ↔ ∀ n : ℕ,
      HasLiftingProperty (joinOverPushoutMap (stdSimplex.δ (0 : Fin 2)) (boundary.{u} n).ι)
        (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) := by
  constructor
  · intro h n
    exact (sliceOver.hasLiftingProperty_restrictionComparison_iff _ _ _ _).mpr (h n)
  · intro h n
    exact (sliceOver.hasLiftingProperty_restrictionComparison_iff _ _ _ _).mp (h n)

end CartesianEdge

namespace CocartesianEdge

variable {X B : SSet.{u}}

/-- The actual under-slice comparison at the source endpoint of the original edge. -/
abbrev comparison (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    sliceUnder X e ⟶
      pullback (sliceUnder.map X (stdSimplex.δ (1 : Fin 2) ≫ e) p)
        (sliceUnder.restrict B (e ≫ p) (stdSimplex.δ (1 : Fin 2))) :=
  sliceUnder.restrictionComparison (stdSimplex.δ (1 : Fin 2)) e p

/-- The first leg is precisely the original edge-to-source restriction. -/
theorem comparison_fst (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    comparison p e ≫ pullback.fst _ _ = sliceUnder.restrict X e (stdSimplex.δ (1 : Fin 2)) :=
  sliceUnder.restrictionComparison_fst (stdSimplex.δ (1 : Fin 2)) e p

/-- The second leg is precisely the original base map on the edge slice. -/
theorem comparison_snd (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    comparison p e ≫ pullback.snd _ _ = sliceUnder.map X e p :=
  sliceUnder.restrictionComparison_snd (stdSimplex.δ (1 : Fin 2)) e p

/-- The actual p-cocartesian edge condition, expressed by the specified under-slice boundary lifting. -/
def IsPCocartesian (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) : Prop :=
  ∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι (comparison p e)

/-- The same cocartesian boundary lifts are the native structured pushout-join lifts. -/
theorem isPCocartesian_iff_joinLifting (p : X ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    IsPCocartesian p e ↔ ∀ n : ℕ,
      HasLiftingProperty (joinUnderPushoutMap (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι)
        (Under.homMk p rfl : Under.mk e ⟶ Under.mk (e ≫ p)) := by
  constructor
  · intro h n
    exact (sliceUnder.hasLiftingProperty_restrictionComparison_iff _ _ _ _).mpr (h n)
  · intro h n
    exact (sliceUnder.hasLiftingProperty_restrictionComparison_iff _ _ _ _).mp (h n)

end CocartesianEdge
end SSet
