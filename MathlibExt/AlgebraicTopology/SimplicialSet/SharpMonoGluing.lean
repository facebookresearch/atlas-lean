/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Sharpness and pullback comparisons

This file defines sharpness by the ordinary-to-homotopy pullback comparison and the weak base-change condition in the Kan–Quillen model of simplicial sets. It records the full cospan and ordinary pullback maps, their projection equations, and their agreement with the categorical limit map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
namespace SSet.SharpComparisonDraft

/-- The actual ordinary-to-named-homotopy pullback comparison. -/
def comparison {X B T : SSet.{u}} (p : X ⟶ B) (t : T ⟶ B) :=
  (HomotopicalAlgebra.homotopyPullbackComparison (C := SSet.{u})).app (cospan p t)

/-- The comparison-based sharp predicate in the original scalar Kan–Quillen model. -/
def Sharp {X B : SSet.{u}} (p : X ⟶ B) : Prop :=
  ∀ (T : SSet.{u}) (t : T ⟶ B), WeakEquivalence (comparison p t)

/-- The map of original cospans with components id, f, and id. -/
def cospanMap {X X' B T : SSet.{u}} (f : X ⟶ X') (p : X' ⟶ B) (t : T ⟶ B) :
    cospan (f ≫ p) t ⟶ cospan p t :=
  cospanHomMk (𝟙 B) f (𝟙 T) (by simp) (by simp)

/-- The original ordinary pullback map with components f and id. -/
def ordinaryMap {X X' B T : SSet.{u}} (f : X ⟶ X') (p : X' ⟶ B) (t : T ⟶ B) :
    pullback (f ≫ p) t ⟶ pullback p t :=
  pullback.map _ _ _ _ f (𝟙 T) (𝟙 B) (by simp) (by simp)

/-- Both original projection equations. -/
theorem ordinaryMap_legs {X X' B T : SSet.{u}}
    (f : X ⟶ X') (p : X' ⟶ B) (t : T ⟶ B) :
    ordinaryMap f p t ≫ pullback.fst p t = pullback.fst (f ≫ p) t ≫ f ∧
    ordinaryMap f p t ≫ pullback.snd p t = pullback.snd (f ≫ p) t := by
  constructor <;> simp [ordinaryMap]

/-- Native limit.map is exactly the same original ordinary pullback map. -/
theorem ordinaryMap_eq_limMap {X X' B T : SSet.{u}}
    (f : X ⟶ X') (p : X' ⟶ B) (t : T ⟶ B) :
    ordinaryMap f p t = lim.map (cospanMap f p t) := by
  apply pullback.hom_ext
  · simp [ordinaryMap, cospanMap]
  · simp [ordinaryMap, cospanMap]

/-- Rezk's original weak-base-change predicate, with the same ordinary pullback map. -/
def SharpBaseChange {X B : SSet.{u}} (p : X ⟶ B) : Prop :=
  ∀ (U V : SSet.{u}) (w : U ⟶ V) (v : V ⟶ B), WeakEquivalence w →
    WeakEquivalence (pullback.map p (w ≫ v) p v (𝟙 X) w (𝟙 B)
      (by simp) (by simp))

end SSet.SharpComparisonDraft
