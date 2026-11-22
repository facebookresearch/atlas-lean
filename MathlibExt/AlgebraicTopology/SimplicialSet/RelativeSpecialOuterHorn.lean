/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHornRight
public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHornOpposite

/-!
# Strict relative special outer horn filling

The endpoint type selects the left or right outer horn and its critical edge.
An inner fibration with quasicategory target fills either endpoint horn when
that edge is an equivalence, preserving the horn map and the complete base
simplex. Dimensions are written as `n + 2`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- The two endpoint positions of an outer horn. Dimensions are written as
`n + 2`, so `.zero` is horn index `0` and `.last` is index `n + 2`. -/
inductive SpecialOuterHornEndpoint where
  | zero
  | last

namespace SpecialOuterHornEndpoint

/-- The horn index selected by an endpoint in dimension `n + 2`. -/
def index (ε : SpecialOuterHornEndpoint) (n : ℕ) : Fin (n + 3) :=
  match ε with
  | .zero => 0
  | .last => Fin.last (n + 2)

@[simp]
lemma index_zero (n : ℕ) : SpecialOuterHornEndpoint.zero.index n = 0 := rfl

@[simp]
lemma index_last (n : ℕ) :
    SpecialOuterHornEndpoint.last.index n = Fin.last (n + 2) := rfl

/-- The critical-edge equivalence hypothesis for the selected outer endpoint.
This is deliberately defined only for the two endpoint indices. -/
def CriticalEdgeIsEquivalence {C : SSet.{u}} {n : ℕ}
    (ε : SpecialOuterHornEndpoint)
    (σ₀ : (horn (n + 2) (ε.index n) : SSet.{u}) ⟶ C) : Prop :=
  match ε with
  | .zero => (leftHornEdge σ₀).IsEquivalence
  | .last => (rightHornEdge σ₀).IsEquivalence

@[simp]
lemma criticalEdgeIsEquivalence_zero {C : SSet.{u}} {n : ℕ}
    (σ₀ : (horn (n + 2) (0 : Fin (n + 3)) : SSet.{u}) ⟶ C) :
    SpecialOuterHornEndpoint.zero.CriticalEdgeIsEquivalence σ₀ ↔
      (leftHornEdge σ₀).IsEquivalence :=
  Iff.rfl

@[simp]
lemma criticalEdgeIsEquivalence_last {C : SSet.{u}} {n : ℕ}
    (σ₀ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ C) :
    SpecialOuterHornEndpoint.last.CriticalEdgeIsEquivalence σ₀ ↔
      (rightHornEdge σ₀).IsEquivalence :=
  Iff.rfl

end SpecialOuterHornEndpoint

/-- Strict relative special outer horn filling at either endpoint, with the
complete base simplex prescribed. -/
theorem exists_fill_relativeSpecialOuterHorn_of_isEquivalence
    {C D : SSet.{u}} {q : C ⟶ D} [InnerFibration q] [Quasicategory D]
    {n : ℕ} (ε : SpecialOuterHornEndpoint)
    (σ₀ : (horn (n + 2) (ε.index n) : SSet.{u}) ⟶ C)
    (σBar : (Δ[n + 2] : SSet.{u}) ⟶ D)
    (hsq : σ₀ ≫ q = (horn (n + 2) (ε.index n)).ι ≫ σBar)
    (h : ε.CriticalEdgeIsEquivalence σ₀) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ C,
      (horn (n + 2) (ε.index n)).ι ≫ σ = σ₀ ∧ σ ≫ q = σBar := by
  cases ε with
  | zero =>
      exact exists_fill_relativeSpecialOuterHorn_left_of_isEquivalence
        σ₀ σBar hsq h
  | last =>
      exact exists_fill_relativeSpecialOuterHorn_right_of_isEquivalence
        σ₀ σBar hsq h

end SSet
