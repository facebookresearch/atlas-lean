/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.Basic.Countable.Basic

/-!
# Countability of all original simplices and generating-domain maps

Countability is retained in every original scalar degree and in the
entire original simplex family. The actual Yoneda bijection counts whole
simplex maps. Original full boundary and horn maps embed in their finite
families of actual whole face maps, including the empty boundary.
No replacement of the original map or its coefficients is made.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet

/-- Every original scalar degree has its actual countable simplex set. -/
protected class CountableSimplices (X : SSet.{u}) : Prop where
  countable_obj (q : SimplexCategoryᵒᵖ) : Countable (X.obj q)

attribute [instance] CountableSimplices.countable_obj

/-- Finite original simplicial sets have countably many original simplices in EVERY scalar degree. -/
instance countableSimplices_of_finite (X : SSet.{u}) [X.Finite] : X.CountableSimplices where
  countable_obj _ := inferInstance

/-- The entire original simplex family is countable, retaining every dimension. -/
theorem countable_all_simplices (X : SSet.{u}) [X.CountableSimplices] :
    Countable (Σ n : ℕ, X _⦋n⦌) := inferInstance

/-- The SAME full original simplex maps are counted by the native original Yoneda bijection. -/
theorem countable_simplex_maps (X : SSet.{u}) [X.CountableSimplices] (n : ℕ) :
    Countable ((Δ[n] : SSet.{u}) ⟶ X) :=
  Countable.of_equiv (X _⦋n⦌) SSet.yonedaEquiv.symm

/-- Every whole original boundary map is counted through its actual finite family of original face maps, including
degree zero. -/
theorem countable_boundary_maps (X : SSet.{u}) [X.CountableSimplices] (n : ℕ) :
    Countable ((∂Δ[n] : SSet.{u}) ⟶ X) := by
  cases n with
  | zero =>
    have hI : IsInitial (∂Δ[0] : SSet.{u}) :=
      (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
        (Subcomplex.eqToIso boundary_zero).symm
    have : Subsingleton ((∂Δ[0] : SSet.{u}) ⟶ X) := ⟨hI.hom_ext⟩
    infer_instance
  | succ n =>
    have : Countable ((Δ[n] : SSet.{u}) ⟶ X) := countable_simplex_maps X n
    let faces : ((∂Δ[n + 1] : SSet.{u}) ⟶ X) → (Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X)) :=
      fun f j => boundary.ι j ≫ f
    have h : Function.Injective faces := by
      intro f g hfg
      apply boundary.hom_ext
      intro j
      exact congrArg (fun h => h j) hfg
    exact h.countable

/-- Every whole original positive-dimensional horn map is counted through all its actual prescribed faces. -/
theorem countable_horn_maps (X : SSet.{u}) [X.CountableSimplices] (n : ℕ) (i : Fin (n + 2)) :
    Countable ((Λ[n + 1, i] : SSet.{u}) ⟶ X) := by
  have : Countable ((Δ[n] : SSet.{u}) ⟶ X) := countable_simplex_maps X n
  let faces : ((Λ[n + 1, i] : SSet.{u}) ⟶ X) →
      ({j : Fin (n + 2) // j ≠ i} → ((Δ[n] : SSet.{u}) ⟶ X)) :=
    fun f j => horn.ι i j.val j.property ≫ f
  have h : Function.Injective faces := by
    intro f g hfg
    apply horn.hom_ext'
    intro j hj
    exact congrArg (fun h => h ⟨j, hj⟩) hfg
  exact h.countable

end SSet
