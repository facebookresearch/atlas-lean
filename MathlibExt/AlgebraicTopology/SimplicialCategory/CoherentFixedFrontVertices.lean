/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontOperators

/-!
# Exact original structural vertices of the fixed-front resolution

The actual quotient resolving simplex has exactly its structural front
source and original last target as vertices. They are distinct in every
resolving height, and every actual right-join operator preserves them.
No target enriched object is quotiented in this construction.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontVertices
open FixedFrontCollapse FixedFrontOperators PathMaximumOperators
variable {n m : ℕ}

/-- A constant original resolving vertex away from the last label belongs to the original front. -/
theorem constant_front (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    InFront (SSet.stdSimplex.objEquiv.{u}.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j)) := by
  intro i
  exact hj

/-- Every actual original front vertex has precisely the same structural quotient source image. -/
theorem front_vertex (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    (projection.{u} n).app (op ⦋0⦌) (SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j)) = source n :=
  projection_front_eq _ _ (constant_front j hj) (constant_front 0 (by exact ne_of_lt Fin.last_pos))

/-- The original structural target vertex is not an original front simplex. -/
theorem target_not_front : ¬InFront (SSet.stdSimplex.objEquiv.{u}.symm
    (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)))) := fun h => h 0 rfl

/-- The actual structural source and target of the fixed-front quotient are distinct. -/
theorem source_ne_target (n : ℕ) : source.{u} n ≠ target n := by
  intro h
  have hRel := _root_.Quotient.exact h
  rcases hRel with hEq | hFront
  · have hV := congrArg (fun a => a.down.toOrderHom 0) hEq
    exact (ne_of_lt Fin.last_pos) hV
  · exact target_not_front hFront.2

/-- Every actual quotient vertex is exactly its structural source or original last target. -/
theorem vertices (n : ℕ) (a : (object.{u} n) _⦋0⦌) : a = source n ∨ a = target n := by
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    let j := a.down.toOrderHom 0
    have hA : a = SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j) := by
      apply SSet.stdSimplex.objEquiv.injective
      ext i : 3
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
    by_cases hj : j = Fin.last (n + 1)
    · right
      exact (congrArg (fun a => _root_.Quotient.mk _ a) hA).trans
        (congrArg (fun j => (projection.{u} n).app (op ⦋0⦌) (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ j))) hj)
    · left
      exact (congrArg (fun a => _root_.Quotient.mk _ a) hA).trans (front_vertex j hj)

/-- The entire actual quotient operator retains the original structural source label. -/
theorem map_source (θ : ⦋n⦌ ⟶ ⦋m⦌) : (FixedFrontOperators.map.{u} θ).app (op
  ⦋0⦌) (source n) = source m := by
  have hV : (SSet.stdSimplex.map (extension θ)).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)) =
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ (θ.toOrderHom
      0).castSucc) := by
    apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    exact extension_front θ 0
  exact (congrArg (fun a => (projection.{u} m).app (op ⦋0⦌) a) hV).trans
    (front_vertex (θ.toOrderHom 0).castSucc (ne_of_lt (Fin.castSucc_lt_last _)))

/-- The entire actual quotient operator retains the original last target label. -/
theorem map_target (θ : ⦋n⦌ ⟶ ⦋m⦌) : (FixedFrontOperators.map.{u} θ).app (op
  ⦋0⦌) (target n) = target m := by
  have hV : (SSet.stdSimplex.map (extension θ)).app (op ⦋0⦌)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)))) =
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ (Fin.last (m + 1))) := by
    apply SSet.stdSimplex.objEquiv.injective
    ext i : 3
    exact extension_last θ
  exact congrArg (fun a => (projection.{u} m).app (op ⦋0⦌) a) hV

end CategoryTheory.CoherentRealization.FixedFrontVertices
