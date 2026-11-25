/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne

/-!
# The native fully marked interval classifies marked original edges

Its three degree-one simplices are the two degenerate endpoint edges and
the original identity simplex. A marked edge therefore gives a unique
marked map out of the maximally marked interval, with the whole original
Yoneda map retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem interval_identity :
    SSet.stdSimplex.objMk₁.{u} (1 : Fin 3) =
      SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
  ext i
  fin_cases i <;> rfl

/-- A marked original edge gives its native marked map from the maximally marked interval. -/
def intervalMapOfMarkedEdge {Y : Marked.{u}} (e : Y.toSSet _⦋1⦌) (he : e ∈ Y.marking) :
    max (Δ[1] : SSet.{u}) ⟶ Y where
  hom := SSet.yonedaEquiv.symm e
  preserve {a} _ := by
    obtain ⟨i, rfl⟩ := SSet.stdSimplex.objMk₁_surjective a
    fin_cases i
    · change (SSet.yonedaEquiv.symm e).app (op ⦋1⦌)
        (SSet.stdSimplex.objMk₁ (0 : Fin 3)) ∈ Y.marking
      have h : (Δ[1] : SSet.{u}).σ (0 : Fin 1)
          (SSet.stdSimplex.objMk₁ (0 : Fin 2)) = SSet.stdSimplex.objMk₁ (0 : Fin 3) :=
        SSet.stdSimplex.σ_objMk₁_of_le (0 : Fin 2) (0 : Fin 1) (by decide)
      rw [← h, SSet.σ_naturality_apply]
      exact Y.degenerate_mem _
    · change (SSet.yonedaEquiv.symm e).app (op ⦋1⦌)
        (SSet.stdSimplex.objMk₁ (1 : Fin 3)) ∈ Y.marking
      rw [interval_identity, SSet.yonedaEquiv_symm_app_id]
      exact he
    · change (SSet.yonedaEquiv.symm e).app (op ⦋1⦌)
        (SSet.stdSimplex.objMk₁ (2 : Fin 3)) ∈ Y.marking
      have h : (Δ[1] : SSet.{u}).σ (0 : Fin 1)
          (SSet.stdSimplex.objMk₁ (1 : Fin 2)) = SSet.stdSimplex.objMk₁ (2 : Fin 3) :=
        SSet.stdSimplex.σ_objMk₁_of_lt (1 : Fin 2) (0 : Fin 1) (by decide)
      rw [← h, SSet.σ_naturality_apply]
      exact Y.degenerate_mem _

/-- Marked interval maps and actual marked edges are equivalent, through original Yoneda
  evaluation. -/
def maxIntervalHomEquiv (Y : Marked.{u}) : (max (Δ[1] : SSet.{u}) ⟶ Y) ≃ Y.marking where
  toFun f := ⟨SSet.yonedaEquiv f.hom, f.preserve (Set.mem_univ _)⟩
  invFun e := intervalMapOfMarkedEdge e.val e.property
  left_inv f := Hom.ext (Equiv.symm_apply_apply SSet.yonedaEquiv f.hom)
  right_inv e := Subtype.ext (Equiv.apply_symm_apply SSet.yonedaEquiv e.val)

/-- The complete original interval map is retained by the edge classifier. -/
@[simp]
theorem intervalMapOfMarkedEdge_hom {Y : Marked.{u}} (e : Y.toSSet _⦋1⦌) (he : e ∈ Y.marking) :
    (intervalMapOfMarkedEdge e he).hom = SSet.yonedaEquiv.symm e := rfl

end SSet.Marked
