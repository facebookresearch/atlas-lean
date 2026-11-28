/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GraphTheory.BookThicknessOfSubdivisionsDefs

namespace MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted

/-- Interleaved pairs cross along the natural order. -/
example : IsCrossing (fun a b : ℕ => a < b) s(0, 2) s(1, 3) :=
  ⟨0, 2, 1, 3, by simp, by simp, by decide, by simp, by simp, by decide,
    Or.inl ⟨by decide, by decide, by decide⟩⟩

/-- Nested pairs do not cross. -/
example : ¬ IsCrossing (fun a b : ℕ => a < b) s(0, 3) s(1, 2) := by
  rintro ⟨v, w, x, y, hv, hw, -, hx, hy, -, h⟩
  simp only [Sym2.mem_iff] at hv hw hx hy
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;> omega

/-- Disjoint consecutive pairs do not cross. -/
example : ¬ IsCrossing (fun a b : ℕ => a < b) s(0, 1) s(2, 3) := by
  rintro ⟨v, w, x, y, hv, hw, -, hx, hy, -, h⟩
  simp only [Sym2.mem_iff] at hv hw hx hy
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;> omega

/-- Pairs sharing an endpoint do not cross. -/
example : ¬ IsCrossing (fun a b : ℕ => a < b) s(0, 2) s(0, 1) := by
  rintro ⟨v, w, x, y, hv, hw, -, hx, hy, -, h⟩
  simp only [Sym2.mem_iff] at hv hw hx hy
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;> omega

/-- Every graph on three vertices has a one-page book embedding: a crossing needs four
distinct spine positions. -/
example (G : SimpleGraph (Fin 3)) : HasBookEmbedding G 1 := by
  refine ⟨Fin.val, Fin.val_injective, fun _ => 0, fun _ _ h => ?_⟩
  obtain ⟨v, w, x, y, -, -, -, -, -, -, h⟩ := h
  have := v.isLt
  have := y.isLt
  omega

/-- A graph with an edge has no book embedding with zero pages. -/
example : ¬ HasBookEmbedding (⊤ : SimpleGraph (Fin 2)) 0 := by
  rintro ⟨-, -, color, -⟩
  exact (color ⟨s(0, 1), by simp⟩).elim0

/-- The edgeless graph has a book embedding with zero pages. -/
example : HasBookEmbedding (⊥ : SimpleGraph (Fin 3)) 0 :=
  ⟨Fin.val, Fin.val_injective, fun e => absurd e.2 (by simp), fun e => absurd e.2 (by simp)⟩

end MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted
