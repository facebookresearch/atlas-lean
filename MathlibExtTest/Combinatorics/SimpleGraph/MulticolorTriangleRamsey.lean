/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.SimpleGraph.MulticolorTriangleRamsey
import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace SimpleGraph

private theorem zeroColoring_nonempty {n : ℕ} (hn : n < 2) :
    Nonempty (TopEdgeLabeling (Fin n) (Fin 0)) := by
  apply Fintype.card_pos_iff.mp
  rw [card_topEdgeLabeling]
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with rfl | rfl <;> decide

private theorem noZeroColoringOfTwo : IsEmpty (TopEdgeLabeling (Fin 2) (Fin 0)) := by
  apply Fintype.card_eq_zero_iff.mp
  rw [card_topEdgeLabeling]
  decide

/-- The empty palette is vacuous exactly at the first nonempty edge set. -/
example : multicolorTriangleRamseyNumber 0 = 2 := by
  unfold multicolorTriangleRamseyNumber
  have h₂ : (2 : ℕ) ∈ {n | ∀ C : TopEdgeLabeling (Fin n) (Fin 0),
      ∃ color : Fin 0, ¬ (C.labelGraph color).CliqueFree 3} :=
    fun C => False.elim (noZeroColoringOfTwo.false C)
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) h₂) (le_csInf ⟨2, h₂⟩ ?_)
  intro n hn
  by_contra! hlt
  obtain ⟨C⟩ := zeroColoring_nonempty hlt
  obtain ⟨color, _⟩ := hn C
  exact Fin.elim0 color

/-- The one-color threshold is precisely the number of vertices of a triangle. -/
example : multicolorTriangleRamseyNumber 1 = 3 := by
  unfold multicolorTriangleRamseyNumber
  have h₃ : (3 : ℕ) ∈ {n | ∀ C : TopEdgeLabeling (Fin n) (Fin 1),
      ∃ color : Fin 1, ¬ (C.labelGraph color).CliqueFree 3} := by
    intro C
    refine ⟨0, ?_⟩
    have heq : C.labelGraph 0 = ⊤ := by
      ext i j
      rw [TopEdgeLabeling.labelGraph_adj]
      constructor
      · rintro ⟨h, _⟩
        exact h
      · intro h
        exact ⟨h, Subsingleton.elim _ _⟩
    rw [heq, not_cliqueFree_iff_top_isContained]
    exact IsContained.refl _
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) h₃) (le_csInf ⟨3, h₃⟩ ?_)
  intro n hn
  by_contra! hlt
  obtain ⟨color, hcolor⟩ := hn (fun _ => 0)
  exact hcolor (cliqueFree_of_card_lt (by simpa using hlt))

open Classical in
/-- The two-color instance agrees with the existing classical Ramsey API. -/
example : multicolorTriangleRamseyNumber 2 = graphRamsey 3 3 := by
  rw [multicolorTriangleRamseyNumber, graphRamsey_eq_sInf]
  congr 1
  ext n
  change (∀ C : TopEdgeLabeling (Fin n) (Fin 2), ∃ color : Fin 2,
      ¬ (C.labelGraph color).CliqueFree 3) ↔ classicalRamsey 3 3 n
  constructor
  · intro h G
    obtain ⟨color, hcolor⟩ := h G.toTopEdgeLabeling
    fin_cases color
    · exact Or.inr ((not_cliqueFree_iff_top_isContained 3).mp (by simpa using hcolor))
    · exact Or.inl ((not_cliqueFree_iff_top_isContained 3).mp (by simpa using hcolor))
  · intro h C
    rcases h (C.labelGraph 1) with h₁ | h₀
    · exact ⟨1, h₁.not_cliqueFree⟩
    · have hcompl : C.labelGraph 0 = (C.labelGraph 1)ᶜ := by
        rw [← (C.labelGraph 1).toTopEdgeLabeling_labelGraph_compl,
          C.labelGraph_toTopEdgeLabeling]
      refine ⟨0, ?_⟩
      rw [hcompl]
      exact h₀.not_cliqueFree

end SimpleGraph
