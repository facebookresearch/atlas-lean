/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.Chvatal
import Mathlib.Data.Fintype.Powerset

open Finset MathlibExt.Combinatorics.ChvatalHereditaryIntersectingWanted

private def triangle : Finset (Finset (Fin 3)) := univ.filter (fun A => A.card ≤ 2)
private def edges : Finset (Finset (Fin 3)) := univ.filter (fun A => A.card = 2)

-- The three edges have no common vertex.
example : ¬ ∃ x : Fin 3, ∀ A ∈ edges, x ∈ A := by decide

-- They meet pairwise and tie a largest star.
example : ∃ x : Fin 3, edges.card = (triangle.filter (fun A => x ∈ A)).card := by
  have hF : IsHereditary triangle := by
    intro A hA B hBA
    simp only [triangle, mem_filter, mem_univ, true_and] at hA ⊢
    exact (card_le_card hBA).trans hA
  have hG : SetFamily.IsIntersecting edges := by unfold SetFamily.IsIntersecting; decide
  obtain ⟨x, hx⟩ := conjecture_holds (Fin 3) triangle hF (by
    exact ⟨{0}, by decide, by decide⟩)
  refine ⟨x, (hx edges (by decide) hG).antisymm ?_⟩
  exact (by decide : ∀ i : Fin 3, (triangle.filter (fun A => i ∈ A)).card ≤ edges.card) x

-- The exceptional intersecting family {∅} ties the star on a one-point ground set.
example : ∃ x : Unit, ({∅} : Finset (Finset Unit)).card ≤
    ((univ : Finset (Finset Unit)).filter (fun A => x ∈ A)).card := by
  obtain ⟨x, hx⟩ := conjecture_holds Unit univ (fun _ _ _ _ => mem_univ _)
    ⟨{()}, mem_univ _, by decide⟩
  exact ⟨x, hx {∅} (subset_univ _) (by unfold SetFamily.IsIntersecting; decide)⟩
