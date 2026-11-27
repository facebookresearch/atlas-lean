/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Control.NearestNeighborEstimate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MathlibExt.Analysis.Control

private theorem estimate_eq_of_le {n : ℕ} (y : Fin (n + 2) → ℝ) (u : Fin (n + 1) → ℝ)
    (i : Fin (n + 1))
    (h : ∀ j : Fin (n + 1),
      toLex (|y (Fin.last (n + 1)) - y i.castSucc|, i) ≤
        toLex (|y (Fin.last (n + 1)) - y j.castSucc|, j)) :
    nearestNeighborEstimate y u = y i.succ - u i := by
  let key (j : Fin (n + 1)) : ℝ ×ₗ Fin (n + 1) := toLex (|y (Fin.last (n + 1)) - y j.castSucc|, j)
  have hi : key i ∈ Finset.univ.image key := Finset.mem_image_of_mem key (Finset.mem_univ i)
  have hmin : (Finset.univ.image key).min' (Finset.univ_nonempty.image key) = key i :=
    le_antisymm (Finset.min'_le _ _ hi) (Finset.le_min' _ _ _ fun _ hj => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
      exact h j)
  change y (ofLex ((Finset.univ.image key).min' (Finset.univ_nonempty.image key))).2.succ - _ = _
  simp only [hmin, key, ofLex_toLex]

-- The first positive time has just one candidate; its successor is the current observation.
example : nearestNeighborEstimate (n := 0) ![4, 7] ![2] = 5 := by
  rw [estimate_eq_of_le _ _ (0 : Fin 1)]
  · change (7 : ℝ) - 2 = 5
    norm_num
  · intro j
    fin_cases j
    exact le_rfl

-- Indices 1 and 2 tie at distance 1; index 0 is farther away. The later tied index gives -18.
example : nearestNeighborEstimate (n := 2) ![7, 1, 3, 2] ![50, 10, 20] = -7 := by
  rw [estimate_eq_of_le _ _ (1 : Fin 3)]
  · change (3 : ℝ) - 10 = -7
    norm_num
  · intro j
    fin_cases j
    · change toLex (|(2 : ℝ) - 1|, (1 : Fin 3)) ≤ toLex (|(2 : ℝ) - 7|, (0 : Fin 3))
      norm_num [Prod.Lex.toLex_le_toLex]
    · exact le_rfl
    · change toLex (|(2 : ℝ) - 1|, (1 : Fin 3)) ≤ toLex (|(2 : ℝ) - 3|, (2 : Fin 3))
      norm_num [Prod.Lex.toLex_le_toLex]

-- Indices 0 and 2 both record the current value; keep the earlier transition, not the latest.
example : nearestNeighborEstimate (n := 2) ![1, 5, 1, 1] ![2, 0, 2] = 3 := by
  rw [estimate_eq_of_le _ _ (0 : Fin 3)]
  · change (5 : ℝ) - 2 = 3
    norm_num
  · intro j
    fin_cases j
    · exact le_rfl
    · change toLex (|(1 : ℝ) - 1|, (0 : Fin 3)) ≤ toLex (|(1 : ℝ) - 5|, (1 : Fin 3))
      norm_num [Prod.Lex.toLex_le_toLex]
    · change toLex (|(1 : ℝ) - 1|, (0 : Fin 3)) ≤ toLex (|(1 : ℝ) - 1|, (2 : Fin 3))
      norm_num [Prod.Lex.toLex_le_toLex]

-- At t = 2 the last past transition is uniquely closest regardless of future observations and
-- controls, even when y₃ is a perfect match for y₂.
example (y₃ y₄ u₂ u₃ : ℝ) :
    let y : Fin 5 → ℝ := ![7, 1, 2, y₃, y₄]
    let u : Fin 4 → ℝ := ![10, 20, u₂, u₃]
    nearestNeighborEstimate (n := 1) (fun i => y (i.castLE (by decide)))
      (fun i => u (i.castLE (by decide))) = -18 := by
  dsimp only
  rw [estimate_eq_of_le _ _ (1 : Fin 2)]
  · change (2 : ℝ) - 20 = -18
    norm_num
  · intro j
    fin_cases j
    · change toLex (|(2 : ℝ) - 1|, (1 : Fin 2)) ≤ toLex (|(2 : ℝ) - 7|, (0 : Fin 2))
      norm_num [Prod.Lex.toLex_le_toLex]
    · exact le_rfl
