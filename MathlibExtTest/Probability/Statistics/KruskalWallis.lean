/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.KruskalWallis
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tests for the Kruskal–Wallis statistic

With identity ranking and groups containing ranks `1` and `2, 3`, the centered form gives
`H = 3/2`.
-/

open WantedExt.Probability.Statistics.KruskalWallisWanted

private def groups : Fin 3 → Fin 2 := ![0, 1, 1]

example : kruskalWallis groups (Equiv.refl (Fin 3)) = 3 / 2 := by
  have hSize₀ : sampleSize groups 0 = 1 := by decide
  have hSize₁ : sampleSize groups 1 = 2 := by decide
  have hRank₀ : rankSum groups (Equiv.refl (Fin 3)) 0 = 1 := by decide
  have hRank₁ : rankSum groups (Equiv.refl (Fin 3)) 1 = 5 := by decide
  have hn : ∀ i, 0 < sampleSize groups i := Fin.forall_fin_two.mpr
    ⟨by rw [hSize₀]; decide, by rw [hSize₁]; decide⟩
  rw [kruskalWallis_eq_sum_sq groups (by decide) hn, Fin.sum_univ_two, hSize₀, hSize₁,
    hRank₀, hRank₁]
  norm_num

example : kruskalWallis groups (Equiv.refl (Fin 3)) = 3 / 2 := by
  have hSize₀ : sampleSize groups 0 = 1 := by decide
  have hRank₀ : rankSum groups (Equiv.refl (Fin 3)) 0 = 1 := by decide
  have hn : ∀ i, 0 < sampleSize groups i := Fin.forall_fin_two.mpr ⟨by decide, by decide⟩
  rw [kruskalWallis_two_samples groups hn, hSize₀, hRank₀]
  norm_num
