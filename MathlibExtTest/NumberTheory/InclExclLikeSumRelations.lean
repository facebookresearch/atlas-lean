/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InclExclLikeSumRelations
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.inclExclLikeSum_relations_and_periodic

-- The two half-coordinate corrections have opposite signs at a rounding tie.
example :
    let x : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    inclExclLikeSum Int.floor x - inclExclLikeSum Int.floor (Fin.snoc x (1 / 2)) = 1 ∧
      inclExclLikeSum Int.ceil x - inclExclLikeSum Int.ceil (Fin.snoc x (-1 / 2)) = -1 := by
  dsimp only
  obtain ⟨hup, hdown, _⟩ :=
    inclExclLikeSum_relations_and_periodic (hn := by decide) (![1 / 2, 1 / 2] : Fin 2 → ℝ)
  rw [← hup, ← hdown]
  norm_num [inclExclLikeSum_two, round_eq]

-- A negative period preserves a nonzero sum at the minimum allowed dimension.
example : inclExclLikeSum round
    (Function.update (![1 / 2, 1 / 2] : Fin 2 → ℝ) 1 (-1 / 2)) = 1 := by
  have h := (inclExclLikeSum_relations_and_periodic (hn := by decide)
    (![1 / 2, 1 / 2] : Fin 2 → ℝ)).2.2 round (by simp) 1 (-1)
  norm_num [inclExclLikeSum_two, round_eq] at h ⊢
  exact h

-- In one variable the floor sum increases under a unit shift.
example : inclExclLikeSum Int.floor ![(1 / 2 : ℝ) + 1] ≠ inclExclLikeSum Int.floor ![1 / 2] := by
  norm_num [inclExclLikeSum_one]

end MetaMathlibExt.inclExclLikeSum_relations_and_periodic
