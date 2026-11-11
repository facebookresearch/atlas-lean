/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax

open Matrix

/-- Boundary check: in a `1 × 1` game every mixed strategy is the constant
`1` strategy, so the saddle payoff is the single entry. -/
example (A : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ p ∈ stdSimplex ℝ (Fin 1), ∃ q ∈ stdSimplex ℝ (Fin 1),
      p ⬝ᵥ (A *ᵥ q) = A 0 0 := by
  obtain ⟨p, hp, q, hq, -, -⟩ := matrixGame_exists_isSaddlePointOn (m := 1) (n := 1) (by norm_num) (by norm_num) A
  have hp0 : p 0 = 1 := by
    have h := hp.2
    simpa using h
  have hq0 : q 0 = 1 := by
    have h := hq.2
    simpa using h
  refine ⟨p, hp, q, hq, ?_⟩
  simp [dotProduct, mulVec, Fin.sum_univ_one, hp0, hq0]

/-- The minimax value of a `1 × 1` game is its single entry, seen from the
maximin side. -/
example (A : Matrix (Fin 1) (Fin 1) ℝ) :
    (⨆ p : stdSimplex ℝ (Fin 1), ⨅ q : stdSimplex ℝ (Fin 1),
      (p : Fin 1 → ℝ) ⬝ᵥ (A *ᵥ (q : Fin 1 → ℝ))) =
      ⨅ q : stdSimplex ℝ (Fin 1), ⨆ p : stdSimplex ℝ (Fin 1),
        (p : Fin 1 → ℝ) ⬝ᵥ (A *ᵥ (q : Fin 1 → ℝ)) :=
  matrixGame_minimax (by norm_num) (by norm_num) A
