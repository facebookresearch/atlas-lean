/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax

open Matrix Convexity

/-- Boundary check: in a `1 × 1` game every mixed strategy is the constant
`1` strategy, so the saddle payoff is the single entry. -/
example (A : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ (p : StdSimplex ℝ (Fin 1)) (q : StdSimplex ℝ (Fin 1)),
      p.weights ⬝ᵥ (A *ᵥ q.weights) = A 0 0 := by
  obtain ⟨p, q, -, -⟩ :=
    matrixGame_exists_isSaddlePointOn (by norm_num) (by norm_num) A
  exact ⟨p, q, by simp [dotProduct, mulVec]⟩

/-- The maximin value of a `1 × 1` game is its single entry. -/
example (A : Matrix (Fin 1) (Fin 1) ℝ) :
    (⨆ p : StdSimplex ℝ (Fin 1), ⨅ q : StdSimplex ℝ (Fin 1),
      p.weights ⬝ᵥ (A *ᵥ q.weights)) = A 0 0 := by
  simp [dotProduct, mulVec]

/-- The minimax side gives the same singleton value through the public theorem. -/
example (A : Matrix (Fin 1) (Fin 1) ℝ) :
    (⨅ q : StdSimplex ℝ (Fin 1), ⨆ p : StdSimplex ℝ (Fin 1),
      p.weights ⬝ᵥ (A *ᵥ q.weights)) = A 0 0 := by
  rw [← matrixGame_minimax (by norm_num) (by norm_num) A]
  simp [dotProduct, mulVec]

#print axioms matrixGame_exists_isSaddlePointOn
#print axioms matrixGame_minimax
