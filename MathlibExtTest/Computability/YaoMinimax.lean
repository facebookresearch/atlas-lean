/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.YaoMinimax

/-!
# Tests for Yao's minimax principle
-/

namespace MathlibExtTest.Computability.YaoMinimax

open MathlibExt.Computability.YaoMinimax Convexity Matrix

/-- The uniform distribution on two inputs. -/
noncomputable def uniformTwo : StdSimplex ℝ (Fin 2) :=
  StdSimplex.duple 0 1 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-- Two algorithms on two inputs; algorithm `a` costs `1` on input `x ≠ a` and `0` on `x = a`
(a guessing game). Under the uniform input distribution each algorithm costs `1 / 2`, so every
randomized algorithm costs at least `1 / 2` on some input. -/
example (R : StdSimplex ℝ (Fin 2)) :
    ∃ x : Fin 2, 1 / 2 ≤ ∑ a, R.weights a * (if a = x then (0 : ℝ) else 1) := by
  refine exists_le_expectedCost (fun a x => if a = x then (0 : ℝ) else 1) uniformTwo R ?_
  intro a
  fin_cases a <;> simp [uniformTwo, Fin.sum_univ_two, Finsupp.single_apply]

/-- With one algorithm and one input, both sides of Yao's minimax principle are the cost. -/
example (c : ℝ) :
    (⨅ R : StdSimplex ℝ (Fin 1), ⨆ x : Fin 1,
        ((R.weights : Fin 1 → ℝ) ᵥ* Matrix.of fun _ _ => c) x) =
      ⨆ D : StdSimplex ℝ (Fin 1), ⨅ a : Fin 1,
        ((Matrix.of fun _ _ => c) *ᵥ (D.weights : Fin 1 → ℝ)) a :=
  yao_minimax (by norm_num) (by norm_num) (Matrix.of fun _ _ => c)

end MathlibExtTest.Computability.YaoMinimax
