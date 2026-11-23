/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.UnconditionalRegretMatching

open MathlibExt.GameTheory.UnconditionalRegretMatching
open MathlibExt.GameTheory.BlackwellApproachability

/-- Matching pennies from the mismatching side: cost `1` when the actions match, `0` otherwise. -/
def penniesCost (a b : Fin 2) : ℝ := if a = b then 1 else 0

/-- Its regret vectors have norm at most `2`. -/
theorem norm_regretVector_pennies_le (a b : Fin 2) : ‖regretVector penniesCost a b‖ ≤ 2 := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 ?_
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [regretVector, PiLp.toLp_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> norm_num [penniesCost]

/-- Against every sequence of the opponent, unconditional regret matching has average expected
regret at most `4 / √n` against each fixed action. -/
example (β : ℕ → Fin 2) {n : ℕ} (hn : 0 < n) (k : Fin 2) :
    (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
      (∑ a, urm (average (strategyPayoffs (regretVector penniesCost) urm β) t) a *
        penniesCost a (β t) - penniesCost k (β t)) ≤ 2 * 2 / Real.sqrt n :=
  average_regret_le_of_urm penniesCost norm_regretVector_pennies_le β hn k

/-- With no positive regret, regret matching is uniform. -/
example : urm (0 : EuclideanSpace ℝ (Fin 2)) = fun _ => 1 / 2 := by
  funext k
  simp [urm]

#print axioms average_regret_le_of_urm
