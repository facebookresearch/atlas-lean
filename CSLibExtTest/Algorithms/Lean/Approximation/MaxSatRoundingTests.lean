/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MaxSatRounding

@[expose] public section

open Cslib.Logic.PL CSLibExt.Algorithms.Approximation.MaxSat

namespace CSLibExtTest.Algorithms.Lean.Approximation.MaxSatRounding

/-- Johnson's assignment satisfies the two-literal clause `x₀ ∨ ¬x₁` with probability `3/4`. -/
example : clauseSatProb (fun _ => 1 / 2) half_mem_Icc [(0, true), (1, false)] (by decide) =
    3 / 4 := by
  rw [clauseSatProb_half]; norm_num

/-- The rounding factors `β₁ = 1` and `β₂ = 3/4`. -/
example : roundingFactor 1 = 1 ∧ roundingFactor 2 = 3 / 4 := by
  constructor <;> norm_num [roundingFactor]

/-- The instance `x₀`, `¬x₀` (weights 1): each clause has distinct variables, and `y₀ = 1/2`,
`z = (1/2, 1/2)` is feasible for (LP). -/
def clauses : Fin 2 → CNFClause := ![[(0, true)], [(0, false)]]

theorem clauses_nodup : ∀ j, ((clauses j).map Prod.fst).Nodup := by decide

example : LPFeasible clauses (fun _ => 1 / 2) ![1 / 2, 1 / 2] := by
  refine ⟨fun _ => by norm_num, fun j => ?_⟩
  fin_cases j <;> norm_num [clauses, lpClauseBound, literalProb]

/-- Non-vacuity of Theorem 4.1 on that instance. -/
example : (3 / 4 : ℝ) * ∑ j, (fun _ => (1 : ℝ)) j * (![1 / 2, 1 / 2] : Fin 2 → ℝ) j ≤
    max (expectedWeight (fun _ => 1) clauses clauses_nodup (fun _ => 1 / 2) half_mem_Icc)
      (expectedWeight (fun _ => 1) clauses clauses_nodup (fun _ => 1 / 2) half_mem_Icc) := by
  have hf : LPFeasible clauses (fun _ => 1 / 2) ![1 / 2, 1 / 2] := by
    refine ⟨fun _ => by norm_num, fun j => ?_⟩
    fin_cases j <;> norm_num [clauses, lpClauseBound, literalProb]
  obtain ⟨h1, h2⟩ := three_quarters_le_max_expectedWeight clauses_nodup (fun _ => zero_le_one) hf
  linarith

/-- Distinct variables: for `x₀ ∨ ¬x₁` the closed form is `1 - (1 - p₀) p₁`. -/
example (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    clauseSatProb p hp [(0, true), (1, false)] (by decide) = 1 - (1 - p 0) * p 1 := by
  simp [clauseSatProb, literalProb]

open Classical in
/-- The closed form is the satisfaction probability: the assignments of `x₀` and `x₁` that satisfy
`x₀ ∨ ¬x₁`, weighted by independent rounding, have total probability `1 - (1 - p₀) p₁`. -/
example (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ∑ a : ([(0, true), (1, false)].map Prod.fst).toFinset → Bool,
      (∏ i, if a i then p i else 1 - p i) *
        (if CNFClause.Satisfies (fun n => if h : n ∈ ([(0, true), (1, false)].map Prod.fst).toFinset
            then a ⟨n, h⟩ else false) [(0, true), (1, false)] then 1 else 0) =
      1 - (1 - p 0) * p 1 := by
  rw [← clauseSatProb_eq_sum_assignments p hp (by decide)]
  simp [clauseSatProb, literalProb]

/-- Clauses that repeat a variable are excluded by the hypothesis of distinct variables, in the
same polarity (`x₀ ∨ x₀`, whose closed form at `p₀ = 1/2` would be `3/4` while the clause is
satisfied with probability `1/2`) or in opposite polarities (`x₀ ∨ ¬x₀`). -/
example : ¬ ([(0, true), (0, true)].map Prod.fst).Nodup ∧
    ¬ ([(0, true), (0, false)].map Prod.fst).Nodup := by
  decide

/-! The rounding probabilities must lie in `[0, 1]`: with `p₀ = 2`, for which the clause `x₀`
would be satisfied with "probability" `2`, the proof of `p₀ ≤ 1` cannot be given. -/

/--
error: unsolved goals
x✝ : ℕ
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ := clauseSatProb (fun _ => 2) (fun _ => by norm_num) [(0, true)] (by decide)

end CSLibExtTest.Algorithms.Lean.Approximation.MaxSatRounding
