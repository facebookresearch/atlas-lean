/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RandomGraphTriangleThreshold

@[expose] public section

open MeasureTheory SimpleGraph unitInterval Filter
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Combinatorics.RandomGraphTriangleThreshold

namespace MathlibExtTest.Combinatorics.SimpleGraph.RandomGraphTriangleThreshold

/-- First moment bound for `G(10, 1/2)`: at most `C(10, 3)/8 = 15`, a vacuous but valid bound. -/
example : (randomSubsetLaw (fun _ : Pair 10 => (⟨1 / 2, by norm_num, by norm_num⟩ : I))).real
    {ω | ¬ (pairGraph ω).CliqueFree 3} ≤ ((10 : ℕ).choose 3 : ℝ) * (1 / 2) ^ 3 :=
  measureReal_not_cliqueFree_three_le _

/-- Second moment bound for `G(n, 1)`: the complete graph on `n ≥ 3` vertices has a triangle,
and the bound `(1 + 3n) / C(n, 3)` is valid. -/
example (n : ℕ) (hn : 3 ≤ n) :
    (randomSubsetLaw (fun _ : Pair n => (1 : I))).real {ω | (pairGraph ω).CliqueFree 3} ≤
      (1 + 3 * n * ((1 : I) : ℝ) ^ 2) / ((n.choose 3 : ℝ) * ((1 : I) : ℝ) ^ 3) :=
  measureReal_cliqueFree_three_le 1 (by simp) hn

/-- Below the threshold: with `pₙ = 1/(n + 1)²`, `n pₙ → 0`, so triangles are absent whp. -/
example (p : ℕ → I) (hp : ∀ n, (p n : ℝ) = 1 / ((n : ℝ) + 1) ^ 2) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | ¬ (pairGraph ω).CliqueFree 3}) atTop (nhds 0) := by
  refine tendsto_measureReal_not_cliqueFree_three_of_tendsto_zero p ?_
  have h : ∀ n : ℕ, (n : ℝ) * p n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    rw [hp n, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h0 : ∀ n : ℕ, 0 ≤ (n : ℝ) * p n := fun n => mul_nonneg (Nat.cast_nonneg n) (p n).2.1
  exact squeeze_zero h0 h tendsto_one_div_add_atTop_nhds_zero_nat

/-- Above the threshold: the constant `p = 1/2` has `n p → ∞`, so triangles appear whp. -/
example : Tendsto (fun n : ℕ => (randomSubsetLaw
      (fun _ : Pair n => (⟨1 / 2, by norm_num, by norm_num⟩ : I))).real
      {ω | ¬ (pairGraph ω).CliqueFree 3}) atTop (nhds 1) := by
  refine tendsto_measureReal_not_cliqueFree_three_of_tendsto_atTop
    (fun _ => ⟨1 / 2, by norm_num, by norm_num⟩) ?_
  simpa using tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)

end MathlibExtTest.Combinatorics.SimpleGraph.RandomGraphTriangleThreshold
