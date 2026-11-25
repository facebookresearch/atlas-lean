/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices

@[expose] public section

open MeasureTheory Filter Topology unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound
  MathlibExt.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices

namespace MathlibExtTest.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices

/-- Every vertex of `K_5` has the four pairs at it. -/
example (v : Fin 5) : (pairsAt v).card = 4 := card_pairsAt v

/-- In `G(n, 1) = K_n` with `n ≥ 2` no vertex is isolated. -/
example (n : ℕ) (hn : 2 ≤ n) (v : Fin n) :
    (randomSubsetLaw (fun _ : Pair n => (1 : I))).real
      {ω | ∀ w, ¬ (pairGraph ω).Adj v w} = 0 := by
  rw [measureReal_isolated]
  simp only [Set.Icc.coe_one, sub_self]
  exact zero_pow (by omega)

/-- In `G(n, 0)`, the empty graph, every vertex is isolated. -/
example (n : ℕ) (v : Fin n) :
    (randomSubsetLaw (fun _ : Pair n => (0 : I))).real
      {ω | ∀ w, ¬ (pairGraph ω).Adj v w} = 1 := by
  rw [measureReal_isolated]
  simp

/-- The hypotheses of the threshold statements are satisfiable, and along such a sequence the
expected number of isolated vertices tends to `e^{-c}`; at `c = 0` the limit is `1`. -/
example : ∃ p : ℕ → I, Tendsto (fun n : ℕ => (n : ℝ) * (1 - (p n : ℝ)) ^ (n - 1)) atTop
    (𝓝 1) := by
  obtain ⟨p, hp⟩ := exists_prob_eventually_eq 0
  refine ⟨p, ?_⟩
  simpa using tendsto_mul_one_sub_pow 0 (fun n => (p n : ℝ))
    (tendsto_mul_sub_log_of_eventually_eq 0 _ hp)

/-- The first moment bound along the threshold sequence with `c = 0`: eventually the
probability of an isolated vertex is at most `1 + 1/2`. -/
example : ∃ p : ℕ → I, ∀ᶠ n : ℕ in atTop, (randomSubsetLaw (fun _ : Pair n => p n)).real
    {ω | ∃ v, ∀ w, ¬ (pairGraph ω).Adj v w} ≤ Real.exp (-0) + 1 / 2 := by
  obtain ⟨p, hp⟩ := exists_prob_eventually_eq 0
  exact ⟨p, eventually_measureReal_exists_isolated_le 0 p
    (tendsto_mul_sub_log_of_eventually_eq 0 _ hp) (by norm_num)⟩

/-- The general hypothesis `n pₙ - log n → c` also covers sequences not of the exact form, such
as `pₙ = (log n + c + 1/n)/n`. -/
example (c : ℝ) (p : ℕ → ℝ) (hp : ∀ᶠ n : ℕ in atTop, p n = (Real.log n + c + 1 / n) / n) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - p n) ^ (n - 1)) atTop (𝓝 (Real.exp (-c))) := by
  refine tendsto_mul_one_sub_pow c p ?_
  have h : Tendsto (fun n : ℕ => c + 1 / (n : ℝ)) atTop (𝓝 c) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.const_add c
  refine h.congr' ?_
  filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [hpn]
  field_simp
  ring

end MathlibExtTest.Combinatorics.SimpleGraph.RandomGraphIsolatedVertices
