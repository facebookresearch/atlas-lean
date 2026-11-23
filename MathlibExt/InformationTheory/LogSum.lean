/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The log-sum inequality

For `p ≥ 0` and `q > 0` on a finset `s`,
`(∑ i ∈ s, p i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i) ≤ ∑ i ∈ s, p i * log (p i / q i)`.
The proof is Jensen's inequality for the convex function `x ↦ x * log x` with weights
`q i / ∑ j ∈ s, q j` at the points `p i / q i`.
-/

public section

open Finset

namespace Real

/-- **Log-sum inequality.** Let $s$ be a finite subset of a type $\iota$ and let
$p, q : \iota \to \mathbb{R}$ satisfy $p_i \ge 0$ and $q_i > 0$ for all $i \in s$. Then
$$
\Bigl(\sum_{i \in s} p_i\Bigr) \log \frac{\sum_{i \in s} p_i}{\sum_{i \in s} q_i}
\le \sum_{i \in s} p_i \log \frac{p_i}{q_i}.
$$

Here $\log$ is the natural logarithm; a summand with $p_i = 0$ is $0$, and both sides are $0$
when $s$ is empty. -/
theorem sum_mul_log_sum_div_sum_le_sum_mul_log_div {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i) :
    (∑ i ∈ s, p i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
      ≤ ∑ i ∈ s, p i * log (p i / q i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hQ : 0 < ∑ i ∈ s, q i := sum_pos hq hs
  have hJ := convexOn_mul_log.map_sum_le (t := s) (w := fun i => q i / ∑ j ∈ s, q j)
    (p := fun i => p i / q i) (fun i hi => (div_pos (hq i hi) hQ).le)
    (by rw [← sum_div, div_self hQ.ne'])
    (fun i hi => Set.mem_Ici.2 (div_nonneg (hp i hi) (hq i hi).le))
  have h1 : ∑ i ∈ s, (q i / ∑ j ∈ s, q j) • (p i / q i)
      = (∑ i ∈ s, p i) / ∑ i ∈ s, q i := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    have := (hq i hi).ne'
    rw [smul_eq_mul]
    field_simp
  have h2 : ∑ i ∈ s, (q i / ∑ j ∈ s, q j) • (p i / q i * log (p i / q i))
      = (∑ i ∈ s, p i * log (p i / q i)) / ∑ i ∈ s, q i := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    have := (hq i hi).ne'
    rw [smul_eq_mul]
    field_simp
  simp only [h1, h2] at hJ
  rw [le_div_iff₀ hQ] at hJ
  calc (∑ i ∈ s, p i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
      = (∑ i ∈ s, p i) / (∑ i ∈ s, q i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
        * ∑ i ∈ s, q i := by field_simp
    _ ≤ _ := hJ

end Real
