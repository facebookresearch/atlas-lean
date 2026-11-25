/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry10Example1SummableEventually

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 10, Example 1

Eventual positivity of ∑ xʲ⁺¹√(j+1)/(j+1)!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example1SumPositiveEventually

/-- **Eventual positivity of the square-root Poisson series.** For all sufficiently large
real $x$, the sum $\sum_{k=1}^{\infty} x^k \sqrt{k} / k!$ is strictly positive.

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example1_sum_positive_eventually`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 1, printed p.
    64 / PDF p. 74.
-/
theorem ramanujan_part1_ch3_entry10_example1_sum_positive_eventually :
    ∀ᶠ (x : ℝ) in Filter.atTop, 0 < ∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1)) /
        (↑(Nat.factorial (j + 1)) : ℝ) := by
  filter_upwards [
    Entry10Example1SummableEventually.ramanujan_part1_ch3_entry10_example1_summable_eventually,
    Filter.eventually_gt_atTop 0] with x hs hx
  refine hs.tsum_pos (fun j => by positivity) 0 ?_
  apply div_pos
  · apply mul_pos (pow_pos hx (0 + 1))
    exact Real.sqrt_pos.mpr (by positivity)
  · exact_mod_cast Nat.factorial_pos (0 + 1)

end Entry10Example1SumPositiveEventually

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
