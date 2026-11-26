/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import MathlibExt.NumberTheory.Bernoulli.KanekoBernoulliStirling

/-!
# Bernoulli numbers via Stirling numbers of the second kind

Farhi's formula expresses each Bernoulli number as an alternating sum of weighted Stirling numbers.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

/-- **Bernoulli numbers via Stirling numbers of the second kind.** Let $B_m$ be the Bernoulli
numbers (with $B_1 = -1/2$) and $S(m, j)$ the Stirling numbers of the second kind. For every
natural number $n$,
$$B_n = \sum_{i=0}^{n} (-1)^i \, \frac{i!}{i+1} \, S(n, i).$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 9. -/
public theorem bernoulli_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℚ) ^ i *
        ((i.factorial : ℚ) / (i + 1)) *
        (Nat.stirlingSecond n i : ℚ) := by
  rw [MetaMathlibExt.kaneko_bernoulli_stirling_sum, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1, Nat.cast_add, Nat.cast_one]
  exact Finset.sum_congr rfl fun i _ => by ring

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
