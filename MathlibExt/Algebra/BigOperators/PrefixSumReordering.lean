/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Reordering pairs to compare all prefix sums

Sorting the differences in increasing order puts all nonpositive differences first.
-/

namespace MetaMathlibExt

/-- **Reordering so that prefix sums compare.** Let $k$ be a natural number and let
$x_1, \dots, x_k$ and $y_1, \dots, y_k$ be real numbers with $\sum_i x_i \le \sum_i y_i$. Then
there is a permutation $\sigma$ of $\{1, \dots, k\}$ such that
$\sum_{i \le s} x_{\sigma(i)} \le \sum_{i \le s} y_{\sigma(i)}$ for every $s$ with $0 \le s \le k$.

No positivity of the $x_i$ or $y_i$ is assumed.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 2 (`integers-2026-A115-lem-2`). -/
public theorem exists_perm_prefix_sum_le {k : ℕ} (x y : Fin k → ℝ)
    (h : ∑ i, x i ≤ ∑ i, y i) :
    ∃ σ : Equiv.Perm (Fin k), ∀ s ≤ k,
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < s), x (σ i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < s), y (σ i) := by
  classical
  let d (i : Fin k) := x i - y i
  let σ := Tuple.sort d
  refine ⟨σ, fun s _ => ?_⟩
  rw [← sub_nonpos, ← Finset.sum_sub_distrib]
  let initial := Finset.univ.filter (fun i : Fin k => i.val < s)
  change ∑ i ∈ initial, d (σ i) ≤ 0
  by_cases hpos : ∃ i : Fin k, i.val < s ∧ 0 < d (σ i)
  · obtain ⟨i, hi, hd⟩ := hpos
    calc
      ∑ j ∈ initial, d (σ j) ≤ ∑ j, d (σ j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ initial)
        intro j _ hj
        have hsj : s ≤ j.val := by simpa [initial] using hj
        exact hd.le.trans (Tuple.monotone_sort d (Fin.le_def.mpr (hi.le.trans hsj)))
      _ = ∑ j, d j := Equiv.sum_comp σ d
      _ ≤ 0 := by simpa [d, Finset.sum_sub_distrib] using sub_nonpos.mpr h
  · apply Finset.sum_nonpos
    intro i hi
    exact le_of_not_gt fun hd => hpos ⟨i, (Finset.mem_filter.mp hi).2, hd⟩

end MetaMathlibExt
