/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
import MathlibExt.Combinatorics.Enumerative.BellTuranIdentity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace MetaMathlibExt

/-- **Engel's inequality for Bell numbers.** For every integer $n \ge 1$, the Bell numbers
satisfy $B_n^2 \le B_{n-1} B_{n+1}$, where $B_n$ is the number of partitions of an $n$-element
set.

This non-strict inequality is Eq. (E2) of Horst Alzer, "On Engel's Inequality for Bell
Numbers," Journal of Integer Sequences 22 (2019); Alzer's strict refinement is a different
result.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL22/Alzer/alzer6.tex>,
lines 79--104, where `B_n` is defined as the Bell number and Eq. (E2) states
`B_n^2 ≤ B_{n-1} B_{n+1}` for every integer `n ≥ 1`.
Source file SHA-256:
`03a0712f6a473227541845886072d039e644d950ee6f591a456b1cffcd1b9f46`.
The source attributes this inequality to K. Engel, "On the average rank of an
element in a filter of the partition lattice," J. Combin. Theory Ser. A 65
(1994), 67--78.
-/
theorem engel_bell_log_convexity (n : ℕ) (hn : 1 ≤ n) :
    (Nat.bell n) ^ 2 ≤ Nat.bell (n - 1) * Nat.bell (n + 1) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    norm_num [Nat.bell_zero, Nat.bell_one, Nat.bell_two]
  · have h : (Nat.bell n : ℝ) ^ 2 ≤ (Nat.bell (n - 1) : ℝ) * (Nat.bell (n + 1) : ℝ) := by
      rw [← sub_nonneg, bell_turan_identity n h2]
      exact mul_nonneg (by positivity)
        (tsum_nonneg fun k => Finset.sum_nonneg fun j _ => by positivity)
    exact_mod_cast h

end MetaMathlibExt
