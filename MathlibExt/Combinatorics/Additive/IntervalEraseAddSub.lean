/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval

/-!
# Sums and differences of an interval with one point removed

The interval identities are Lemma 2.4 of Herrmann, Hill, Phillips, Flores, Miller and Senger,
*Additional Constructions of Sequences of Alternating Sum and Difference Dominated Sets*
(https://arxiv.org/html/2509.12829v1).
-/

namespace MetaMathlibExt

open scoped Pointwise

/-- **Sums and differences of an interval with one point removed.** Let $m$ and $r$ be integers
with $m \ge 4$ and $2 \le r \le m - 3$, and let $B = \{0, 1, \dots, m - 1\} \setminus \{r\}$. Then
the sumset $B + B = \{b + b' : b, b' \in B\}$ is $\{0, 1, \dots, 2m - 2\}$ and the difference set
$B - B = \{b - b' : b, b' \in B\}$ is the set of integers from $-(m - 1)$ to $m - 1$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Lemma 1 (`integers-2026-A88-lem-1`). -/
public theorem interval_erase_add_sub {m r : ℤ} (hm : 4 ≤ m) (hr : 2 ≤ r)
    (hrm : r ≤ m - 3) :
    (Finset.Icc 0 (m - 1)).erase r + (Finset.Icc 0 (m - 1)).erase r = Finset.Icc 0 (2 * m - 2) ∧
      (Finset.Icc 0 (m - 1)).erase r - (Finset.Icc 0 (m - 1)).erase r =
        Finset.Icc (-(m - 1)) (m - 1) := by
  constructor
  · ext x
    simp only [Finset.mem_add, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      omega
    · intro hx
      -- Use an endpoint as one summand, moving it one step inward if its partner is erased.
      by_cases hlow : x ≤ m - 1
      · by_cases h : x = r
        · exact ⟨1, by omega, r - 1, by omega, by omega⟩
        · exact ⟨0, by omega, x, by omega, zero_add x⟩
      · by_cases h : x - (m - 1) = r
        · exact ⟨m - 2, by omega, r + 1, by omega, by omega⟩
        · exact ⟨m - 1, by omega, x - (m - 1), by omega, by omega⟩
  · ext x
    simp only [Finset.mem_sub, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      omega
    · intro hx
      -- A difference of magnitude r is represented by (r + 1) - 1 or its negative.
      by_cases hnonneg : 0 ≤ x
      · by_cases h : x = r
        · exact ⟨r + 1, by omega, 1, by omega, by omega⟩
        · exact ⟨x, by omega, 0, by omega, sub_zero x⟩
      · by_cases h : -x = r
        · exact ⟨1, by omega, r + 1, by omega, by omega⟩
        · exact ⟨0, by omega, -x, by omega, by omega⟩

end MetaMathlibExt
