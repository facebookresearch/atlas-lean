/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MathlibExt.NumberTheory.HataEulerMascheroniFareySum

namespace MetaMathlibExt

-- The first reciprocal interval has left endpoint 1/2 and right endpoint 1.
example : HasSum
    (fun q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
        b * c = a * d + 1 ∧ b ≤ 2 * a ∧ 1 * c ≤ d} =>
      match q.1 with
      | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d)))
    (3 / 2 - 2 * Real.log 2) := by
  convert hasSum_farey_subintervals_reciprocal_interval (n := 1) (by decide) using 1
  norm_num

-- In the interval [1/3, 1/2], the root and its left child both contribute.
example : (13 : ℝ) / 720 ≤ 5 / 6 - 2 * Real.log (3 / 2) := by
  classical
  let Q := {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | b * c = a * d + 1 ∧ b ≤ 3 * a ∧ 2 * c ≤ d}
  let r : Q := ⟨(1, 3, 1, 2), by decide⟩
  let l : Q := ⟨(1, 3, 2, 5), by decide⟩
  let f (q : Q) : ℝ := match q.1 with
    | (a, b, c, d) => 1 / (a * b * c * d * (a + c) * (b + d))
  have h : HasSum f (5 / 6 - 2 * Real.log (3 / 2)) := by
    convert hasSum_farey_subintervals_reciprocal_interval (n := 2) (by decide) using 1
    norm_num
  have hrl : r ≠ l := by decide
  have hnonneg (q : Q) : 0 ≤ f q := by
    obtain ⟨⟨a, b, c, d⟩, _⟩ := q
    unfold f
    positivity
  have hsum := h.summable.sum_le_tsum ({r, l} : Finset Q) (fun q _ => hnonneg q)
  rw [h.tsum_eq, Finset.sum_pair hrl] at hsum
  norm_num [f, r, l] at hsum
  exact hsum

end MetaMathlibExt
