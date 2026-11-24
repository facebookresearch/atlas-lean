/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LinearRecurrenceLogBehavior
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.LinearRecurrenceLogBehavior` -/

namespace MetaMathlibExt

/-- The sequence defined by `A 0 = A 1 = 1` and the recurrence, solved for its last term. -/
private noncomputable def a005773Seq : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => (2 * ((n : ℝ) + 2) * a005773Seq (n + 1) + 3 * n * a005773Seq n) / ((n : ℝ) + 2)

private theorem a005773Seq_rec : ∀ n : ℕ, 1 ≤ n →
    ((n : ℝ) + 1) * a005773Seq (n + 1) =
      2 * ((n : ℝ) + 1) * a005773Seq n + 3 * ((n : ℝ) - 1) * a005773Seq (n - 1) := by
  rintro (_ | m) hm
  · omega
  · rw [a005773Seq, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

-- Test section: the hypotheses are satisfiable, by the sequence `1, 1, 2, 5, 13, 35, …`
-- (OEIS A005773), so the theorem applies to it for every `n`.
example : a005773Seq 2 = 2 ∧ a005773Seq 3 = 5 ∧ a005773Seq 4 = 13 ∧ a005773Seq 5 = 35 := by
  norm_num [a005773Seq]

example (n : ℕ) : a005773Seq (n + 1) / a005773Seq n ≤ 3 * (2 * n + 1) / (2 * (n + 1)) :=
  (a005773Recurrence_ratio_bounds a005773Seq (by simp [a005773Seq]) (by simp [a005773Seq])
    a005773Seq_rec n).1

-- Test section: both bounds are equalities at `n = 2`, where `x 2 = 5 / 2` and
-- `x 3 / x 2 = 26 / 25`, so neither inequality is strict for every `n`.
example :
    a005773Seq 3 / a005773Seq 2 = 3 * (2 * ((2 : ℕ) : ℝ) + 1) / (2 * (((2 : ℕ) : ℝ) + 1)) := by
  norm_num [a005773Seq]

example : 2 * (3 * ((2 : ℕ) : ℝ) ^ 2 + 6 * ((2 : ℕ) : ℝ) + 2) /
      ((((2 : ℕ) : ℝ) + 2) * (2 * ((2 : ℕ) : ℝ) + 1) *
        (3 * (2 * ((2 : ℕ) : ℝ) + 1) / (2 * (((2 : ℕ) : ℝ) + 1)))) =
      (a005773Seq 4 / a005773Seq 3) / (a005773Seq 3 / a005773Seq 2) := by
  norm_num [a005773Seq]

-- Test section: a consequence for an arbitrary solution, `A (n + 1) / A n < 3` for every `n`.
example (A : ℕ → ℝ) (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) : A (n + 1) / A n < 3 := by
  refine (a005773Recurrence_ratio_bounds A h0 h1 hrec n).1.trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  linarith

-- At the first admissible index, the neighboring powered terms are 1, 16, and 3375.
example :
    let z (m : ℕ) := ((m : ℝ) * a005773Seq m) ^ m
    z 1 = 1 ∧ z 2 = 16 ∧ z 3 = 3375 ∧ z 2 ^ 2 ≤ z 1 * z 3 := by
  refine ⟨?_, ?_, ?_, a005773Recurrence_pow_logConvex a005773Seq rfl rfl a005773Seq_rec 2
    (by decide)⟩ <;> norm_num [a005773Seq]

-- The lower bound n = 2 is sharp for the differences of the weighted terms.
-- Their first four values are 1, 3, 11, 37, so log-concavity fails at n = 1.
example :
    let v (m : ℕ) := (m + 1 : ℕ) * a005773Seq (m + 1) - m * a005773Seq m
    v 1 ^ 2 < v 0 * v 2 ∧ v 1 * v 3 ≤ v 2 ^ 2 := by
  refine ⟨?_, (a005773Recurrence_weighted_logConcave a005773Seq rfl rfl a005773Seq_rec 2
    (by decide)).2.1⟩
  norm_num [a005773Seq]

end MetaMathlibExt
