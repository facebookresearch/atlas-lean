/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# Power sums over a symmetric integer interval

Increasing the radius by one adds two opposite endpoints. Their odd powers cancel,
and their even powers give the increments of the two polynomial formulas.
-/

namespace MetaMathlibExt

/-- **Power sums over a symmetric interval.** For natural numbers $N$ and $r$, let
$S_r(N) = \sum_{a=-N}^{N} a^r$, the sum over the integers $a$ with $-N \le a \le N$. Then
$S_r(N) = 0$ for every odd $r$, and
$$S_2(N) = \frac{N(N+1)(2N+1)}{3}, \qquad S_4(N) = \frac{N(N+1)(2N+1)(3N^2+3N-1)}{15}.$$

The paper takes $N \ge 1$; here $N = 0$ is allowed.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 3 (`integers-2025-A10-lem-3`). -/
public theorem symmetric_power_sums (N : ℕ) :
    (∀ r : ℕ, Odd r → ∑ a ∈ Finset.Icc (-(N : ℤ)) N, a ^ r = 0) ∧
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, (a : ℚ) ^ 2 = N * (N + 1) * (2 * N + 1) / 3 ∧
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, (a : ℚ) ^ 4 =
      N * (N + 1) * (2 * N + 1) * (3 * N ^ 2 + 3 * N - 1) / 15 := by
  induction N with
  | zero =>
    refine ⟨?_, by simp, by simp⟩
    rintro r ⟨k, rfl⟩
    simp
  | succ N ih =>
    obtain ⟨hodd, h₂, h₄⟩ := ih
    simp only [Nat.cast_succ]
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rw [Finset.sum_Icc_succ_eq_add_endpoints (fun a : ℤ => a ^ r), hodd r hr]
      simp only [hr.neg_pow, add_neg_cancel, add_zero]
    · rw [Finset.sum_Icc_succ_eq_add_endpoints (fun a : ℤ => (a : ℚ) ^ 2), h₂]
      push_cast
      ring
    · rw [Finset.sum_Icc_succ_eq_add_endpoints (fun a : ℤ => (a : ℚ) ^ 4), h₄]
      push_cast
      ring

end MetaMathlibExt
