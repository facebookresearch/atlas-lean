/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.LinearRecurrenceLogBehavior

/-!
# Log-behavior of sequences related to A005773

Statements from Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear
Recurrence Sequence*, INTEGERS 25 (2025), Article A100.

Every statement is about a real sequence `A` with `A 0 = A 1 = 1` and
`(n + 1) A (n + 1) = 2 (n + 1) A n + 3 (n - 1) A (n - 1)` for `n ≥ 1` (the paper's
recurrence (1); OEIS A005773, `1, 1, 2, 5, 13, 35, …`). Forward differences are written out:
`ΔA n = A (n + 1) - A n`, `Δ²A n = A (n + 2) - 2 A (n + 1) + A n`,
`Δ³A n = A (n + 3) - 3 A (n + 2) + 3 A (n + 1) - A n`. A sequence `(z n)_{n ≥ m}` is
log-convex (log-concave) if `z n ^ 2 ≤ z (n - 1) z (n + 1)` (`≥`) for every `n ≥ m + 1`, and
log-balanced (Došlić) if it is log-convex and `(z n / n!)_{n ≥ m}` is log-concave.

Proved in `MathlibExt.Combinatorics.Enumerative.LinearRecurrenceLogBehavior`: Lemma 1
(`MetaMathlibExt.a005773Recurrence_ratio_bounds`), Theorem 2 on third differences
(`MetaMathlibExt.a005773Recurrence_thirdDiff_logConvex_logBalanced`), the weighted log-concavity
result (`MetaMathlibExt.a005773Recurrence_weighted_logConcave`), and Theorem 4
(`MetaMathlibExt.a005773Recurrence_pow_logConvex`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The first and second differences of A005773 are log-balanced.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$\Delta A_n = A_{n+1} - A_n$ and $\Delta^2 A_n = A_{n+2} - 2A_{n+1} + A_n$. Then for every
$n \ge 4$, each of the sequences $z = \Delta A$ and $z = \Delta^2 A$ satisfies
$z_n^2 \le z_{n-1} z_{n+1}$ and
$$\frac{z_{n-1}}{(n-1)!} \cdot \frac{z_{n+1}}{(n+1)!} \le \left(\frac{z_n}{n!}\right)^2.$$
That is, $(\Delta A_n)_{n \ge 3}$ and $(\Delta^2 A_n)_{n \ge 3}$ are log-balanced: log-convex, with
$(z_n / n!)_{n \ge 3}$ log-concave.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 1. -/
public theorem_wanted a005773Recurrence_diff_logBalanced (A : ℕ → ℝ) (h0 : A 0 = 1)
    (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) (hn : 4 ≤ n) :
    let D₁ : ℕ → ℝ := fun m => A (m + 1) - A m
    let D₂ : ℕ → ℝ := fun m => A (m + 2) - 2 * A (m + 1) + A m
    (D₁ n ^ 2 ≤ D₁ (n - 1) * D₁ (n + 1) ∧
        D₁ (n - 1) / (n - 1).factorial * (D₁ (n + 1) / (n + 1).factorial) ≤
          (D₁ n / n.factorial) ^ 2) ∧
      D₂ n ^ 2 ≤ D₂ (n - 1) * D₂ (n + 1) ∧
        D₂ (n - 1) / (n - 1).factorial * (D₂ (n + 1) / (n + 1).factorial) ≤
          (D₂ n / n.factorial) ^ 2

end

end MetaMathlibExt
