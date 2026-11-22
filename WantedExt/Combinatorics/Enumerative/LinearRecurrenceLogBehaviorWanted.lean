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
-/

namespace MetaMathlibExt

@[expose] public section

/-- With `x n = A (n + 1) / A n` and `φ n = 3 (2n + 1) / (2 (n + 1))`, for every `n ≥ 0`:
`x n ≤ φ n` (2) and `x (n + 1) / x n ≥ 2 (3n² + 6n + 2) / ((n + 2)(2n + 1) φ n)` (3).

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Lemma 1. -/
public theorem_wanted a005773Recurrence_ratio_bounds (A : ℕ → ℝ) (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    A (n + 1) / A n ≤ 3 * (2 * n + 1) / (2 * (n + 1)) ∧
      2 * (3 * (n : ℝ) ^ 2 + 6 * n + 2) / ((n + 2) * (2 * n + 1) * (3 * (2 * n + 1) / (2 * (n + 1))))
        ≤ (A (n + 2) / A (n + 1)) / (A (n + 1) / A n)

/-- The sequences `(ΔA n)_{n ≥ 3}` and `(Δ²A n)_{n ≥ 3}` are log-balanced: for every `n ≥ 4`,
both satisfy `z n ^ 2 ≤ z (n - 1) z (n + 1)` and
`(z (n - 1) / (n - 1)!) (z (n + 1) / (n + 1)!) ≤ (z n / n!) ^ 2`.

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

/-- `(Δ³A n)_{n ≥ 2}` is log-convex (`z n ^ 2 ≤ z (n - 1) z (n + 1)` for `n ≥ 3`) and
`(Δ³A n)_{n ≥ 3}` is log-balanced (additionally
`(z (n - 1) / (n - 1)!) (z (n + 1) / (n + 1)!) ≤ (z n / n!) ^ 2` for `n ≥ 4`).

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 2. -/
public theorem_wanted a005773Recurrence_thirdDiff_logConvex_logBalanced (A : ℕ → ℝ)
    (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1)) :
    let D₃ : ℕ → ℝ := fun m => A (m + 3) - 3 * A (m + 2) + 3 * A (m + 1) - A m
    (∀ n, 3 ≤ n → D₃ n ^ 2 ≤ D₃ (n - 1) * D₃ (n + 1)) ∧
      ∀ n, 4 ≤ n →
        D₃ (n - 1) / (n - 1).factorial * (D₃ (n + 1) / (n + 1).factorial) ≤
          (D₃ n / n.factorial) ^ 2

/-- The sequences `(n A n)_{n ≥ 1}`, `(Δ(n A n))_{n ≥ 1}`, `(n ΔA n)_{n ≥ 1}` and
`(n Δ²A n)_{n ≥ 1}` are log-concave: `z (n - 1) z (n + 1) ≤ z n ^ 2` for every `n ≥ 2`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 3. -/
public theorem_wanted a005773Recurrence_weighted_logConcave (A : ℕ → ℝ) (h0 : A 0 = 1)
    (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) (hn : 2 ≤ n) :
    let W : ℕ → ℝ := fun m => m * A m
    let V : ℕ → ℝ := fun m => (m + 1 : ℕ) * A (m + 1) - m * A m
    let U : ℕ → ℝ := fun m => m * (A (m + 1) - A m)
    let T : ℕ → ℝ := fun m => m * (A (m + 2) - 2 * A (m + 1) + A m)
    W (n - 1) * W (n + 1) ≤ W n ^ 2 ∧ V (n - 1) * V (n + 1) ≤ V n ^ 2 ∧
      U (n - 1) * U (n + 1) ≤ U n ^ 2 ∧ T (n - 1) * T (n + 1) ≤ T n ^ 2

/-- The sequence `(nⁿ A nⁿ)_{n ≥ 1} = ((n A n)ⁿ)_{n ≥ 1}` is log-convex:
`z n ^ 2 ≤ z (n - 1) z (n + 1)` for every `n ≥ 2`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 4. -/
public theorem_wanted a005773Recurrence_pow_logConvex (A : ℕ → ℝ) (h0 : A 0 = 1)
    (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) (hn : 2 ≤ n) :
    let z : ℕ → ℝ := fun m => ((m : ℝ) * A m) ^ m
    z n ^ 2 ≤ z (n - 1) * z (n + 1)

end

end MetaMathlibExt
