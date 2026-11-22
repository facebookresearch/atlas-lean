/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Rogers dilogarithm series of Hoorfar--Qi, Bridgeman, and Sanford

Statement-only targets from Chance Sanford, *A Dilogarithm Series and a Generalization of a
Theorem of Bridgeman*, INTEGERS 25 (2025), Article A52 (texts checked against
arXiv:2410.21619v2). Each statement writes the Rogers dilogarithm inline as
`L x = ∑_{n ≥ 1} xⁿ/n² + (log x · log (1 - x))/2`; on `[0, 1]` this is the paper's `L`, including
`L 0 = 0` and `L 1 = π²/6` (Lean's `log 0 = 0`), and every argument below lies in `[0, 1]`.
-/

open Real

namespace MetaMathlibExt

@[expose] public section

/-- Hoorfar and Qi's two-parameter series: for positive integers `p, q` and `0 < θ, β < 1`,
`∑_{n ≥ 0} L(β(1 - θ^p)(1 - θ^q)θⁿ / ((1 - βθ^{n+p})(1 - βθ^{n+q})))
  = ∑_{n < q} L(β(1 - θ^p)θⁿ/(1 - βθ^{n+p})) + ∑_{n < p} L((1 - θ^q)/(1 - βθ^{n+q}))
    - p L(1 - θ^q)`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 1, quoting Hoorfar and Qi (`integers-2025-A52-thm-1`). -/
public theorem_wanted rogersDilog_hoorfarQi_series {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {θ β : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (β * (1 - θ ^ p) * (1 - θ ^ q) * θ ^ n /
        ((1 - β * θ ^ (n + p)) * (1 - β * θ ^ (n + q)))) =
      ∑ n ∈ Finset.range q, L (β * (1 - θ ^ p) * θ ^ n / (1 - β * θ ^ (n + p))) +
        ∑ n ∈ Finset.range p, L ((1 - θ ^ q) / (1 - β * θ ^ (n + q))) - p * L (1 - θ ^ q)

/-- Bridgeman's series for a positive Pell solution: let `n` be a positive non-square integer and
`u = a + b√n` with rationals `a, b > 0` and `a² - n b² = 1`, and let `u^k = a_k + b_k √n` (the
sequences `A, B` given by the multiplication recurrence). Then
`L(1/u²) = ∑_{k ≥ 2} L(b²/b_k²)`, and if `a, b` are integers then `b ∣ b_k` for every `k`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 3 (3), quoting Bridgeman (`integers-2025-A52-thm-3`). -/
public theorem_wanted rogersDilog_pell_positive_series {n : ℕ} (hn : ¬ IsSquare n) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hpell : a ^ 2 - n * b ^ 2 = 1) {A B : ℕ → ℚ}
    (hA₀ : A 0 = 1) (hB₀ : B 0 = 0) (hA : ∀ k, A (k + 1) = a * A k + n * b * B k)
    (hB : ∀ k, B (k + 1) = b * A k + a * B k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / ((a : ℝ) + b * √n) ^ 2) = ∑' k : ℕ, L ((b : ℝ) ^ 2 / (B (k + 2) : ℝ) ^ 2) ∧
      ((∃ a' b' : ℤ, a = a' ∧ b = b') → ∀ k, ∃ m : ℤ, B k = b * m)

/-- Bridgeman's series for a negative Pell solution: with `n`, `u = a + b√n`, `a_k`, `b_k` as in
the positive case but `a² - n b² = -1`,
`L(1/u²) = ∑_{k ≥ 1} L(a²/(n b_{2k}²)) + ∑_{k ≥ 1} L(a²/a_{2k+1}²)`, and if `a, b` are integers
then `b_{2k}/a` and `a_{2k+1}/a` are integers for every `k`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 3 (4), quoting Bridgeman (`integers-2025-A52-thm-3`). -/
public theorem_wanted rogersDilog_pell_negative_series {n : ℕ} (hn : ¬ IsSquare n) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hpell : a ^ 2 - n * b ^ 2 = -1) {A B : ℕ → ℚ}
    (hA₀ : A 0 = 1) (hB₀ : B 0 = 0) (hA : ∀ k, A (k + 1) = a * A k + n * b * B k)
    (hB : ∀ k, B (k + 1) = b * A k + a * B k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / ((a : ℝ) + b * √n) ^ 2) =
        ∑' k : ℕ, L ((a : ℝ) ^ 2 / (n * (B (2 * (k + 1)) : ℝ) ^ 2)) +
          ∑' k : ℕ, L ((a : ℝ) ^ 2 / (A (2 * (k + 1) + 1) : ℝ) ^ 2) ∧
      ((∃ a' b' : ℤ, a = a' ∧ b = b') →
        ∀ k, (∃ m : ℤ, B (2 * k) = a * m) ∧ ∃ m : ℤ, A (2 * k + 1) = a * m)

/-- Sanford's coupled recurrence: for `a, b ∈ (0, 1)` with `a ≠ b`, the sequences
`x_n = a(a - b)(1 - b)ⁿ / (a(1 - b)^{n+1} - b(1 - a)^{n+1})` and
`y_n = b(a - b)(1 - a)ⁿ / (a(1 - b)^{n+1} - b(1 - a)^{n+1})` satisfy
`x_{n+1} = x_n(1 - y_n)/(1 - x_n y_n)` and `y_{n+1} = y_n(1 - x_n)/(1 - x_n y_n)`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Lemma 1 (`integers-2025-A52-lem-1`). -/
public theorem_wanted sanford_coupled_recurrence {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (hab : a ≠ b) (n : ℕ) :
    let x : ℕ → ℝ := fun m =>
      a * (a - b) * (1 - b) ^ m / (a * (1 - b) ^ (m + 1) - b * (1 - a) ^ (m + 1))
    let y : ℕ → ℝ := fun m =>
      b * (a - b) * (1 - a) ^ m / (a * (1 - b) ^ (m + 1) - b * (1 - a) ^ (m + 1))
    x (n + 1) = x n * (1 - y n) / (1 - x n * y n) ∧ y (n + 1) = y n * (1 - x n) / (1 - x n * y n)

/-- Sanford's principal identity: for `a, b ∈ (0, 1)` with `a ≠ b`,
`∑_{n ≥ 0} L(ab(a - b)²(1 - a)ⁿ(1 - b)ⁿ / (a(1 - b)^{n+1} - b(1 - a)^{n+1})²)
  = L(a) + L(b) - L(|a - b|/(1 - min(a, b)))`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 4 (`integers-2025-A52-thm-4`). -/
public theorem_wanted rogersDilog_sanford_principal_series {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (hb₀ : 0 < b) (hb₁ : b < 1) (hab : a ≠ b) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (a * b * (a - b) ^ 2 * (1 - a) ^ n * (1 - b) ^ n /
        (a * (1 - b) ^ (n + 1) - b * (1 - a) ^ (n + 1)) ^ 2) =
      L a + L b - L (|a - b| / (1 - min a b))

/-- The symmetric specialization `a ↦ 1/2 + a/2`, `b ↦ 1/2 - a/2`: for `a ∈ (0, 1)`,
`∑_{n ≥ 1} L(a²(1/2 - a/2)ⁿ(1/2 + a/2)ⁿ / ((1/2 + a/2)^{n+1} - (1/2 - a/2)^{n+1})²)
  = L((1 - a)/(1 + a))`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Corollary 1 (`integers-2025-A52-cor-1`). -/
public theorem_wanted rogersDilog_sanford_symmetric_series {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (a ^ 2 * (1 / 2 - a / 2) ^ (n + 1) * (1 / 2 + a / 2) ^ (n + 1) /
        ((1 / 2 + a / 2) ^ (n + 2) - (1 / 2 - a / 2) ^ (n + 2)) ^ 2) =
      L ((1 - a) / (1 + a))

/-- Sanford's Lucas-sequence generalization of Bridgeman, equation (8): for integer parameters
`P > 0`, `Q > 0` with `D = P² - 4Q > 0`, `α = (P + √D)/2`, and `k ≥ 1`,
`∑_{n ≥ 1} L(U_k² Q^{kn} / U_{k(n+1)}²) = L(Q^k/α^{2k})`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 5 (8) (`integers-2025-A52-thm-5`). -/
public theorem_wanted rogersDilog_lucasU_series (params : LucasSequenceParams)
    (hP : 0 < params.p) (hQ : 0 < params.q) (hD : 0 < params.p ^ 2 - 4 * params.q)
    {k : ℕ} (hk : 0 < k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    let α : ℝ := (params.p + √((params.p ^ 2 - 4 * params.q : ℤ) : ℝ)) / 2
    ∑' n : ℕ, L ((lucasU params k : ℝ) ^ 2 * (params.q : ℝ) ^ (k * (n + 1)) /
        (lucasU params (k * (n + 2)) : ℝ) ^ 2) = L ((params.q : ℝ) ^ k / α ^ (2 * k))

/-- Sanford's Lucas-sequence generalization of Bridgeman, equation (9): for integer parameters
`P > 0`, `Q < 0`, `D = P² - 4Q`, `α = (P + √D)/2`, and odd `k ≥ 1`,
`∑_{n ≥ 1} L(-V_k² Q^{k(2n-1)} / (D U_{2kn}²)) + ∑_{n ≥ 1} L(V_k² Q^{2kn} / V_{k(2n+1)}²)
  = L(-Q^k/α^{2k})`.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 5 (9) (`integers-2025-A52-thm-5`). -/
public theorem_wanted rogersDilog_lucasUV_series_of_neg (params : LucasSequenceParams)
    (hP : 0 < params.p) (hQ : params.q < 0) {k : ℕ} (hk : Odd k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    let D : ℤ := params.p ^ 2 - 4 * params.q
    let α : ℝ := (params.p + √(D : ℝ)) / 2
    ∑' n : ℕ, L (-(lucasV params k : ℝ) ^ 2 * (params.q : ℝ) ^ (k * (2 * n + 1)) /
        ((D : ℝ) * (lucasU params (2 * k * (n + 1)) : ℝ) ^ 2)) +
      ∑' n : ℕ, L ((lucasV params k : ℝ) ^ 2 * (params.q : ℝ) ^ (2 * k * (n + 1)) /
        (lucasV params (k * (2 * n + 3)) : ℝ) ^ 2) =
      L (-(params.q : ℝ) ^ k / α ^ (2 * k))

end

end MetaMathlibExt
