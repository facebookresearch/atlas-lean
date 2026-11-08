/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Farey staircases

Statements from David Harry Richman, *Lower Rational Approximations and Farey Staircases*,
INTEGERS 24 (2024), Article A37 (primary text: arXiv:2303.02935).

The Farey staircase `A_n(x) = (1/n) Σ_{k=1}^n ⌊kx⌋/k` averages the lower rational approximations
`⌊kx⌋/k`; `B_n(x) = n A_n(x/n)` zooms in at the origin; `D_n = A_n - A_{n-1}`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace MetaMathlibExt

@[expose] public section

/-- The Farey staircase of order `n`: `A_n(x) = (1/n) Σ_{k=1}^n ⌊kx⌋/k`, the average of the first `n`
lower rational approximations `⌊kx⌋/k` of `x` (`A_0 = 0`).

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1, equation (2). -/
public noncomputable def fareyStaircase (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k

/-- `A_0 = 0`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1, equation (2). -/
public theorem fareyStaircase_zero (x : ℝ) : fareyStaircase 0 x = 0 := by
  simp [fareyStaircase]

/-- `A_1(x) = ⌊x⌋`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1, equation (2). -/
public theorem fareyStaircase_one (x : ℝ) : fareyStaircase 1 x = ⌊x⌋ := by
  simp [fareyStaircase]

/-- The zoomed Farey staircase `B_n(x) = n A_n(x/n) = Σ_{k=1}^n ⌊(k/n) x⌋/k`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1.1, equation (4). -/
public noncomputable def fareyZoom (n : ℕ) (x : ℝ) : ℝ :=
  n * fareyStaircase n (x / n)

/-- `B_n(x) = Σ_{k=1}^n ⌊(k/n) x⌋/k` for `n ≥ 1`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1.1, equation (4). -/
public theorem fareyZoom_eq_sum {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fareyZoom n x = ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) / n * x⌋ : ℝ) / k := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [fareyZoom, fareyStaircase, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_mul_eq_mul_div, mul_div_assoc]

/-- `B_1(x) = ⌊x⌋`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Section 1.1, equation (4). -/
public theorem fareyZoom_one (x : ℝ) : fareyZoom 1 x = ⌊x⌋ := by
  simp [fareyZoom, fareyStaircase_one]

/-- Theorem 1: for `x ≥ 0`, `B_n(x) → Σ_{k=1}^{⌊x⌋} log(x/k)` as `n → ∞`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 1 (`integers-2024-A37-thm-1`). -/
public theorem_wanted tendsto_fareyZoom {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto (fun n : ℕ => fareyZoom n x) Filter.atTop
      (nhds (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / k)))

/-- Theorem 3: for `x ≥ 0` and a positive reduced fraction `p/q`,
`B_n(x + (p/q) n) - B_n((p/q) n) → (1/q) Σ_{k=1}^{⌊qx⌋} log(qx/k)` as `n → ∞`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 3 (`integers-2024-A37-thm-3`). -/
public theorem_wanted tendsto_fareyZoom_sub_at_rational {x : ℝ} (hx : 0 ≤ x) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    Filter.Tendsto
      (fun n : ℕ => fareyZoom n (x + (p : ℝ) / q * n) - fareyZoom n ((p : ℝ) / q * n))
      Filter.atTop
      (nhds ((q : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 ⌊(q : ℝ) * x⌋₊, Real.log (q * x / k)))

/-- Theorem 4: for `x ≥ 0`, `n² D_n(x/n) → Σ_{k=1}^{⌊x⌋} (1 - log(x/k))` as `n → ∞`, where
`D_n = A_n - A_{n-1}`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 4 (`integers-2024-A37-thm-4`). -/
public theorem_wanted tendsto_sq_mul_fareyStaircase_sub {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 2 * (fareyStaircase n (x / n) - fareyStaircase (n - 1) (x / n)))
      Filter.atTop (nhds (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (1 - Real.log (x / k))))

/-- Theorem 5 (i) (D. R. Richman): the set `S` of values
`f_n(x) = ⌊nx⌋ - Σ_{k=1}^n ⌊kx⌋/k = ⌊nx⌋ - n A_n(x)` (`n ≥ 1`, `x ∈ ℝ`) is dense in
`[1 - log 2, ∞)`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (i) (`integers-2024-A37-thm-5`), also Corollary 6
(`integers-2024-A37-cor-6`). -/
public theorem_wanted Ici_one_sub_log_two_subset_closure_floor_gaps :
    Set.Ici (1 - Real.log 2) ⊆
      closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x}

/-- Theorem 5 (ii) (D. R. Richman): for every `ε > 0` only finitely many values
`f_n(x) = ⌊nx⌋ - n A_n(x)` (`n ≥ 1`, `x ∈ ℝ`) are at most `1 - log 2 - ε`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (ii) (`integers-2024-A37-thm-5`). -/
public theorem_wanted floor_gaps_inter_Iic_finite {ε : ℝ} (hε : 0 < ε) :
    ({y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x} ∩
      Set.Iic (1 - Real.log 2 - ε)).Finite

/-- Proposition 7: for `n ≥ 2`, `D_n = A_n - A_{n-1}` satisfies
(a) `D_n(x) = (1/n)(⌊nx⌋/n - A_{n-1}(x))` and (b) `D_n(x) = (1/(n-1))(⌊nx⌋/n - A_n(x))`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Proposition 7 (`integers-2024-A37-prop-7`). -/
public theorem_wanted fareyStaircase_sub_eq {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    fareyStaircase n x - fareyStaircase (n - 1) x =
        (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase (n - 1) x) ∧
      fareyStaircase n x - fareyStaircase (n - 1) x =
        ((n : ℝ) - 1)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase n x)

/-- Lemma 8 (a): for `n ≥ 1`, `A_n(x) ≤ ⌊nx⌋/n ≤ A_n(x) + (log n)/n`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (a) (`integers-2024-A37-lem-8`). -/
public theorem_wanted fareyStaircase_le_floor_div {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fareyStaircase n x ≤ ⌊(n : ℝ) * x⌋ / n ∧
      (⌊(n : ℝ) * x⌋ : ℝ) / n ≤ fareyStaircase n x + Real.log n / n

/-- Lemma 8 (b): for `n ≥ 2`, `0 ≤ D_n(x) ≤ (log n)/(n(n - 1))`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`). -/
public theorem_wanted fareyStaircase_sub_mem_Icc {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ fareyStaircase n x - fareyStaircase (n - 1) x ∧
      fareyStaircase n x - fareyStaircase (n - 1) x ≤ Real.log n / (n * (n - 1))

/-- Lemma 9: if `a_n ≤ b_n` are natural numbers with `a_n → ∞`, then
`Σ_{k=a_n}^{b_n} 1/k - ∫_{a_n}^{b_n} dt/t → 0`, i.e. the two limits agree whenever either exists.
The paper's positivity of `a_n, b_n` and `b_n → ∞` follow eventually from `a_n ≤ b_n`, `a_n → ∞`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 9 (`integers-2024-A37-lem-9`). -/
public theorem_wanted tendsto_harmonic_block_sub_integral {a b : ℕ → ℕ} (hab : ∀ n, a n ≤ b n)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n => ∑ k ∈ Finset.Icc (a n) (b n), (1 / k : ℝ) - ∫ t in (a n : ℝ)..(b n), t⁻¹)
      Filter.atTop (nhds 0)

/-- Proposition 12: if `f` has derivative `f'` at `x`, the dilation derivative
`lim_{λ → 1} (λ⁻¹ f(λx) - f(x))/(λ - 1)` exists and equals `x f' - f(x)`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Proposition 12 (`integers-2024-A37-prop-12`); dilation derivative as defined
before it. -/
public theorem_wanted tendsto_dilation_quotient {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    Filter.Tendsto (fun l : ℝ => (l⁻¹ * f (l * x) - f x) / (l - 1)) (nhdsWithin 1 {1}ᶜ)
      (nhds (x * f' - f x))

end

end MetaMathlibExt
