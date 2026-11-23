/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-!
# Incomplete exponential sums: a partial-fraction bound for the cosecant

`MetaMathlibExt.one_div_sin_pi_lt`: for `0 < x < 1`,
`1 / sin(πx) < (1/π) (1/x + 2x / (1 - x²))`. The right-hand side is `1/π` times the sum of the
first two terms of the partial-fraction expansion
`π / sin(πx) = 1/x + ∑_{n ≥ 1} (-1)^(n+1) 2x / (n² - x²)`.

This is Lemma 3.1 of Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*,
INTEGERS 25 (2025), Article A48, quoted there from [3, Lemma 2.2]. Further statements from that
paper appear in `WantedExt.NumberTheory.IncompleteExponentialSumWanted`.

## Proof outline

Since `1/x + 2x/(1 - x²) = (1 + x²) / (x (1 - x²))`, the claim is
`π x (1 - x²) / (1 + x²) < sin(πx)`. Instead of the partial-fraction expansion, we use Euler's
product `sin(πx) = π x ∏_{j ≥ 1} (1 - x²/j²)` (`Real.tendsto_euler_sin_prod`).

* With `e(k) = (k + x²) / k`, each factor satisfies
  `e(k) (1 - x²/(k + 1)²) - e(k + 1) = x² (1 - x²) / ((k + 1)² k) ≥ 0` for `k > 0`.
* So the partial products telescope: for `n ≥ 2`,
  `∏_{j=1}^{n} (1 - x²/j²) ≥ (1 - x²)(1 - x²/4) e(n) / e(2)`, and `e(n) ≥ 1`.
* Letting `n → ∞` gives `sin(πx) ≥ π x (1 - x²)(1 - x²/4) / e(2)`, which exceeds
  `π x (1 - x²) / (1 + x²)` because `(4 - x²)(1 + x²) - 2 (2 + x²) = x² (1 - x²) > 0`.

The bound is sharp at both ends: the ratio of `sin(πx)` to `π x (1 - x²) / (1 + x²)` tends to `1`
as `x → 0` and as `x → 1`. This is why `e` is chosen to make the telescoping exact at `x = 1`,
where `∏_{j=2}^{n} (1 - 1/j²) = e(n) / e(1) = (n + 1) / (2n)`.
-/

namespace MetaMathlibExt

open Filter Finset

/-- The telescoping step: for `0 < x < 1` and `k > 0`,
`(k + 1 + x²) / (k + 1) ≤ (k + x²) / k · (1 - x² / (k + 1)²)`. -/
private lemma one_div_sin_pi_lt_step {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) {k : ℝ} (hk : 0 < k) :
    (k + 1 + x ^ 2) / (k + 1) ≤ (k + x ^ 2) / k * (1 - x ^ 2 / (k + 1) ^ 2) := by
  have hk1 : 0 < k + 1 := by linarith
  have hgap : (k + x ^ 2) / k * (1 - x ^ 2 / (k + 1) ^ 2) - (k + 1 + x ^ 2) / (k + 1) =
      x ^ 2 * (1 - x ^ 2) / ((k + 1) ^ 2 * k) := by
    field_simp
    ring
  have hx2 : 0 ≤ 1 - x ^ 2 := by nlinarith
  have : 0 ≤ x ^ 2 * (1 - x ^ 2) / ((k + 1) ^ 2 * k) := by positivity
  linarith

/-- Lower bound for the partial products of Euler's sine product: for `0 < x < 1` and every `n`,
`(1 - x²)(1 - x²/4) · (2 / (2 + x²)) · e(n + 2) ≤ ∏_{j < n + 2} (1 - x² / (j + 1)²)`,
where `e(k) = (k + x²) / k`. -/
private lemma one_div_sin_pi_lt_prod {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    (1 - x ^ 2) * (1 - x ^ 2 / 4) * (2 / (2 + x ^ 2)) *
        ((((n + 2 : ℕ) : ℝ) + x ^ 2) / ((n + 2 : ℕ) : ℝ)) ≤
      ∏ j ∈ range (n + 2), (1 - x ^ 2 / ((j : ℝ) + 1) ^ 2) := by
  have hx2 : 0 < 1 - x ^ 2 := by nlinarith
  have hA : 0 ≤ (1 - x ^ 2) * (1 - x ^ 2 / 4) * (2 / (2 + x ^ 2)) := by
    have : 0 ≤ 1 - x ^ 2 / 4 := by nlinarith
    positivity
  induction n with
  | zero =>
    apply le_of_eq
    simp only [prod_range_succ, range_zero, prod_empty]
    push_cast
    field_simp
    ring
  | succ n ih =>
    rw [prod_range_succ]
    have hk : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    have hcast : ((n + 1 + 2 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    have hf : 0 ≤ 1 - x ^ 2 / (((n + 2 : ℕ) : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith
    rw [hcast]
    calc (1 - x ^ 2) * (1 - x ^ 2 / 4) * (2 / (2 + x ^ 2)) *
          ((((n + 2 : ℕ) : ℝ) + 1 + x ^ 2) / (((n + 2 : ℕ) : ℝ) + 1))
        ≤ (1 - x ^ 2) * (1 - x ^ 2 / 4) * (2 / (2 + x ^ 2)) *
          ((((n + 2 : ℕ) : ℝ) + x ^ 2) / ((n + 2 : ℕ) : ℝ) *
            (1 - x ^ 2 / (((n + 2 : ℕ) : ℝ) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left (one_div_sin_pi_lt_step hx₀ hx₁ hk) hA
      _ = (1 - x ^ 2) * (1 - x ^ 2 / 4) * (2 / (2 + x ^ 2)) *
          ((((n + 2 : ℕ) : ℝ) + x ^ 2) / ((n + 2 : ℕ) : ℝ)) *
            (1 - x ^ 2 / (((n + 2 : ℕ) : ℝ) + 1) ^ 2) := by ring
      _ ≤ (∏ j ∈ range (n + 2), (1 - x ^ 2 / ((j : ℝ) + 1) ^ 2)) *
            (1 - x ^ 2 / (((n + 2 : ℕ) : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right ih hf

/-- **Partial-fraction bound for the cosecant.** For every real number $x$ with $0 < x < 1$,
$$\frac{1}{\sin(\pi x)} < \frac{1}{\pi}\left(\frac{1}{x} + \frac{2x}{1 - x^2}\right).$$
That is, the first two terms of the partial-fraction expansion of $\pi / \sin(\pi x)$ bound it
from above.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.1 (quoted from [3, Lemma 2.2]) (`integers-2025-A48-lem-3-1`). -/
public theorem one_div_sin_pi_lt (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    1 / Real.sin (Real.pi * x) < (1 / Real.pi) * (1 / x + 2 * x / (1 - x ^ 2)) := by
  have hx2 : 0 < 1 - x ^ 2 := by nlinarith
  have hx4 : 0 < 1 - x ^ 2 / 4 := by nlinarith
  have hpi := Real.pi_pos
  set A := (1 - x ^ 2) * (1 - x ^ 2 / 4) * (2 / (2 + x ^ 2)) with hA_def
  have hA : 0 < A := by positivity
  -- Euler's product gives `π x A ≤ sin (π x)`.
  have hsin : Real.pi * x * A ≤ Real.sin (Real.pi * x) := by
    refine ge_of_tendsto' ((Real.tendsto_euler_sin_prod x).comp (tendsto_add_atTop_nat 2))
      fun n => ?_
    simp only [Function.comp_apply]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (one_div_sin_pi_lt_prod hx₀ hx₁ n)
    refine le_mul_of_one_le_right hA.le ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `π x (1 - x²) / (1 + x²) < π x A`, since `(4 - x²)(1 + x²) - 2 (2 + x²) = x² (1 - x²)`.
  have hpos : 0 < Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2) := by positivity
  have hlt : Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2) < Real.pi * x * A := by
    have hgap : Real.pi * x * A - Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2) =
        Real.pi * x * (1 - x ^ 2) * (x ^ 2 * (1 - x ^ 2)) / (2 * (2 + x ^ 2) * (1 + x ^ 2)) := by
      rw [hA_def]
      field_simp
      ring
    have : 0 < Real.pi * x * (1 - x ^ 2) * (x ^ 2 * (1 - x ^ 2)) /
        (2 * (2 + x ^ 2) * (1 + x ^ 2)) := by positivity
    linarith
  calc 1 / Real.sin (Real.pi * x) < 1 / (Real.pi * x * (1 - x ^ 2) / (1 + x ^ 2)) :=
        one_div_lt_one_div_of_lt hpos (hlt.trans_le hsin)
    _ = (1 / Real.pi) * (1 / x + 2 * x / (1 - x ^ 2)) := by
        field_simp
        ring

end MetaMathlibExt
