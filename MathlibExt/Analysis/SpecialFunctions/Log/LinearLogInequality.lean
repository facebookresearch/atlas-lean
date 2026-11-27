/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Solving `x ≤ u (v + log x)` for `x`

Gaudron and Rémond's Lemme 8.5 in *Polarisations et isogénies*: an elementary bound that turns
an inequality `x ≤ u (v + log x)` into an explicit bound for `x`. They use it to bound the degree
of the abelian subvariety given by the period theorem.

The proof differs slightly from the printed one, which reduces to `v = 0`: we compare
`y ↦ y - u log y` directly at `x` and at `2u (log u + v)`, and bound `log (2t)` by `2t / e`.
-/

@[expose] public section

namespace Real

/-- **An elementary inequality for $x \le u(v + \log x)$** (Gaudron and Rémond, Lemme 8.5).
Let $u \ge \sqrt{e}$ and $v \ge 0$ be real numbers, and let $x > 0$ be a real number with
$x \le u\,(v + \log x)$. Then $x \le 2u\,(\log u + v)$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, Lemme 8.5 and its proof, p. 2096. -/
theorem le_two_mul_mul_log_add_of_le_mul_add_log {u v x : ℝ} (hu : √(exp 1) ≤ u)
    (hv : 0 ≤ v) (hx : 0 < x) (h : x ≤ u * (v + log x)) : x ≤ 2 * u * (log u + v) := by
  have hu0 : 0 < u := lt_of_lt_of_le (sqrt_pos.mpr (exp_pos 1)) hu
  -- `log u ≥ 1/2`, since `√e = exp (1/2)`.
  have hlog : 1 / 2 ≤ log u := by
    have h1 : exp (1 / 2) ≤ u := by rw [exp_half]; exact hu
    have := log_le_log (exp_pos _) h1
    rwa [log_exp] at this
  set t := log u + v with ht
  have ht0 : 1 / 2 ≤ t := by linarith
  set X := 2 * u * t with hX
  have hXu : u ≤ X := by nlinarith
  have hX0 : 0 < X := lt_of_lt_of_le hu0 hXu
  by_contra! hlt
  -- `y ↦ y - u log y` increases strictly from `X` to `x`, as `X ≥ u`.
  have hincr : X - u * log X < x - u * log x := by
    have hq : 0 < x / X := div_pos hx hX0
    have hq1 : x / X ≠ 1 := by
      intro h1
      rw [div_eq_one_iff_eq hX0.ne'] at h1
      exact hlt.ne' h1
    have hl := log_lt_sub_one_of_pos hq hq1
    rw [log_div hx.ne' hX0.ne'] at hl
    have key : u * (log x - log X) < u * (x / X - 1) := mul_lt_mul_of_pos_left hl hu0
    have key2 : u * (x / X - 1) ≤ x - X := by
      have : u * (x / X - 1) = (x - X) * (u / X) := by field_simp
      rw [this]
      have h' : u / X ≤ 1 := (div_le_one hX0).mpr hXu
      have h'' : 0 ≤ x - X := by linarith
      nlinarith
    linarith
  -- `log (2t) ≤ 2t / e ≤ t`.
  have h2t : log (2 * t) ≤ t := by
    have ht2 : 0 < 2 * t := by linarith
    have he : 0 < exp 1 := exp_pos 1
    have hl := log_le_sub_one_of_pos (div_pos ht2 he)
    rw [log_div ht2.ne' he.ne', log_exp] at hl
    have he2 : 2 ≤ exp 1 := by
      have := add_one_le_exp (1 : ℝ)
      linarith
    have : 2 * t / exp 1 ≤ t := by
      rw [div_le_iff₀ he]
      nlinarith
    linarith
  -- At `X` the function is `u (t - log (2t)) ≥ 0`, up to the shift `u v`.
  have hXval : X - u * log X - u * v = u * (t - log (2 * t)) := by
    have hlogX : log X = log u + log (2 * t) := by
      rw [hX, mul_comm 2 u, mul_assoc, log_mul hu0.ne' (by linarith)]
    rw [hlogX]
    ring
  have hfX : 0 ≤ X - u * log X - u * v := by
    rw [hXval]
    exact mul_nonneg hu0.le (by linarith)
  nlinarith

end Real
