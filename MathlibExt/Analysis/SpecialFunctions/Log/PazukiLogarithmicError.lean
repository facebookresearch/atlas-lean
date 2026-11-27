/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Analysis.SpecialFunctions.Log.PazukiConstants
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Pazuki's lemma on logarithmic errors

F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
Lemma 5.7 (p. 20 of arXiv:0907.1458v2): for real numbers `a`, `b`, `c` with `b ≥ 1` and
`c ≥ 2`, an error term `c log (2 + a)` in a comparison `|a - b| ≤ c log (2 + a)` can be replaced
by `c̃ log (2 + min a b)`, with `c̃ = c log (6 + 2c log (2c) - 2c) / log 3`, the constant
`Pazuki.lemma57Constant c`.

The proof follows Pazuki's. The printed lemma assumes `a ≥ 1`; the proof here does not use it
(when `a ≤ b`, the hypothesis itself forces `log (2 + a) ≥ 0`), so the statement drops it. For
`a ≤ -2`, `log (2 + a)` is Mathlib's `Real.log`, which is `log |2 + a|` (and `0` at `a = -2`); for
`a > -2`, which contains Pazuki's range `a ≥ 1`, it is the usual logarithm.

## Main results

* `Pazuki.log_two_mul_add_le`: `log (2y + d) ≤ (log (6 + d) / log 3) log y` for `y ≥ 3`, `d ≥ 0`.
* `Pazuki.abs_sub_le_mul_log_two_add_min`: Pazuki's Lemma 5.7.
-/

@[expose] public section

open Real

namespace Pazuki

/-- **The logarithm of `2y + d` against that of `y`** (a step in the proof of Pazuki's
Lemma 5.7). For real numbers $y \ge 3$ and $d \ge 0$,
$$\log(2y + d) \le \frac{\log(6 + d)}{\log 3} \log y.$$

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012),
19–49, proof of Lemma 5.7, read in arXiv:0907.1458v2, p. 20 ("valid for all $y \geq 3$ and
$d \geq 0$"). -/
theorem log_two_mul_add_le {y d : ℝ} (hy : 3 ≤ y) (hd : 0 ≤ d) :
    log (2 * y + d) ≤ log (6 + d) / log 3 * log y := by
  have hy0 : 0 < y := by linarith
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  have hlogy : log 3 ≤ log y := log_le_log (by norm_num) hy
  -- `log (2 + d / 3) ≥ 0`, and `log (6 + d) = log 3 + log (2 + d / 3)`.
  have hm : 0 ≤ log (2 + d / 3) :=
    log_nonneg (by linarith [div_nonneg hd (by norm_num : (0:ℝ) ≤ 3)])
  have h6 : log (6 + d) = log 3 + log (2 + d / 3) := by
    rw [← log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  -- `log (2y + d) = log y + log (2 + d / y) ≤ log y + log (2 + d / 3)`.
  have h1 : log (2 * y + d) ≤ log y + log (2 + d / 3) := by
    have hdy : d / y ≤ d / 3 := div_le_div_of_nonneg_left hd (by norm_num) hy
    have : log (2 * y + d) = log y + log (2 + d / y) := by
      rw [← log_mul hy0.ne' (by positivity)]
      congr 1
      field_simp
    rw [this]
    gcongr
  calc log (2 * y + d) ≤ log y + log (2 + d / 3) := h1
    _ ≤ log y + log (2 + d / 3) * (log y / log 3) := by
        gcongr
        exact le_mul_of_one_le_right hm (by rw [le_div_iff₀ hlog3, one_mul]; exact hlogy)
    _ = log (6 + d) / log 3 * log y := by
        rw [h6]
        field_simp

/-- **Pazuki's lemma on logarithmic errors** (Lemma 5.7). Let $b \ge 1$ and $a$ be real numbers,
and let $c \ge 2$ be a real number with $|a - b| \le c \log(2 + a)$. Then
$$|a - b| \le \tilde c \log(2 + \min\{a, b\}), \qquad
\tilde c = \frac{c \log(6 + 2c \log(2c) - 2c)}{\log 3},$$
where $\tilde c$ is `Pazuki.lemma57Constant c`.

Pazuki also assumes $a \ge 1$; the statement does not need it. It holds for every real $a$,
with Mathlib's `Real.log`, for which $\log x = \log |x|$ (and $\log 0 = 0$): for $a \le -2$ the
logarithms $\log(2 + a)$ and $\log(2 + \min\{a, b\})$ are read this way. For $a > -2$, which
contains Pazuki's range $a \ge 1$, they are the usual logarithms.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012),
19–49, Lemma 5.7 and its proof, read in arXiv:0907.1458v2, p. 20. -/
theorem abs_sub_le_mul_log_two_add_min {a b c : ℝ} (hb : 1 ≤ b) (hc : 2 ≤ c)
    (h : |a - b| ≤ c * log (2 + a)) :
    |a - b| ≤ lemma57Constant c * log (2 + min a b) := by
  rw [lemma57Constant]
  have hc0 : 0 < c := by linarith
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  -- `log (2c) ≥ 1`, since `2c ≥ 4 > e`.
  have hlog2c : 1 ≤ log (2 * c) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9])
  set d := 2 * c * log (2 * c) - 2 * c with hd_def
  have hd : 0 ≤ d := by nlinarith
  have hsix : 6 + 2 * c * log (2 * c) - 2 * c = 6 + d := by rw [hd_def]; ring
  rw [hsix]
  -- `c̃ ≥ c`, as `log (6 + d) ≥ log 3`.
  have hratio : 1 ≤ log (6 + d) / log 3 := by
    rw [le_div_iff₀ hlog3, one_mul]
    exact log_le_log (by norm_num) (by linarith)
  have hct : c ≤ c * log (6 + d) / log 3 := by
    rw [mul_div_assoc]
    nlinarith
  rcases le_or_gt a b with hab | hab
  · -- `min a b = a`: the hypothesis forces `log (2 + a) ≥ 0`.
    rw [min_eq_left hab]
    have hlog : 0 ≤ log (2 + a) := by
      by_contra hneg
      have hneg : log (2 + a) < 0 := not_le.mp hneg
      have : c * log (2 + a) < 0 := mul_neg_of_pos_of_neg hc0 hneg
      linarith [abs_nonneg (a - b)]
    calc |a - b| ≤ c * log (2 + a) := h
      _ ≤ c * log (6 + d) / log 3 * log (2 + a) := mul_le_mul_of_nonneg_right hct hlog
  · -- `min a b = b`.
    rw [min_eq_right hab.le]
    have ha0 : 0 < 2 + a := by linarith
    -- `c log (2 + a) ≤ a / 2 + c log (2c) - c + 1`, from `log t ≤ t - 1`.
    have hmax : c * log (2 + a) ≤ a / 2 + c * log (2 * c) - c + 1 := by
      have h1 : log ((2 + a) / (2 * c)) ≤ (2 + a) / (2 * c) - 1 :=
        log_le_sub_one_of_pos (by positivity)
      rw [log_div ha0.ne' (by positivity)] at h1
      have h2 : c * ((2 + a) / (2 * c)) = (2 + a) / 2 := by field_simp
      nlinarith
    have habs : |a - b| = a - b := abs_of_pos (by linarith)
    -- Hence `2 + a ≤ 2 (2 + b) + d`.
    have hle : 2 + a ≤ 2 * (2 + b) + d := by
      rw [habs] at h
      rw [hd_def]
      linarith
    calc |a - b| ≤ c * log (2 + a) := h
      _ ≤ c * log (2 * (2 + b) + d) := by gcongr
      _ ≤ c * (log (6 + d) / log 3 * log (2 + b)) := by
          gcongr
          exact log_two_mul_add_le (by linarith) hd
      _ = c * log (6 + d) / log 3 * log (2 + b) := by ring

end Pazuki
