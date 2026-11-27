/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Pazuki's constants for the comparison of the theta height and the Faltings height

The constants of F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140
(2012), 19–49: `Pazuki.m r g`, `Pazuki.M r g` of Theorem 1.1, `Pazuki.C g` of Remark 1.2,
`Pazuki.C₁ g r`, `Pazuki.C₂ g r` of Corollary 1.3, and the constant `Pazuki.lemma57Constant c`
of Lemma 5.7. Pazuki states the values of `C₁` and `C₂` without writing the inequalities that
derive them; this module proves those two inequalities for all integers `g ≥ 1` and `r ≥ 2`:

* `Pazuki.firstComparison_constant_le`: the constant obtained from Theorem 1.1 and Remark 1.2 for
  Corollary 1.3 (1) is at most `C₁(g, r)`;
* `Pazuki.secondComparison_constant_le`: the constant obtained from Lemma 5.7 with
  `c = 2 C₁(g, r)` for Corollary 1.3 (2) is at most `C₂(g, r)`.
-/

@[expose] public section

open Real

namespace Pazuki

/-- Pazuki's lower constant $m(r, g) = g\bigl[\tfrac14 \log(4\pi) - \tfrac12 r^{2g} \log r\bigr]$
of Theorem 1.1.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Theorem 1.1, p. 21. -/
noncomputable def m (r g : ℕ) : ℝ :=
  g * (1 / 4 * log (4 * π) - 1 / 2 * (r : ℝ) ^ (2 * g) * log r)

/-- Pazuki's upper constant
$M(r, g) = \tfrac{g}{4} \log(4\pi) + g \log r + \tfrac{g}{2} \log\bigl(2 + \tfrac{2}{3^{1/4}}
2^{g^3/4}\bigr)$ of Theorem 1.1.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Theorem 1.1, p. 21. -/
noncomputable def M (r g : ℕ) : ℝ :=
  g / 4 * log (4 * π) + g * log r +
    g / 2 * log (2 + 2 / (3 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ ((g : ℝ) ^ 3 / 4))

/-- The constant $C(g) = \tfrac{8g}{\pi}\bigl(1 + 2g^2 \log(4g)\bigr)$ of Pazuki's Remark 1.2,
bounding the period term by the matrix lemma.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Remark 1.2, p. 21. -/
noncomputable def C (g : ℕ) : ℝ :=
  8 * g / π * (1 + 2 * (g : ℝ) ^ 2 * log (4 * g))

/-- The constant $C_1(g, r) = 6 r^{2g} \log(r^{2g})$ of Pazuki's Corollary 1.3 (1).

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Corollary 1.3, p. 22. -/
noncomputable def C₁ (g r : ℕ) : ℝ :=
  6 * (r : ℝ) ^ (2 * g) * log ((r : ℝ) ^ (2 * g))

/-- The constant $C_2(g, r) = 1000\, r^{2g} (\log(r^{2g}))^5$ of Pazuki's Corollary 1.3 (2).

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Corollary 1.3, p. 22. -/
noncomputable def C₂ (g r : ℕ) : ℝ :=
  1000 * (r : ℝ) ^ (2 * g) * log ((r : ℝ) ^ (2 * g)) ^ 5

/-- The constant $\tilde c = c \log(6 + 2c \log(2c) - 2c) / \log 3$ of Pazuki's Lemma 5.7: for real
numbers $a, b \ge 1$ and $c \ge 2$ with $|a - b| \le c \log(2 + a)$, one has
$|a - b| \le \tilde c \log(2 + \min\{a, b\})$.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Lemma 5.7, p. 43. -/
noncomputable def lemma57Constant (c : ℝ) : ℝ :=
  c * log (6 + 2 * c * log (2 * c) - 2 * c) / log 3

/-- `log 2` lies between `0.69` and `0.7`. -/
private lemma log_two_bounds : 0.69 < log 2 ∧ log 2 < 0.7 :=
  ⟨by linarith [log_two_gt_d9], by linarith [log_two_lt_d9]⟩

/-- `log 3 > 1`, since `e < 3`. -/
private lemma one_lt_log_three : 1 < log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  linarith [exp_one_lt_d9]

/-- For every natural number `g ≥ 1`, `2 g³ ≤ 4 ^ g`. -/
private lemma two_mul_cube_le_four_pow (g : ℕ) (hg : 1 ≤ g) : 2 * g ^ 3 ≤ 4 ^ g := by
  induction g, hg using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      norm_num
    · have h3 : (n + 1) ^ 3 ≤ 4 * n ^ 3 := by
        have h2 : n ^ 2 * 2 ≤ n ^ 2 * n := Nat.mul_le_mul_left _ h
        nlinarith
      calc 2 * (n + 1) ^ 3 ≤ 4 * (2 * n ^ 3) := by omega
        _ ≤ 4 * 4 ^ n := by omega
        _ = 4 ^ (n + 1) := by ring

/-- **Pazuki's constant $C_1(g, r)$.** For integers $g \ge 1$ and $r \ge 2$, with $m(r, g)$,
$M(r, g)$ of Theorem 1.1, $C(g)$ of Remark 1.2 and $C_1(g, r) = 6 r^{2g} \log(r^{2g})$ of
Corollary 1.3,
$$\frac{\max\{|m(r, g)|, M(r, g)\} + \frac32 + \frac{g}{4} \log(2\pi)}{\log 3} + \frac{C(g)}{4}
\le C_1(g, r).$$
Pazuki takes $r$ even; the inequality holds for every integer $r \ge 2$.

This is the inequality that gives Corollary 1.3 (1) with the constant $C_1(g, r)$ from Theorem 1.1
and Remark 1.2: the terms $1$ and $\frac12 + \frac{g}{4} \log(2\pi)$ bound the effect of replacing
$h_\Theta(A, L)$ by $\max\{h_\Theta(A, L), 1\}$ and $\frac12 h_F(A)$ by $\frac12 \max\{h_F(A), 1\}$,
and $\log(\max\{h_\Theta(A, L), 1\} + 2) \ge \log 3$.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Theorem 1.1 and Remark 1.2, p. 21, Corollary 1.3, p. 22, and
§5.2.1, p. 42, where Pazuki states the constants without writing this inequality. -/
theorem firstComparison_constant_le (g r : ℕ) (hg : 1 ≤ g) (hr : 2 ≤ r) :
    (max |m r g| (M r g) + 3 / 2 + g / 4 * log (2 * π)) / log 3 + C g / 4 ≤ C₁ g r := by
  obtain ⟨hl₁, hl₂⟩ := log_two_bounds
  have hl3 := one_lt_log_three
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set a : ℝ := (g : ℝ) with ha
  set s : ℝ := log r with hs
  set N : ℝ := (r : ℝ) ^ (2 * g) with hN
  -- Basic bounds.
  have hs0 : log 2 ≤ s := log_le_log (by norm_num) hrR
  have hQ : (4 : ℝ) ^ g ≤ N := by
    rw [hN, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by nlinarith) g
  have hcube : 2 * a ^ 3 ≤ (4 : ℝ) ^ g := by
    have : ((2 * g ^ 3 : ℕ) : ℝ) ≤ ((4 ^ g : ℕ) : ℝ) := by
      exact_mod_cast two_mul_cube_le_four_pow g hg
    push_cast at this
    exact this
  have hN1 : 1 ≤ N := one_le_pow₀ (by linarith)
  have hlogN : log N = 2 * a * s := by
    rw [hN, log_pow]; push_cast; ring
  have hpi1 : log (4 * π) ≤ 4 * log 2 := by
    have : log (4 * π) ≤ log 16 := log_le_log (by positivity) (by linarith [pi_lt_d2])
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow] at this
    exact_mod_cast this
  have hpi1' : 0 ≤ log (4 * π) := log_nonneg (by linarith [pi_gt_three])
  have hpi2 : log (2 * π) ≤ 3 * log 2 := by
    have : log (2 * π) ≤ log 8 := log_le_log (by positivity) (by linarith [pi_lt_d2])
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow] at this
    exact_mod_cast this
  have hpi2' : 0 ≤ log (2 * π) := log_nonneg (by linarith [pi_gt_three])
  -- `|m| ≤ g (log (4π) / 4 + N s / 2)`.
  have hm : |m r g| ≤ a * (log (4 * π) / 4 + N * s / 2) := by
    rw [m, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    linarith
  -- `M ≤ g log(4π)/4 + g s + g/2 (2 + g³/4) log 2`.
  set X : ℝ := (2 : ℝ) ^ ((g : ℝ) ^ 3 / 4) with hX
  have hX1 : 1 ≤ X := one_le_rpow (by norm_num) (by positivity)
  have h3 : 1 ≤ (3 : ℝ) ^ (1 / 4 : ℝ) := one_le_rpow (by norm_num) (by norm_num)
  have hc3 : 2 / (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := div_le_self (by norm_num) h3
  have hc3' : 0 ≤ 2 / (3 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hlogX : log X = a ^ 3 / 4 * log 2 := by rw [hX, log_rpow (by norm_num)]
  have harg : log (2 + 2 / (3 : ℝ) ^ (1 / 4 : ℝ) * X) ≤ (2 + a ^ 3 / 4) * log 2 := by
    have h4 : 2 + 2 / (3 : ℝ) ^ (1 / 4 : ℝ) * X ≤ 4 * X := by nlinarith
    calc log (2 + 2 / (3 : ℝ) ^ (1 / 4 : ℝ) * X) ≤ log (4 * X) :=
          log_le_log (by positivity) h4
      _ = 2 * log 2 + a ^ 3 / 4 * log 2 := by
          rw [log_mul (by norm_num) (by positivity), hlogX,
            show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
          push_cast; ring
      _ = (2 + a ^ 3 / 4) * log 2 := by ring
  have hargpos : 0 ≤ log (2 + 2 / (3 : ℝ) ^ (1 / 4 : ℝ) * X) :=
    log_nonneg (by nlinarith)
  have hM : M r g ≤ a / 4 * log (4 * π) + a * s + a / 2 * ((2 + a ^ 3 / 4) * log 2) := by
    rw [M]
    have := mul_le_mul_of_nonneg_left harg (by positivity : (0 : ℝ) ≤ a / 2)
    linarith
  have hM0 : 0 ≤ M r g := by
    rw [M]
    have : 0 ≤ log (r : ℝ) := log_nonneg (by linarith)
    positivity
  -- `C g / 4 ≤ (2 g / 3) (1 + 2 g² (2 log 2 + g - 1))`.
  have hlog4g : log (4 * a) ≤ 2 * log 2 + (a - 1) := by
    rw [log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < a)
    push_cast; linarith
  have hlog4g0 : 0 ≤ log (4 * a) := log_nonneg (by linarith)
  have hC : C g / 4 ≤ 2 * a / 3 * (1 + 2 * a ^ 2 * (2 * log 2 + (a - 1))) := by
    rw [C]
    have hpi : 2 * a / π ≤ 2 * a / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num)
      (by linarith [pi_gt_three])
    have h1 : 1 + 2 * a ^ 2 * log (4 * a) ≤ 1 + 2 * a ^ 2 * (2 * log 2 + (a - 1)) := by
      gcongr
    calc 8 * a / π * (1 + 2 * a ^ 2 * log (4 * a)) / 4
          = 2 * a / π * (1 + 2 * a ^ 2 * log (4 * a)) := by ring
      _ ≤ 2 * a / 3 * (1 + 2 * a ^ 2 * (2 * log 2 + (a - 1))) := by
          gcongr
  -- The numerator, divided by `log 3 > 1`.
  have hnum0 : 0 ≤ max |m r g| (M r g) + 3 / 2 + a / 4 * log (2 * π) := by positivity
  have hdiv : (max |m r g| (M r g) + 3 / 2 + a / 4 * log (2 * π)) / log 3 ≤
      max |m r g| (M r g) + 3 / 2 + a / 4 * log (2 * π) :=
    div_le_self hnum0 hl3.le
  have hmax : max |m r g| (M r g) ≤ |m r g| + M r g :=
    max_le (le_add_of_nonneg_right hM0) (le_add_of_nonneg_left (abs_nonneg _))
  have hC1 : C₁ g r = 12 * a * N * s := by
    rw [C₁, ← hN, hlogN]; ring
  rw [hC1]
  -- Final comparison with `N ≥ 4 ^ g ≥ 2 g³` and `s ≥ log 2`.
  set Q : ℝ := (4 : ℝ) ^ g with hQdef
  have ha0 : 0 ≤ a := by linarith
  have hs00 : 0 ≤ s := by linarith
  have hQ4 : 4 ≤ Q := by
    rw [hQdef]
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ g := pow_le_pow_right₀ (by norm_num) hg
  have p1 : a * log (4 * π) ≤ a * (4 * log 2) := mul_le_mul_of_nonneg_left hpi1 ha0
  have p2 : a * log (2 * π) ≤ a * (3 * log 2) := mul_le_mul_of_nonneg_left hpi2 ha0
  have p3 : a * log 2 ≤ a * 0.7 := mul_le_mul_of_nonneg_left hl₂.le ha0
  have p4 : a ^ 3 * log 2 ≤ a ^ 3 * 0.7 := mul_le_mul_of_nonneg_left hl₂.le (by positivity)
  have p5 : a ^ 4 * log 2 ≤ a ^ 4 * 0.7 := mul_le_mul_of_nonneg_left hl₂.le (by positivity)
  have p6 : a * s ≤ a * N * s := by
    have := mul_le_mul_of_nonneg_left hN1 (mul_nonneg ha0 hs00)
    linarith
  have p7 : a * N * 0.69 ≤ a * N * s :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have p8 : a * Q ≤ a * N := mul_le_mul_of_nonneg_left hQ ha0
  have p9 : a * (2 * a ^ 3) ≤ a * Q := mul_le_mul_of_nonneg_left hcube ha0
  have p10 : Q ≤ a * Q := by nlinarith
  have p11 : a * 4 ≤ a * Q := mul_le_mul_of_nonneg_left hQ4 ha0
  linarith

/-- **Pazuki's constant $C_2(g, r)$.** For integers $g \ge 1$ and $r \ge 2$, let
$C_1(g, r) = 6 r^{2g} \log(r^{2g})$ and $C_2(g, r) = 1000\, r^{2g} (\log(r^{2g}))^5$, as in
Corollary 1.3, let $c = 2 C_1(g, r)$ and let
$\tilde c = c \log(6 + 2c \log(2c) - 2c) / \log 3$ be the constant of Lemma 5.7 for this $c$.
Then
$$\frac{\tilde c}{2} \Bigl(1 + \frac{\log 2}{\log 3}\Bigr) \le C_2(g, r).$$
Pazuki takes $r$ even; the inequality holds for every integer $r \ge 2$.

This is the inequality that gives Corollary 1.3 (2) from Corollary 1.3 (1), applying Lemma 5.7 to
$a = 2\max\{h_\Theta(A, L), 1\}$, $b = \max\{h_F(A), 1\}$ and $c = 2 C_1(g, r)$.

Source: F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
<https://doi.org/10.24033/bsmf.2623>, Corollary 1.3, p. 22, and Lemma 5.7, p. 43, where Pazuki
states the constants without writing this inequality. -/
theorem secondComparison_constant_le (g r : ℕ) (hg : 1 ≤ g) (hr : 2 ≤ r) :
    lemma57Constant (2 * C₁ g r) / 2 * (1 + log 2 / log 3) ≤ C₂ g r := by
  obtain ⟨hl₁, hl₂⟩ := log_two_bounds
  have hl3 := one_lt_log_three
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set N : ℝ := (r : ℝ) ^ (2 * g) with hN
  set Y : ℝ := log N with hY
  have hN4 : 4 ≤ N := by
    rw [hN, pow_mul]
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ g := pow_le_pow_right₀ (by norm_num) hg
      _ ≤ ((r : ℝ) ^ 2) ^ g := pow_le_pow_left₀ (by norm_num) (by nlinarith) g
  have hY1 : 1.38 ≤ Y := by
    have : log 4 ≤ Y := log_le_log (by norm_num) hN4
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow] at this
    push_cast at this; linarith
  set c : ℝ := 2 * C₁ g r with hc
  have hcY : c = 12 * N * Y := by rw [hc, C₁]; ring
  have hc66 : 66 ≤ c := by rw [hcY]; nlinarith
  -- `log (2c) ≤ 2 Y + 5 log 2 - 1`.
  have h2c : log (2 * c) ≤ 2 * Y + 5 * log 2 - 1 := by
    have hY0 : 0 < Y := by linarith
    have hNpos : 0 < N := by linarith
    have : log (2 * c) = log 24 + Y + log Y := by
      rw [hcY, show 2 * (12 * N * Y) = 24 * N * Y by ring, log_mul (by positivity) hY0.ne',
        log_mul (by norm_num) hNpos.ne']
    rw [this]
    have h24 : log 24 ≤ 5 * log 2 := by
      have := log_le_log (by norm_num : (0 : ℝ) < 24) (by norm_num : (24 : ℝ) ≤ 2 ^ 5)
      rwa [log_pow] at this
    have := log_le_sub_one_of_pos hY0
    linarith
  have h2c1 : 1 ≤ log (2 * c) := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  -- `log (6 + 2c log(2c) - 2c) ≤ 2 log (2c)`.
  have harg0 : 0 < 6 + 2 * c * log (2 * c) - 2 * c := by nlinarith
  have harg : log (6 + 2 * c * log (2 * c) - 2 * c) ≤ 2 * log (2 * c) := by
    rw [show 2 * log (2 * c) = log ((2 * c) ^ 2) by rw [log_pow]; norm_num]
    refine log_le_log harg0 ?_
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 2 * c)
    nlinarith
  have harg1 : 0 ≤ log (6 + 2 * c * log (2 * c) - 2 * c) := by
    apply log_nonneg; nlinarith
  -- `c̃ ≤ 2 c log (2c)`.
  have hct : lemma57Constant c ≤ 2 * c * log (2 * c) := by
    rw [lemma57Constant, div_le_iff₀ (by linarith)]
    have h1 : c * log (6 + 2 * c * log (2 * c) - 2 * c) ≤ c * (2 * log (2 * c)) :=
      mul_le_mul_of_nonneg_left harg (by linarith)
    nlinarith
  have hct0 : 0 ≤ lemma57Constant c := by
    rw [lemma57Constant]
    have : 0 ≤ c := by linarith
    positivity
  have hfac : 1 + log 2 / log 3 ≤ 2 := by
    have : log 2 / log 3 ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact log_le_log (by norm_num) (by norm_num)
    linarith
  have hC2 : C₂ g r = 1000 * N * Y ^ 5 := by rw [C₂]
  rw [hC2]
  calc lemma57Constant c / 2 * (1 + log 2 / log 3) ≤ lemma57Constant c / 2 * 2 := by
        gcongr
    _ = lemma57Constant c := by ring
    _ ≤ 2 * c * log (2 * c) := hct
    _ ≤ 2 * (12 * N * Y) * (2 * Y + 5 * log 2 - 1) := by
        rw [hcY] at h2c ⊢; gcongr
    _ ≤ 1000 * N * Y ^ 5 := by
        have hNY : 0 ≤ N * Y := by nlinarith
        have hY4 : 1.38 ^ 3 * Y ≤ Y ^ 4 := by
          have : 1.38 ^ 3 ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY1 3
          nlinarith
        have : 24 * (2 * Y + 5 * log 2 - 1) ≤ 1000 * Y ^ 4 := by nlinarith
        nlinarith

end Pazuki
