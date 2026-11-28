/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.Analysis.SpecialFunctions.Log.LinearLogInequality

/-!
# Removing the heights from the Gaudron–Rémond isogeny bound

The last step of the proof of the isogeny estimates of Gaudron and Rémond (Lemme 9.4 of
*Polarisations et isogénies*) is a purely numerical inequality. Their bounds are first stated in
terms of a quantity $P$ (p. 2098), built from the dimension $g$, the degree $D = [k : \mathbb{Q}]$
of the field of definition and a bound $M \ge 1$ for several Faltings heights; the isogeny degree
is bounded by $Q = (9g)^{96 g^4} P^{2^{10} g^3}$. Raynaud's estimate for the change of Faltings
height under an isogeny gives $M \le \max(h + \frac12 \log Q, 1)$, where $h = h_F(A)$, and this
module shows that this self-referential bound forces $Q \le \kappa$, where
$$\kappa = \Bigl( (14 g)^{64 g^2} \, D \, \max(h, \log D, 1)^2 \Bigr)^{2^{10} g^3}$$
is the constant $\kappa(A)$ of p. 2058.

The proof follows the paper: a crude bound $Q \le \exp(75 \cdot 2^{11} g^6) (DM)^{2^{11} g^3}$,
then Lemme 8.5 (`Real.le_two_mul_mul_log_add_of_le_mul_add_log`) to get
$M + \frac32 g \le 83 \cdot 2^{11} g^6 \max(h, \log D, 1)$, which is inserted back into $P$. The
real power $(9g)^{3g/32}$ of the printed argument is avoided by raising the final comparison of
constants to the power $32 g^3$. The printed proof uses Bost's lower bound $h \ge -\frac32 g$ to
drop the maximum in Raynaud's estimate; here the case $M \le 1$ is treated directly, so no lower
bound on $h$ is needed.
-/

@[expose] public section

namespace GaudronRemond

open Real

/-- **The quantity $P$ of Gaudron and Rémond.** For a natural number $g$ and real numbers $D$
and $M$,
$$P(g, D, M) = 4 (9g)^{4g} (8g)^{64 g^2} D \max\Bigl(M + \tfrac32 g,
\log\bigl(4 (9g)^{4g} D\bigr)\Bigr)^2.$$
For an abelian variety of dimension $g$ over a number field $k$, with $D = [k : \mathbb{Q}]$ and
$M$ the maximum of $1$ and of the Faltings heights of the abelian varieties in play, this is the
quantity $P$ of É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, p. 2098, <https://doi.org/10.1215/00127094-2782528>. -/
noncomputable def boundP (g : ℕ) (D M : ℝ) : ℝ :=
  4 * (9 * g : ℝ) ^ (4 * g) * (8 * g : ℝ) ^ (64 * g ^ 2) * D *
    max (M + 3 / 2 * g) (log (4 * (9 * g : ℝ) ^ (4 * g) * D)) ^ 2

/-! ### Numerical bounds for logarithms -/

private lemma log_eight : log (8 : ℝ) = 3 * log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
  norm_num

private lemma log_nine_le : log (9 : ℝ) ≤ 3 * log 2 + 1 / 8 := by
  have h := log_le_sub_one_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  rw [log_div (by norm_num) (by norm_num), log_eight] at h
  linarith

private lemma log_nine_ge : 3 * log 2 ≤ log (9 : ℝ) := by
  rw [← log_eight]
  exact log_le_log (by norm_num) (by norm_num)

private lemma log_eightyThree_le : log (83 : ℝ) ≤ 6 * log 2 + 19 / 64 := by
  have h := log_le_sub_one_of_pos (show (0 : ℝ) < 83 / 64 by norm_num)
  rw [log_div (by norm_num) (by norm_num), show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow] at h
  push_cast at h
  linarith

private lemma log_fourteen_ge : 4 * log 2 - 1 / 7 ≤ log (14 : ℝ) := by
  have h := log_le_sub_one_of_pos (show (0 : ℝ) < 16 / 14 by norm_num)
  rw [log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow] at h
  push_cast at h
  linarith

/-! ### The steps of the proof -/

/-- The crude bound of the proof of Lemme 9.4: $\log Q \le 75 \cdot 2^{11} g^6 + 2^{11} g^3
(\log D + \log M)$. -/
private lemma log_le_of_one_le (g : ℕ) (hg : 1 ≤ g) {D M : ℝ} (hD : 1 ≤ D) (hM : 1 ≤ M) :
    log ((9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3)) ≤
      153600 * (g : ℝ) ^ 6 + 2048 * (g : ℝ) ^ 3 * (log D + log M) := by
  set x : ℝ := (g : ℝ) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; exact_mod_cast hg
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hM0 : 0 < M := by linarith
  set lx := log x with hlxdef
  have hlx0 : 0 ≤ lx := log_nonneg hx1
  have hlx1 : lx ≤ x - 1 := log_le_sub_one_of_pos hx0
  have hl2 := log_two_lt_d9
  have hl2' := log_two_gt_d9
  have hl9 := log_nine_le
  have hl9' := log_nine_ge
  have hlogD : 0 ≤ log D := log_nonneg hD
  -- `ℓ = log (4 (9g)^{4g})`.
  set ℓ := log (4 * (9 * x) ^ (4 * g)) with hℓdef
  have hℓ : ℓ = 2 * log 2 + 4 * x * (log 9 + lx) := by
    rw [hℓdef, log_mul (by norm_num) (by positivity), log_pow, log_mul (by norm_num) hx0.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast
    ring
  have hℓlow : 1 + 3 / 2 * x ≤ ℓ := by
    rw [hℓ]
    nlinarith [mul_nonneg hx0.le hlx0]
  have hℓ0 : 0 < ℓ := by linarith
  have hℓup : ℓ ≤ 8 * x ^ 2 * (128 / 100) := by
    rw [hℓ]
    nlinarith [mul_le_mul_of_nonneg_left hlx1 hx0.le, mul_le_mul_of_nonneg_left hl9 hx0.le,
      mul_le_mul_of_nonneg_left hl2.le hx0.le]
  have hlogℓ : log ℓ ≤ 3 * log 2 + 2 * lx + 28 / 100 := by
    have h1 := log_le_log hℓ0 hℓup
    rw [log_mul (by positivity) (by norm_num), log_mul (by norm_num) (by positivity), log_eight,
      log_pow] at h1
    have h2 := log_le_sub_one_of_pos (show (0 : ℝ) < 128 / 100 by norm_num)
    push_cast at h1
    linarith
  -- The maximum in `P` is at most `ℓ √D M`.
  set m := max (M + 3 / 2 * x) (log (4 * (9 * x) ^ (4 * g) * D)) with hmdef
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hsD : 1 ≤ √D := one_le_sqrt.mpr hD
  have hm : m ≤ ℓ * √D * M := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hsD (mul_nonneg hℓ0.le hM0.le)]
    · rw [log_mul (by positivity) hD0.ne', ← hℓdef]
      have hls : log D = 2 * log √D := by rw [log_sqrt hD0.le]; ring
      have hs := log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hsD)
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ - 2) (by linarith : (0 : ℝ) ≤ √D - 1),
        mul_le_mul_of_nonneg_left hM (mul_nonneg hℓ0.le (by linarith : (0 : ℝ) ≤ √D))]
  have hlogm : log m ≤ log ℓ + log D / 2 + log M := by
    have h := log_le_log hm0 hm
    rwa [log_mul (by positivity) hM0.ne', log_mul hℓ0.ne' (by positivity), log_sqrt hD0.le] at h
  -- The logarithm of `P`, then of `Q`.
  have hP : log (boundP g D M) =
      2 * log 2 + 4 * x * (log 9 + lx) + 64 * x ^ 2 * (3 * log 2 + lx) + log D + 2 * log m := by
    rw [boundP, ← hxdef, ← hmdef, log_mul (by positivity) (by positivity),
      log_mul (by positivity) hD0.ne', log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow,
      log_mul (by norm_num) hx0.ne', log_mul (by norm_num) hx0.ne', log_eight,
      show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast
    ring
  have hP0 : 0 < boundP g D M := by
    rw [boundP, ← hxdef, ← hmdef]
    positivity
  rw [log_mul (by positivity) (by positivity), log_pow, log_pow, hP,
    log_mul (by norm_num) hx0.ne']
  push_cast
  have hS : 3 / 32 * x * (log 9 + lx) + 2 * log 2 + 4 * x * (log 9 + lx) +
      64 * x ^ 2 * (3 * log 2 + lx) + 2 * (3 * log 2 + 2 * lx + 28 / 100) ≤ 150 * x ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hlx1 hx0.le,
      mul_le_mul_of_nonneg_left hlx1 (sq_nonneg x), mul_le_mul_of_nonneg_left hl9 hx0.le,
      mul_le_mul_of_nonneg_left hl2.le hx0.le, mul_le_mul_of_nonneg_left hl2.le (sq_nonneg x),
      mul_le_mul_of_nonneg_left hx1 hx0.le, mul_le_mul_of_nonneg_left hx1 (sq_nonneg x)]
  have hx3 : 0 ≤ 1024 * x ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS hx3, mul_le_mul_of_nonneg_left hlogℓ hx3,
    mul_le_mul_of_nonneg_left hlogm hx3]

/-- The height bound of the proof of Lemme 9.4: Raynaud's estimate and Lemme 8.5 give
$M + \frac32 g \le 83 \cdot 2^{11} g^6 \max(h, \log D, 1)$. -/
private lemma add_le_of_le_max (g : ℕ) (hg : 1 ≤ g) {D h M : ℝ} (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hMQ : M ≤ max (h + log ((9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3)) / 2)
      1) :
    M + 3 / 2 * g ≤ 169984 * (g : ℝ) ^ 6 * max h (max (log D) 1) := by
  have hL := log_le_of_one_le g hg hD hM
  set x : ℝ := (g : ℝ) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; exact_mod_cast hg
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  set Y := max h (max (log D) 1) with hYdef
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hYD : log D ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hYh : h ≤ Y := le_max_left _ _
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx1
  have hx6 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx13 : x ≤ x ^ 3 := by simpa using pow_le_pow_right₀ hx1 (show 1 ≤ 3 by norm_num)
  have hx34 : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hx46 : x ^ 4 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
  rcases le_max_iff.mp hMQ with h1 | h1
  · -- Lemme 8.5 with `u = 2^10 g^3` and `v = (75 g^3 + 1 + 2^{-10}) Y`.
    have hu : √(exp 1) ≤ 1024 * x ^ 3 := by
      rw [sqrt_le_left (by positivity)]
      have := exp_one_lt_d9
      nlinarith
    have hv : 0 ≤ (75 * x ^ 3 + 1 + 1 / 1024) * Y := by positivity
    have h2 : M ≤ h + 76800 * x ^ 6 + 1024 * x ^ 3 * log D + 1024 * x ^ 3 * log M := by
      set L := log ((9 * x) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3))
      have e : h + (153600 * x ^ 6 + 2048 * x ^ 3 * (log D + log M)) / 2 =
          h + 76800 * x ^ 6 + 1024 * x ^ 3 * log D + 1024 * x ^ 3 * log M := by ring
      linarith only [h1, hL, e]
    have hle : M ≤ 1024 * x ^ 3 * ((75 * x ^ 3 + 1 + 1 / 1024) * Y + log M) := by
      have e1 := mul_le_mul_of_nonneg_left hY1 (by positivity : (0 : ℝ) ≤ x ^ 6)
      have e2 := mul_le_mul_of_nonneg_left hYD (by positivity : (0 : ℝ) ≤ x ^ 3)
      have e3 := mul_le_mul_of_nonneg_right hx3 (by linarith : (0 : ℝ) ≤ Y)
      have e4 : 1024 * x ^ 3 * ((75 * x ^ 3 + 1 + 1 / 1024) * Y + log M) =
          76800 * x ^ 6 * Y + 1024 * x ^ 3 * Y + x ^ 3 * Y + 1024 * x ^ 3 * log M := by ring
      rw [e4]
      linarith
    have key := le_two_mul_mul_log_add_of_le_mul_add_log hu hv hM0 hle
    rw [log_mul (by norm_num) (by positivity), log_pow,
      show (1024 : ℝ) = 2 ^ 10 by norm_num, log_pow] at key
    push_cast at key
    have hl2 := log_two_lt_d9
    have hlx1 : log x ≤ x - 1 := log_le_sub_one_of_pos hx0
    have hpos : 0 ≤ 16384 * x ^ 6 - 2050 * x ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hl2.le (by positivity : (0 : ℝ) ≤ x ^ 3),
      mul_le_mul_of_nonneg_left hlx1 (by positivity : (0 : ℝ) ≤ x ^ 3),
      mul_le_mul_of_nonneg_left hY1 hpos]
  · nlinarith [mul_le_mul_of_nonneg_left hY1 (by positivity : (0 : ℝ) ≤ x ^ 6)]

/-- The comparison of constants at the end of the proof of Lemme 9.4, raised to the power
$32$: $(9g)^{3g} \bigl(4 (9g)^{4g} (8g)^{64g^2} (83 \cdot 2^{11})^2 g^{12}\bigr)^{32} \le
(14g)^{2048 g^2}$. -/
private lemma const_le (g : ℕ) (hg : 1 ≤ g) :
    (9 * g : ℝ) ^ (3 * g) *
        (4 * (9 * g : ℝ) ^ (4 * g) * (8 * g : ℝ) ^ (64 * g ^ 2) * 169984 ^ 2 * (g : ℝ) ^ 12) ^ 32 ≤
      (14 * g : ℝ) ^ (2048 * g ^ 2) := by
  set x : ℝ := (g : ℝ) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; exact_mod_cast hg
  have hx0 : 0 < x := by linarith
  set c : ℝ := 4 * (9 * x) ^ (4 * g) * (8 * x) ^ (64 * g ^ 2) * 169984 ^ 2 * x ^ 12 with hcdef
  have hc : log c = 2 * log 2 + 4 * x * (log 9 + log x) + 64 * x ^ 2 * (3 * log 2 + log x) +
      2 * (log 83 + 11 * log 2) + 12 * log x := by
    rw [hcdef, log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity), log_pow,
      log_pow, log_pow, log_pow, log_mul (by norm_num) hx0.ne', log_mul (by norm_num) hx0.ne',
      log_eight, show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow,
      show (169984 : ℝ) = 83 * 2 ^ 11 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
    push_cast
    ring
  rw [← log_le_log_iff (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_pow, log_pow, hc, log_mul (by norm_num) hx0.ne',
    log_mul (by norm_num) hx0.ne']
  push_cast
  have hl2 := log_two_lt_d9
  have hl2' := log_two_gt_d9
  have hl9 := log_nine_le
  have hl83 := log_eightyThree_le
  have hl14 := log_fourteen_ge
  have hlx0 : 0 ≤ log x := log_nonneg hx1
  have hlx1 : log x ≤ x - 1 := log_le_sub_one_of_pos hx0
  nlinarith [mul_le_mul_of_nonneg_left hlx1 hx0.le, mul_le_mul_of_nonneg_left hl9 hx0.le,
    mul_le_mul_of_nonneg_left hl2.le hx0.le, mul_le_mul_of_nonneg_left hl2'.le (sq_nonneg x),
    mul_le_mul_of_nonneg_left hl14 (sq_nonneg x), mul_le_mul_of_nonneg_left hx1 hx0.le]

/-- **Removing the heights from the Gaudron–Rémond isogeny bound** (Gaudron and Rémond,
Lemme 9.4). Let $g \ge 1$ be a natural number and let $D \ge 1$, $h$ and $M \ge 1$ be real
numbers. Put $P = P(g, D, M)$ (see `GaudronRemond.boundP`) and
$Q = (9g)^{96 g^4} P^{2^{10} g^3}$, and suppose that $M \le \max(h + \frac12 \log Q, 1)$. Then
$$Q \le \Bigl( (14 g)^{64 g^2} \, D \, \max(h, \log D, 1)^2 \Bigr)^{2^{10} g^3}.$$

In the paper, $D = [k : \mathbb{Q}]$ is the degree of a number field $k$, $h = h_F(A)$ is the
stable Faltings height of an abelian variety $A$ of dimension $g$ over $k$, and the right-hand
side is the constant $\kappa(A)$ of p. 2058. The hypothesis $M \le \max(h + \frac12 \log Q, 1)$ is
the input that the paper draws from Raynaud's estimate for the Faltings height of an isogenous
abelian variety. The paper also uses Bost's lower bound $h \ge -\frac32 g$ to drop the maximum;
the statement here needs no lower bound on $h$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, Lemme 9.4 and its proof, pp. 2100–2101, with $P$ defined on p. 2098 and $\kappa(A)$
on p. 2058, <https://doi.org/10.1215/00127094-2782528>. -/
theorem pow_mul_boundP_pow_le (g : ℕ) (hg : 1 ≤ g) {D h M : ℝ} (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hMQ : M ≤ max (h + log ((9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3)) / 2)
      1) :
    (9 * g : ℝ) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3) ≤
      ((14 * g : ℝ) ^ (64 * g ^ 2) * D * max h (max (log D) 1) ^ 2) ^ (2 ^ 10 * g ^ 3) := by
  have hB := add_le_of_le_max g hg hD hM hMQ
  set x : ℝ := (g : ℝ) with hxdef
  have hx1 : 1 ≤ x := by rw [hxdef]; exact_mod_cast hg
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  set Y := max h (max (log D) 1) with hYdef
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hYD : log D ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  -- The maximum in `P` is at most `83 · 2^11 g^6 Y`.
  have hm : max (M + 3 / 2 * x) (log (4 * (9 * x) ^ (4 * g) * D)) ≤ 169984 * x ^ 6 * Y := by
    refine max_le hB ?_
    have hl2 := log_two_lt_d9
    have hl9 := log_nine_le
    have hlx1 : log x ≤ x - 1 := log_le_sub_one_of_pos hx0
    have hx6 : x ^ 2 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
    rw [log_mul (by positivity) hD0.ne', log_mul (by norm_num) (by positivity), log_pow,
      log_mul (by norm_num) hx0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlx1 hx0.le, mul_le_mul_of_nonneg_left hl9 hx0.le,
      mul_le_mul_of_nonneg_left hl2.le hx0.le, mul_le_mul_of_nonneg_left hx1 hx0.le,
      mul_le_mul_of_nonneg_left hY1 (by positivity : (0 : ℝ) ≤ x ^ 6)]
  have hm0 : 0 ≤ max (M + 3 / 2 * x) (log (4 * (9 * x) ^ (4 * g) * D)) :=
    le_trans (by positivity) (le_max_left _ _)
  set c : ℝ := 4 * (9 * x) ^ (4 * g) * (8 * x) ^ (64 * g ^ 2) * 169984 ^ 2 * x ^ 12 with hcdef
  have hc0 : 0 ≤ c := by positivity
  -- Hence `P ≤ c D Y²`.
  have hP : boundP g D M ≤ c * (D * Y ^ 2) := by
    rw [boundP, ← hxdef, hcdef]
    have := pow_le_pow_left₀ hm0 hm 2
    have h0 : 0 ≤ 4 * (9 * x) ^ (4 * g) * (8 * x) ^ (64 * g ^ 2) * D := by positivity
    calc _ ≤ 4 * (9 * x) ^ (4 * g) * (8 * x) ^ (64 * g ^ 2) * D * (169984 * x ^ 6 * Y) ^ 2 :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hP0 : 0 ≤ boundP g D M := by
    rw [boundP, ← hxdef]
    positivity
  have hconst := const_le g hg
  rw [← hxdef, ← hcdef] at hconst
  calc (9 * x) ^ (96 * g ^ 4) * boundP g D M ^ (2 ^ 10 * g ^ 3)
      ≤ (9 * x) ^ (96 * g ^ 4) * (c * (D * Y ^ 2)) ^ (2 ^ 10 * g ^ 3) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hP _) (by positivity)
    _ = ((9 * x) ^ (3 * g) * c ^ 32) ^ (32 * g ^ 3) * (D * Y ^ 2) ^ (2 ^ 10 * g ^ 3) := by
        rw [mul_pow c, mul_pow _ (c ^ 32), ← pow_mul, ← pow_mul, ← mul_assoc,
          show 3 * g * (32 * g ^ 3) = 96 * g ^ 4 by ring,
          show 32 * (32 * g ^ 3) = 2 ^ 10 * g ^ 3 by ring]
    _ ≤ ((14 * x) ^ (2048 * g ^ 2)) ^ (32 * g ^ 3) * (D * Y ^ 2) ^ (2 ^ 10 * g ^ 3) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hconst _) (by positivity)
    _ = ((14 * x) ^ (64 * g ^ 2) * D * Y ^ 2) ^ (2 ^ 10 * g ^ 3) := by ring

end GaudronRemond
