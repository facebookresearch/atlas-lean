/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SanfordSymmetricSeries

/-!
# Bridgeman's dilogarithm series for a positive Pell solution

We derive the Rogers dilogarithm series from Sanford's symmetric series using the conjugate
Pell roots, and prove the divisibility of the coefficients for integral solutions.
-/

open Real

namespace MetaMathlibExt

/-- **Bridgeman's dilogarithm series for a positive Pell solution.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $n$ be a natural number that is not a perfect square, let
$a, b$ be positive rationals with $a^2 - n b^2 = 1$, and put $u = a + b\sqrt{n}$. Define rationals
$a_k, b_k$ by $a_0 = 1$, $b_0 = 0$, $a_{k+1} = a a_k + n b b_k$ and $b_{k+1} = b a_k + a b_k$,
so that $u^k = a_k + b_k\sqrt{n}$. Then
$$
L(1/u^2) = \sum_{k \ge 2} L(b^2/b_k^2),
$$
and if $a$ and $b$ are integers, then for every $k \ge 0$ there is an integer $m$ with $b_k = bm$.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 3 (3), quoting Bridgeman (`integers-2025-A52-thm-3`). -/
public theorem rogersDilog_pell_positive_series {n : ℕ} (hn : ¬ IsSquare n) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hpell : a ^ 2 - n * b ^ 2 = 1) {A B : ℕ → ℚ}
    (hA₀ : A 0 = 1) (hB₀ : B 0 = 0) (hA : ∀ k, A (k + 1) = a * A k + n * b * B k)
    (hB : ∀ k, B (k + 1) = b * A k + a * B k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / ((a : ℝ) + b * √n) ^ 2) = ∑' k : ℕ, L ((b : ℝ) ^ 2 / (B (k + 2) : ℝ) ^ 2) ∧
      ((∃ a' b' : ℤ, a = a' ∧ b = b') → ∀ k, ∃ m : ℤ, B k = b * m) := by
  intro L
  constructor
  · let s : ℝ := b * √n
    let u : ℝ := a + s
    let v : ℝ := a - s
    let c : ℝ := 2 * a
    let t : ℝ := 2 * s / c
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hn₀ : n ≠ 0 := fun h => hn (h ▸ IsSquare.zero)
    have hsqrt : 0 < √(n : ℝ) := sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn₀)
    have hsqrt_sq : (√(n : ℝ)) ^ 2 = n := sq_sqrt (Nat.cast_nonneg _)
    have hs : 0 < s := mul_pos hbR hsqrt
    have hu : 0 < u := add_pos haR hs
    have hc : 0 < c := mul_pos (by norm_num) haR
    have huv : u * v = 1 := by
      have hpellR : (a : ℝ) ^ 2 - n * (b : ℝ) ^ 2 = 1 := by exact_mod_cast hpell
      change ((a : ℝ) + s) * ((a : ℝ) - s) = 1
      rw [← sq_sub_sq]
      simpa only [s, mul_pow, hsqrt_sq, mul_comm ((b : ℝ) ^ 2)] using hpellR
    have hv : v = 1 / u := (eq_div_iff hu.ne').2 (by rw [mul_comm, huv])
    have hv₀ : 0 < v := hv ▸ div_pos one_pos hu
    have ht₀ : 0 < t := div_pos (mul_pos (by norm_num) hs) hc
    have ht₁ : t < 1 := (div_lt_one hc).2 (by
      change 0 < (a : ℝ) - s at hv₀
      change 2 * s < 2 * (a : ℝ)
      linarith)
    have hminus : 1 / 2 - t / 2 = v / c := by
      dsimp [t, v, c]
      field_simp
    have hplus : 1 / 2 + t / 2 = u / c := by
      dsimp [t, u, c]
      field_simp
    have hr : (1 - t) / (1 + t) = 1 / u ^ 2 := by
      rw [show 1 - t = 2 * (1 / 2 - t / 2) by ring,
        show 1 + t = 2 * (1 / 2 + t / 2) by ring, mul_div_mul_left _ _ (by norm_num),
        hminus, hplus, div_div_div_cancel_right₀ hc.ne', hv, div_div, pow_two]
    -- The recurrence gives the powers of both conjugates.
    have hpowers (k : ℕ) :
        (A k : ℝ) + (B k : ℝ) * √n = u ^ k ∧
          (A k : ℝ) - (B k : ℝ) * √n = v ^ k := by
      induction k with
      | zero => simp [hA₀, hB₀]
      | succ k ih =>
        have hAk : (A (k + 1) : ℝ) = a * (A k : ℝ) + n * (b : ℝ) * (B k : ℝ) := by
          exact_mod_cast hA k
        have hBk : (B (k + 1) : ℝ) = b * (A k : ℝ) + a * (B k : ℝ) := by
          exact_mod_cast hB k
        rw [← hsqrt_sq] at hAk
        rw [hAk, hBk, pow_succ u k, pow_succ v k, ← ih.1, ← ih.2]
        dsimp only [u, v, s]
        constructor <;> ring
    have harg (k : ℕ) :
        t ^ 2 * (1 / 2 - t / 2) ^ (k + 1) * (1 / 2 + t / 2) ^ (k + 1) /
          ((1 / 2 + t / 2) ^ (k + 2) - (1 / 2 - t / 2) ^ (k + 2)) ^ 2 =
        (b : ℝ) ^ 2 / (B (k + 2) : ℝ) ^ 2 := by
      have hnum : t ^ 2 * (v / c) ^ (k + 1) * (u / c) ^ (k + 1) =
          (2 * s) ^ 2 / (c ^ (k + 2)) ^ 2 := by
        rw [mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm v u, huv, ← sq c,
          div_pow (1 : ℝ) (c ^ 2), one_pow, pow_right_comm c 2 (k + 1)]
        change ((2 * s) / c) ^ 2 * (1 / (c ^ (k + 1)) ^ 2) = _
        rw [div_pow, div_mul_div_comm, mul_one, ← mul_pow, ← pow_succ']
      have hdiff : u ^ (k + 2) - v ^ (k + 2) = (2 * √(n : ℝ)) * (B (k + 2) : ℝ) := by
        rw [← (hpowers (k + 2)).1, ← (hpowers (k + 2)).2]
        ring
      have hfactor : 2 * √(n : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hsqrt.ne'
      rw [hminus, hplus, hnum, div_pow, div_pow, ← sub_div, div_pow,
        div_div_div_cancel_right₀ (pow_ne_zero 2 (pow_ne_zero _ hc.ne')), hdiff,
        show 2 * s = (2 * √(n : ℝ)) * (b : ℝ) by dsimp [s]; ring,
        mul_pow (2 * √(n : ℝ)), mul_pow (2 * √(n : ℝ)),
        mul_div_mul_left _ _ (pow_ne_zero 2 hfactor)]
    have hseries := rogersDilog_sanford_symmetric_series ht₀ ht₁
    change (∑' k : ℕ, L (t ^ 2 * (1 / 2 - t / 2) ^ (k + 1) * (1 / 2 + t / 2) ^ (k + 1) /
      ((1 / 2 + t / 2) ^ (k + 2) - (1 / 2 - t / 2) ^ (k + 2)) ^ 2)) =
        L ((1 - t) / (1 + t)) at hseries
    rw [hr] at hseries
    exact hseries.symm.trans (tsum_congr fun k => congrArg L (harg k))
  · rintro ⟨a', b', ha', hb'⟩ k
    suffices ∃ x m : ℤ, A k = x ∧ B k = b * m by
      obtain ⟨_, m, _, hm⟩ := this
      exact ⟨m, hm⟩
    induction k with
    | zero => exact ⟨1, 0, by simp [hA₀], by simp [hB₀]⟩
    | succ k ih =>
      obtain ⟨x, m, hx, hm⟩ := ih
      refine ⟨a' * x + n * b' ^ 2 * m, x + a' * m, ?_, ?_⟩
      · rw [hA, hx, hm, ha', hb']
        push_cast
        ring
      · rw [hB, hx, hm, ha']
        push_cast
        ring

end MetaMathlibExt
