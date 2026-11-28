/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Logic.Equiv.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import MathlibExt.NumberTheory.SanfordSymmetricSeries

/-!
# Bridgeman's dilogarithm series for a negative Pell solution

For nonsquare $n \in \mathbb N$ and positive $a,b \in \mathbb Q$ with $a^2-nb^2=-1$,
we split Sanford's symmetric dilogarithm series into even and odd powers of
$u=a+b\sqrt n$. Their coefficients are determined by multiplying by $u$ from
$(a_0,b_0)=(1,0)$. When $a,b$ are integers, multiplication by $u^2$ preserves the
divisibility by $a$ of the even-indexed second coordinates; multiplication once more by $u$
gives the corresponding divisibility of the odd-indexed first coordinates.

## References

* Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
  INTEGERS 25 (2025), Article A52, pp. 1–15, Theorem 3, equation (4), and Corollary 1.
* Martin Bridgeman, *Dilogarithm identities for solutions to Pell’s equation in terms of continued
  fraction convergents*, The Ramanujan Journal 55 (2021), pp. 141–161, Theorem 2.3.
* The conjugate-power induction and normalization of Sanford's parameter adapt
  `rogersDilog_pell_positive_series` in `MathlibExt.NumberTheory.BridgemanPellPositiveSeries`.
-/

open Real

namespace MetaMathlibExt

/-- **Bridgeman's dilogarithm series for a negative Pell solution.** Write
$L(x) = \sum_{m \ge 1} x^m/m^2 + \frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on
$[0, 1]$ (with $\log 0 = 0$). Let $n$ be a natural number that is not a perfect square, let
$a, b$ be positive rationals with $a^2 - n b^2 = -1$, and put $u = a + b\sqrt{n}$. Define rationals
$a_k, b_k$ by $a_0 = 1$, $b_0 = 0$, $a_{k+1} = a a_k + n b b_k$ and $b_{k+1} = b a_k + a b_k$,
so that $u^k = a_k + b_k\sqrt{n}$. Then
$$
L(1/u^2) = \sum_{k \ge 1} L\left(\frac{a^2}{n b_{2k}^2}\right) +
\sum_{k \ge 1} L\left(\frac{a^2}{a_{2k+1}^2}\right),
$$
and if $a$ and $b$ are integers, then for every $k \ge 0$ both $b_{2k}/a$ and $a_{2k+1}/a$ are
integers.

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Theorem 3 (4), quoting Bridgeman (`integers-2025-A52-thm-3`). -/
public theorem rogersDilog_pell_negative_series {n : ℕ} (hn : ¬ IsSquare n) {a b : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hpell : a ^ 2 - n * b ^ 2 = -1) {A B : ℕ → ℚ}
    (hA₀ : A 0 = 1) (hB₀ : B 0 = 0) (hA : ∀ k, A (k + 1) = a * A k + n * b * B k)
    (hB : ∀ k, B (k + 1) = b * A k + a * B k) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / ((a : ℝ) + b * √n) ^ 2) =
        ∑' k : ℕ, L ((a : ℝ) ^ 2 / (n * (B (2 * (k + 1)) : ℝ) ^ 2)) +
          ∑' k : ℕ, L ((a : ℝ) ^ 2 / (A (2 * (k + 1) + 1) : ℝ) ^ 2) ∧
      ((∃ a' b' : ℤ, a = a' ∧ b = b') →
        ∀ k, (∃ m : ℤ, B (2 * k) = a * m) ∧ ∃ m : ℤ, A (2 * k + 1) = a * m) := by
  intro L
  constructor
  · let s : ℝ := b * √n
    let u : ℝ := a + s
    let v : ℝ := s - a
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hn₀ : n ≠ 0 := fun h => hn (h ▸ IsSquare.zero)
    have hsqrt : 0 < √(n : ℝ) := sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn₀)
    have hsq : (√(n : ℝ)) ^ 2 = n := sq_sqrt (Nat.cast_nonneg _)
    have hu : 0 < u := add_pos haR (mul_pos hbR hsqrt)
    have huv : u * v = 1 := by
      have hpellR : (a : ℝ) ^ 2 - n * (b : ℝ) ^ 2 = -1 := by exact_mod_cast hpell
      have hsSq : s ^ 2 = n * (b : ℝ) ^ 2 := by
        dsimp only [s]
        rw [mul_pow, hsq, mul_comm]
      calc
        u * v = s ^ 2 - (a : ℝ) ^ 2 := by dsimp only [u, v]; ring
        _ = 1 := by rw [hsSq]; linarith
    have hv : v = 1 / u := (eq_div_iff hu.ne').2 (by rw [mul_comm, huv])
    have hv₀ : 0 < v := hv ▸ div_pos one_pos hu
    have hdiff : u - v = 2 * (a : ℝ) := by dsimp only [u, v]; ring
    have hvu : v < u := sub_pos.mp (hdiff ▸ mul_pos (by norm_num) haR)
    let c := u + v
    let t := (u - v) / c
    have hc : 0 < c := add_pos hu hv₀
    have ht₀ : 0 < t := div_pos (sub_pos.mpr hvu) hc
    have ht₁ : t < 1 := (div_lt_one hc).2 (by dsimp only [c]; linarith)
    have hminus : 1 / 2 - t / 2 = v / c := by dsimp only [t, c]; field_simp [hc.ne']; ring
    have hplus : 1 / 2 + t / 2 = u / c := by dsimp only [t, c]; field_simp [hc.ne']; ring
    have hratio : (1 - t) / (1 + t) = v / u := by
      rw [show 1 - t = 2 * (1 / 2 - t / 2) by ring, show 1 + t = 2 * (1 / 2 + t / 2) by ring,
        mul_div_mul_left _ _ (by norm_num), hminus, hplus, div_div_div_cancel_right₀ hc.ne']
    have hleft : v / u = 1 / u ^ 2 := by rw [hv, div_div, pow_two]
    let f (k : ℕ) := L ((u - v) ^ 2 / (u ^ (k + 2) - v ^ (k + 2)) ^ 2)
    have hseries : (∑' k, f k) = L (v / u) := by
      rw [← hratio]
      refine (tsum_congr fun k => ?_).symm.trans (rogersDilog_sanford_symmetric_series ht₀ ht₁)
      change L (t ^ 2 * (1 / 2 - t / 2) ^ (k + 1) * (1 / 2 + t / 2) ^ (k + 1) /
        ((1 / 2 + t / 2) ^ (k + 2) - (1 / 2 - t / 2) ^ (k + 2)) ^ 2) = f k
      have hnum : t ^ 2 * (v / c) ^ (k + 1) * (u / c) ^ (k + 1) =
          (u - v) ^ 2 / (c ^ (k + 2)) ^ 2 := by
        rw [mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm v u, huv, ← sq c,
          div_pow (1 : ℝ) (c ^ 2), one_pow, pow_right_comm c 2 (k + 1)]
        dsimp only [t]
        rw [div_pow, div_mul_div_comm, mul_one, ← mul_pow, ← pow_succ']
      rw [hminus, hplus, hnum, div_pow, div_pow, ← sub_div, div_pow,
        div_div_div_cancel_right₀ (pow_ne_zero 2 (pow_ne_zero _ hc.ne'))]
    -- A nonzero value of the totalized sum certifies summability before reindexing.
    have hpos : 0 < L (v / u) := by
      have hr₀ := div_pos hv₀ hu
      have hr₁ := (div_lt_one hu).2 hvu
      have hLi := (hasSum_li2PowerSeries (by rwa [abs_of_pos hr₀])).summable
      have hLi' : Summable (fun k : ℕ => (v / u) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hLi
      exact add_pos_of_pos_of_nonneg
        (hLi'.tsum_pos (fun k => div_nonneg (pow_nonneg hr₀.le _) (sq_nonneg _)) 0 (by positivity))
        (div_nonneg (mul_nonneg_of_nonpos_of_nonpos (log_nonpos hr₀.le hr₁.le)
          (log_nonpos (sub_nonneg.mpr hr₁.le) (sub_le_self _ hr₀.le))) (by norm_num))
    have hf : Summable f := by
      by_contra h
      rw [tsum_eq_zero_of_not_summable h] at hseries
      exact hpos.ne' hseries.symm
    -- Since the true conjugate is `-v`, even and odd powers select different coordinates.
    have hpowers (k : ℕ) :
        (A k : ℝ) + (B k : ℝ) * √n = u ^ k ∧
          (A k : ℝ) - (B k : ℝ) * √n = (-v) ^ k := by
      induction k with
      | zero => simp [hA₀, hB₀]
      | succ k ih =>
        have hAk : (A (k + 1) : ℝ) = a * (A k : ℝ) + n * (b : ℝ) * (B k : ℝ) := by
          exact_mod_cast hA k
        have hBk : (B (k + 1) : ℝ) = b * (A k : ℝ) + a * (B k : ℝ) := by
          exact_mod_cast hB k
        rw [← hsq] at hAk
        rw [hAk, hBk, pow_succ u k, pow_succ (-v) k, ← ih.1, ← ih.2]
        dsimp only [u, v, s]
        constructor <;> ring
    have heven (k : ℕ) : f (2 * k) = L ((a : ℝ) ^ 2 / (n * (B (2 * (k + 1)) : ℝ) ^ 2)) := by
      let j := 2 * (k + 1)
      have hneg : (-v) ^ j = v ^ j := (even_two_mul (k + 1)).neg_pow _
      have hj : u ^ j - v ^ j = 2 * ((B j : ℝ) * √n) := by
        rw [← hneg, ← (hpowers j).1, ← (hpowers j).2]
        ring
      change L ((u - v) ^ 2 / (u ^ (2 * k + 2) - v ^ (2 * k + 2)) ^ 2) = _
      rw [show 2 * k + 2 = j by dsimp only [j]; omega, hj, hdiff, mul_pow, mul_pow 2,
        mul_div_mul_left _ _ (by norm_num), mul_pow, hsq, mul_comm ((B j : ℝ) ^ 2)]
    have hodd (k : ℕ) : f (2 * k + 1) = L ((a : ℝ) ^ 2 / (A (2 * (k + 1) + 1) : ℝ) ^ 2) := by
      let j := 2 * (k + 1) + 1
      have hneg : (-v) ^ j = -(v ^ j) := (odd_two_mul_add_one (k + 1)).neg_pow _
      have hj : u ^ j - v ^ j = 2 * (A j : ℝ) := by
        rw [sub_eq_add_neg, ← hneg, ← (hpowers j).1, ← (hpowers j).2]
        ring
      change L ((u - v) ^ 2 / (u ^ (2 * k + 1 + 2) - v ^ (2 * k + 1 + 2)) ^ 2) = _
      rw [show 2 * k + 1 + 2 = j by dsimp only [j]; omega, hj, hdiff, mul_pow, mul_pow 2,
        mul_div_mul_left _ _ (by norm_num)]
    let e := Equiv.natSumNatEquivNat
    have split := Summable.tsum_sum (f := f ∘ e)
      (hf.comp_injective (e.injective.comp Sum.inl_injective))
      (hf.comp_injective (e.injective.comp Sum.inr_injective))
    rw [hleft] at hseries
    rw [← hseries, ← e.tsum_eq f]
    simpa only [e, Function.comp_apply, Equiv.natSumNatEquivNat_apply, Sum.elim_inl,
      Sum.elim_inr, heven, hodd] using split
  · rintro ⟨a', b', ha', hb'⟩ k
    have heven (k : ℕ) : ∃ x m : ℤ, A (2 * k) = x ∧ B (2 * k) = a * m := by
      induction k with
      | zero => exact ⟨1, 0, by simp [hA₀], by simp [hB₀]⟩
      | succ k ih =>
        obtain ⟨x, m, hx, hm⟩ := ih
        let c : ℤ := a' ^ 2 + n * b' ^ 2
        refine ⟨c * x + 2 * n * a' ^ 2 * b' * m, 2 * b' * x + c * m, ?_, ?_⟩ <;>
          rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
        · rw [hA, hA, hB, hx, hm, ha', hb']
          dsimp only [c]
          push_cast
          ring
        · rw [hB, hA, hB, hx, hm, ha', hb']
          dsimp only [c]
          push_cast
          ring
    obtain ⟨x, m, hx, hm⟩ := heven k
    refine ⟨⟨m, hm⟩, ⟨x + n * b' * m, ?_⟩⟩
    rw [hA, hx, hm, hb']
    push_cast
    ring

end MetaMathlibExt
