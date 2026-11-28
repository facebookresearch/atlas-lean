/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumEventuallyPseudoGreedyGapEqZero
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion

/-!
# Eventual Sylvester recurrence for rational reciprocal sums

Let `a` be a sequence of positive integers with `aₙ² / aₙ₊₁ → 1` and a convergent rational
reciprocal sum. If the liminf of `(∏ k < n, aₖ) / aₙ * (1 - aₙ² / aₙ₊₁)` is nonnegative,
or if `aₙ₊₁ ≥ aₙ² - aₙ + 1` eventually, then `aₙ₊₁ = aₙ² - aₙ + 1` eventually. The
liminf condition is written as an eventual lower bound by `-δ` for each `δ > 0`.
Positivity makes the natural-number subtraction in the recurrence agree with subtraction
in the integers. Indices start at zero, rather than at one as in the paper.

After passing to a pseudo-greedy tail, the expansion recurrence gives the exact factor
relating the finite product of `1 - εₖ` to `(∏ k < n, aₖ) / aₙ`. This transfers the liminf
condition to the gaps. In the other case a negative gap could never approach zero. The
proof uses `exists_tail_eq_pseudoGreedyExpansion`, `eventually_pseudoGreedyGap_eq_zero`,
`pseudoGreedyExpansion_succ_eq`, and `pseudoGreedyGap_succ_eq_zero`.

## References

* Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential Sequences*,
  *INTEGERS* 26 (2026), Article A28, pp. 1–17, Corollary 4 (pp. 14–15), using Corollary 3,
  Lemmas 2–3, and Proposition 1. <https://math.colgate.edu/~integers/aa28/aa28.pdf>
* C. Badea, *A theorem on irrationality of infinite series and applications*, *Acta Arithmetica*
  63 (1993), no. 4, pp. 313–323, and P. Erdős and E. G. Straus, *On the irrationality of
  certain ahmes series*, *J. Indian Math. Soc.* 27 (1963), pp. 129–133: the original results
  credited in Corollary 4.
-/

open Filter Topology

namespace MetaMathlibExt

private theorem eventually_pseudoGreedyGap_eq_zero_of_tail_bounds {r : ℚ} (hr : 0 < r)
    {b : ℕ → ℝ} (hb : ∀ n, b n = (pseudoGreedyExpansion r n : ℝ))
    (hbpos : ∀ n, 0 < b n) (hlarge : ∀ᶠ n in atTop, 3 ≤ b n)
    (he : Tendsto (pseudoGreedyGap r) atTop (𝓝 0))
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ (∏ k ∈ Finset.range n, b k) / b n * (1 - b n ^ 2 / b (n + 1))) ∨
      ∀ᶠ n in atTop, b n ^ 2 - b n + 1 ≤ b (n + 1)) :
    ∀ᶠ n in atTop, pseudoGreedyGap r n = 0 := by
  let e := pseudoGreedyGap (r : ℝ)
  let u (n : ℕ) := b n - (1 - e n)
  have hrec (n : ℕ) : b (n + 1) = b n ^ 2 / (1 - e n) - b n + (1 - e (n + 1)) := by
    simpa only [hb, e, one_div_mul_eq_div] using
      pseudoGreedyExpansion_succ_eq (by exact_mod_cast hr) n
  have huRec (n : ℕ) : u (n + 1) + b n = b n ^ 2 / (1 - e n) := by
    dsimp only [u]
    linarith [hrec n]
  have heLower : ∀ᶠ n in atTop, -(1 / 2 : ℝ) < e n :=
    he.eventually (eventually_gt_nhds (by norm_num))
  have huLarge : ∀ᶠ n in atTop, b n ≤ 2 * u n := by
    filter_upwards [hlarge, heLower] with n hn hε
    dsimp only [u]
    linarith
  have hden {n : ℕ} (hn : 0 < u (n + 1)) : 0 < 1 - e n := by
    have hquot : 0 < b n ^ 2 / (1 - e n) := huRec n ▸ add_pos hn (hbpos n)
    exact (div_pos_iff_of_pos_left (pow_pos (hbpos n) 2)).mp hquot
  have hmul {n : ℕ} (hd : 0 < 1 - e n) : u (n + 1) * (1 - e n) = b n * u n := by
    have hEq := (eq_div_iff hd.ne').mp (huRec n)
    dsimp only [u] at hEq ⊢
    nlinarith only [hEq]
  -- Positivity at large indices propagates backwards using the recurrence.
  have hback {n : ℕ} (hn : 0 < u (n + 1)) : 0 < u n := by
    apply pos_of_mul_pos_left _ (hbpos n).le
    rw [mul_comm, ← hmul (hden hn)]
    exact mul_pos hn (hden hn)
  have huPos (n : ℕ) : 0 < u n := by
    obtain ⟨M, hM⟩ := eventually_atTop.mp huLarge
    have hM' : 0 < u (n + M) := by linarith [hbpos (n + M), hM (n + M) (by omega)]
    have down (k : ℕ) : 0 < u (n + k) → 0 < u n := by
      induction k with
      | zero => simp
      | succ k ih => exact fun hk => ih (hback hk)
    exact down M hM'
  have hd (n : ℕ) : 0 < 1 - e n := hden (huPos (n + 1))
  apply eventually_pseudoGreedyGap_eq_zero hr
  rcases h with h | h
  · left
    let P (n : ℕ) := ∏ k ∈ Finset.range n, (1 - e k)
    let W (n : ℕ) := (∏ k ∈ Finset.range n, b k) / b n
    have htel (n : ℕ) : P n * u n = u 0 * ∏ k ∈ Finset.range n, b k := by
      induction n with
      | zero => simp [P]
      | succ n ih =>
        simp only [P, Finset.prod_range_succ]
        calc
          _ = P n * (u (n + 1) * (1 - e n)) := by simp only [P]; ring
          _ = (P n * u n) * b n := by rw [hmul (hd n)]; ring
          _ = _ := by rw [ih]; ring
    have hfactor (n : ℕ) : P n = (u 0 * (b n / u n)) * W n := by
      have htel' := (eq_div_iff (huPos n).ne').mpr (htel n)
      rw [htel']
      dsimp only [W]
      field_simp [(hbpos n).ne', (huPos n).ne']
    have hsmallNext : ∀ᶠ n in atTop, -(1 / 2 : ℝ) < e (n + 1) :=
      (tendsto_add_atTop_nat 1).eventually heLower
    intro δ hδ
    have hK : 0 < 2 * u 0 := mul_pos (by norm_num) (huPos 0)
    filter_upwards [h (δ / (2 * u 0)) (div_pos hδ hK), hlarge, hsmallNext, huLarge]
      with n hn hbn hen hun
    have hratio : 1 - b n ^ 2 / b (n + 1) ≤ e n := by
      have hle : b (n + 1) ≤ b n ^ 2 / (1 - e n) := by linarith [hrec n]
      have hmul' := (le_div_iff₀ (hd n)).mp hle
      have hlo : 1 - e n ≤ b n ^ 2 / b (n + 1) := (le_div_iff₀ (hbpos (n + 1))).mpr
        (by rwa [mul_comm])
      linarith
    have hW : 0 ≤ W n := div_nonneg (Finset.prod_nonneg fun k _ => (hbpos k).le) (hbpos n).le
    have hC : 0 < u 0 * (b n / u n) := mul_pos (huPos 0) (div_pos (hbpos n) (huPos n))
    have hCmax : u 0 * (b n / u n) ≤ 2 * u 0 := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (huPos n)).mpr hun) (huPos 0).le
    change -δ ≤ e n * P n
    rw [hfactor]
    calc
      -δ = -(δ / (2 * u 0)) * (2 * u 0) := by rw [neg_mul, div_mul_cancel₀ _ hK.ne']
      _ ≤ -(δ / (2 * u 0)) * (u 0 * (b n / u n)) :=
        mul_le_mul_of_nonpos_left hCmax (neg_nonpos.mpr (div_nonneg hδ.le hK.le))
      _ ≤ (W n * (1 - b n ^ 2 / b (n + 1))) * (u 0 * (b n / u n)) :=
        mul_le_mul_of_nonneg_right hn hC.le
      _ ≤ (W n * e n) * (u 0 * (b n / u n)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hW) hC.le
      _ = _ := by ring
  · right
    have hstep : ∀ᶠ n in atTop, e n < 0 → e (n + 1) ≤ e n := by
      filter_upwards [h, hlarge, heLower] with n hn hbn hen hneg
      have hsquare : 1 - e n ≤ b n ^ 2 := by nlinarith [sq_nonneg (b n - 3)]
      have hfrac : e n * b n ^ 2 / (1 - e n) ≤ e n :=
        (div_le_iff₀ (hd n)).mpr (mul_le_mul_of_nonpos_left hsquare hneg.le)
      have hdiff : b n ^ 2 / (1 - e n) - b n ^ 2 = e n * b n ^ 2 / (1 - e n) := by
        field_simp [(hd n).ne']
        ring
      linarith [hrec n]
    obtain ⟨M, hM⟩ := eventually_atTop.mp hstep
    refine eventually_atTop.mpr ⟨M, fun n hn => ?_⟩
    by_contra! hneg
    have hstay (k : ℕ) : e (k + n) ≤ e n := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.succ_add]
        exact (hM (k + n) (by omega) (ih.trans_lt hneg)).trans ih
    exact hneg.not_ge (le_of_tendsto' (he.comp (tendsto_add_atTop_nat n)) hstay)

/-- **Erdős–Straus and Badea criterion for the Sylvester recurrence.** Let $(a_n)_{n \ge 0}$ be a
sequence of positive integers with $a_n^2 / a_{n+1} \to 1$ such that $\sum_n 1 / a_n$ converges
to a rational number. Suppose that
$\liminf_n (a_0 \cdots a_{n-1} / a_n)(1 - a_n^2 / a_{n+1}) \ge 0$, that is, for every
$\delta > 0$ this quantity is at least $-\delta$ for all sufficiently large $n$; or that
$a_{n+1} \ge a_n^2 - a_n + 1$ for all sufficiently large $n$. Then
$a_{n+1} = a_n^2 - a_n + 1$ for all sufficiently large $n$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 4 (`integers-2026-A28-cor-4`). -/
public theorem eventually_sylvester_recurrence_of_rational_sum {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1))
    (hrat : ∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q)
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ (∏ k ∈ Finset.range n, (a k : ℝ)) / a n * (1 - (a n : ℝ) ^ 2 / a (n + 1))) ∨
      ∀ᶠ n in atTop, a n ^ 2 - a n + 1 ≤ a (n + 1)) :
    ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1 := by
  obtain ⟨q, hsum⟩ := hrat
  obtain ⟨N, hN, he⟩ := exists_tail_eq_pseudoGreedyExpansion hpos hratio hsum.summable
  let b (n : ℕ) : ℝ := a (N + n)
  have hbpos (n : ℕ) : 0 < b n := Nat.cast_pos.mpr (hpos (N + n))
  let r : ℚ := q - ∑ k ∈ Finset.range N, 1 / (a k : ℚ)
  have hsumTail : HasSum (fun n => 1 / b n) (r : ℝ) := by
    simpa only [b, r, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
      Nat.add_comm N] using (hasSum_nat_add_iff' N).mpr hsum
  have hrReal : 0 < (r : ℝ) := hsumTail.tsum_eq ▸
    hsumTail.summable.tsum_pos (fun n => (one_div_pos.mpr (hbpos n)).le) 0
      (one_div_pos.mpr (hbpos 0))
  have hr : 0 < r := by exact_mod_cast hrReal
  rw [hsumTail.tsum_eq] at hN he
  have hb (n : ℕ) : b n = (pseudoGreedyExpansion r n : ℝ) := by
    dsimp only [b]
    exact_mod_cast hN n
  have hlarge : ∀ᶠ n in atTop, 3 ≤ b n := by
    filter_upwards [hsumTail.summable.tendsto_atTop_zero.eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 3 by norm_num))] with n hn
    exact ((one_div_lt_one_div (hbpos n) (by norm_num)).mp hn).le
  have hsq (n : ℕ) : a n ≤ a n ^ 2 := Nat.le_self_pow (by decide) _
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
    simpa only [Nat.add_comm N] using tendsto_add_atTop_nat N
  have hTail : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      -δ ≤ (∏ k ∈ Finset.range n, b k) / b n * (1 - b n ^ 2 / b (n + 1))) ∨
      ∀ᶠ n in atTop, b n ^ 2 - b n + 1 ≤ b (n + 1) := by
    rcases h with h | h
    · left
      let C : ℝ := ∏ k ∈ Finset.range N, (a k : ℝ)
      have hC : 0 < C := Finset.prod_pos fun k _ => by exact_mod_cast hpos k
      intro δ hδ
      filter_upwards [hshift.eventually (h (δ * C) (mul_pos hδ hC))] with n hn
      change -(δ * C) ≤ (∏ k ∈ Finset.range (N + n), (a k : ℝ)) / a (N + n) *
        (1 - (a (N + n) : ℝ) ^ 2 / a (N + n + 1)) at hn
      rw [Finset.prod_range_add, ← neg_mul] at hn
      apply (mul_le_mul_iff_right₀ hC).mp
      rw [mul_comm C (-δ)]
      calc
        -δ * C ≤ (C * ∏ k ∈ Finset.range n, b k) / b n * (1 - b n ^ 2 / b (n + 1)) := hn
        _ = _ := by ring
    · right
      filter_upwards [hshift.eventually h] with n hn
      change a (N + n) ^ 2 - a (N + n) + 1 ≤ a (N + n + 1) at hn
      have hcast := (Nat.cast_le (α := ℝ)).mpr hn
      simpa only [b, Nat.add_assoc, Nat.cast_add, Nat.cast_sub (hsq _), Nat.cast_pow,
        Nat.cast_one] using hcast
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_pseudoGreedyGap_eq_zero_of_tail_bounds hr hb hbpos hlarge he hTail)
  refine eventually_atTop.mpr ⟨N + M, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
  have hz := hM k (by omega)
  have hrec := pseudoGreedyExpansion_succ_eq hrReal k
  rw [hz, pseudoGreedyGap_succ_eq_zero hrReal hz, sub_zero, div_one,
    one_mul, ← hb (k + 1), ← hb k] at hrec
  apply (Nat.cast_inj (R := ℝ)).mp
  simpa only [b, Nat.add_assoc, Nat.cast_add, Nat.cast_sub (hsq _), Nat.cast_pow,
    Nat.cast_one] using hrec

end MetaMathlibExt
