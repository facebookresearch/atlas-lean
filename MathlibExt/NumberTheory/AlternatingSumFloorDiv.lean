/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Alternating sums of floor quotients along an increasing sequence

Let `0 ≤ ν < 1` and let `b 0 < b 1 < b 2 < ⋯` be real numbers with `1 ≤ b k` and `k ≤ b k`.
`MetaMathlibExt.alternating_sum_floor_div_eq_add_bigO` (Dent and Shor) states that, with both
sums over the integers `0 ≤ k ≤ n - ν`,
`∑ (-1) ^ k * ⌊(n - ν) / b k⌋ = n * ∑ (-1) ^ k / b k + O(√n)`.

`AlternatingSumFloorDiv.abs_sub_le_six_mul_sqrt` proves this with the explicit constant `6`,
whatever `b` and `ν` are, for every monotone `b` (not necessarily strictly increasing) with these
bounds.

The bound rests on a finite form of the alternating series estimate: the partial sums
`∑_{j < L} (-1) ^ j * f j` of an antitone nonnegative sequence lie in `[0, f 0]`
(`AlternatingSumFloorDiv.sum_range_neg_one_pow_mul_mem_Icc`), so an alternating sum of such a
sequence over an interval `[m, N)` is at most `f m` in absolute value
(`AlternatingSumFloorDiv.abs_sum_Ico_neg_one_pow_mul_le`).

## Proof

Write `x = n - ν`, so that `n - 1 < x ≤ n`, and split the sum at `K = ⌊√n⌋₊ + 1`, so that
`√n < K ≤ √n + 1`.

* For `k < K`, the term `⌊x / b k⌋ - n / b k` lies in `(-2, 0]`, so these terms contribute
  at most `2 * K` in absolute value.
* For `k ≥ K`, both `k ↦ ⌊x / b k⌋` and `k ↦ n / b k` are antitone and nonnegative, so their
  alternating sums over the remaining interval are at most their first terms, both bounded by
  `n / b K ≤ n / K < √n`.

Hence the difference is at most `2 * K + 2 * n / K ≤ 6 * √n`.

The paper's proof goes through a real-divisor reformulation of the floor quotients and
Dirichlet's hyperbola method instead.

## References

* Nicholas Dent and Caleb M. Shor, *On residues of rounded shifted fractions with a common
  numerator*, arXiv:2206.15452v2, Proposition 4.8; published in Journal of Integer Sequences 27
  (2024), Article 24.2.5.
-/

public section

namespace MetaMathlibExt

namespace AlternatingSumFloorDiv

/-- The partial sums `∑_{j < L} (-1) ^ j * f j` of the alternating series of an antitone sequence
of nonnegative reals lie between `0` and the first term `f 0`. -/
theorem sum_range_neg_one_pow_mul_mem_Icc {f : ℕ → ℝ} (hf : Antitone f) (hf0 : ∀ k, 0 ≤ f k)
    (L : ℕ) : ∑ j ∈ Finset.range L, (-1) ^ j * f j ∈ Set.Icc 0 (f 0) := by
  induction L generalizing f with
  | zero => simp [hf0 0]
  | succ L ih =>
    have h := ih (f := fun j => f (j + 1)) (fun a b hab => hf (by omega)) (fun k => hf0 _)
    have h01 : f 1 ≤ f 0 := hf zero_le_one
    have hsum : ∑ j ∈ Finset.range (L + 1), (-1 : ℝ) ^ j * f j =
        f 0 - ∑ j ∈ Finset.range L, (-1) ^ j * f (j + 1) := by
      rw [Finset.sum_range_succ', sub_eq_neg_add, ← Finset.sum_neg_distrib]
      simp [pow_succ]
    rw [hsum]
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- An alternating sum of an antitone sequence of nonnegative reals over an interval `[m, N)` is
bounded in absolute value by its first term `f m`; for `N ≤ m` the sum is empty. -/
theorem abs_sum_Ico_neg_one_pow_mul_le {f : ℕ → ℝ} (hf : Antitone f) (hf0 : ∀ k, 0 ≤ f k)
    (m N : ℕ) : |∑ k ∈ Finset.Ico m N, (-1) ^ k * f k| ≤ f m := by
  have h := sum_range_neg_one_pow_mul_mem_Icc (f := fun j => f (m + j))
    (fun a b hab => hf (by omega)) (fun k => hf0 _) (N - m)
  rw [Finset.sum_Ico_eq_sum_range]
  have hfac : ∑ j ∈ Finset.range (N - m), (-1 : ℝ) ^ (m + j) * f (m + j) =
      (-1) ^ m * ∑ j ∈ Finset.range (N - m), (-1) ^ j * f (m + j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  rw [hfac, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg h.1]
  simpa using h.2

/-- Explicit form of `MetaMathlibExt.alternating_sum_floor_div_eq_add_bigO`, for a monotone
sequence: if `0 ≤ ν < 1` and `b` is monotone with `1 ≤ b k` and `k ≤ b k` for every `k`, then for
every `n ≥ 1`, with both sums over the natural numbers `k ≤ n - ν`,
`|∑ ⌊(n - ν) / b k⌋ * (-1) ^ k - n * ∑ (-1) ^ k / b k| ≤ 6 * √n`. -/
theorem abs_sub_le_six_mul_sqrt {ν : ℝ} (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) {b : ℕ → ℝ}
    (hb : Monotone b) (hb₁ : ∀ k, 1 ≤ b k) (hbk : ∀ k : ℕ, (k : ℝ) ≤ b k) {n : ℕ}
    (hn : 1 ≤ n) :
    |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
          (⌊((n : ℝ) - ν) / b k⌋ : ℝ) * (-1) ^ k) -
        n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
          (-1) ^ k / b k| ≤ 6 * Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := zero_le_one.trans hn1
  set x : ℝ := (n : ℝ) - ν with hx
  have hx0 : 0 ≤ x := by linarith
  have hxn : x ≤ n := by linarith
  have hbpos : ∀ k, 0 < b k := fun k => one_pos.trans_le (hb₁ k)
  set S := (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x) with hS
  -- Combine the two sums into one alternating sum of the errors `⌊x / b k⌋ - n / b k`.
  have hdiff : (∑ k ∈ S, (⌊x / b k⌋ : ℝ) * (-1) ^ k) - n * ∑ k ∈ S, (-1) ^ k / b k =
      ∑ k ∈ S, (-1) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdiff]
  -- Split the range of summation at `K = ⌊√n⌋₊ + 1`.
  set K : ℕ := ⌊Real.sqrt n⌋₊ + 1 with hK
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => K ≤ k)]
  have hS_hi : S.filter (fun k => K ≤ k) = Finset.Ico K (⌊x⌋₊ + 1) := by
    ext k
    simp only [hS, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨_, hkx⟩, hKk⟩
      exact ⟨hKk, Nat.lt_succ_of_le (Nat.le_floor hkx)⟩
    · rintro ⟨hKk, hk⟩
      have hk' : (k : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 (Nat.lt_succ_iff.1 hk)
      have hkn : (k : ℝ) ≤ n := hk'.trans hxn
      exact ⟨⟨Nat.lt_succ_of_le (by exact_mod_cast hkn), hk'⟩, hKk⟩
  -- The sequences `⌊x / b k⌋` and `n / b k` are antitone and nonnegative.
  have hanti_div : ∀ {y : ℝ}, 0 ≤ y → Antitone fun k => y / b k := fun hy i j hij =>
    div_le_div_of_nonneg_left hy (hbpos i) (hb hij)
  have hfloor_anti : Antitone fun k => (⌊x / b k⌋ : ℝ) := fun i j hij =>
    Int.cast_mono (Int.floor_mono (hanti_div hx0 hij))
  have hfloor_nonneg : ∀ k, 0 ≤ (⌊x / b k⌋ : ℝ) := fun k =>
    Int.cast_nonneg (Int.floor_nonneg.2 (div_nonneg hx0 (hbpos k).le))
  have hdiv_nonneg : ∀ k, 0 ≤ (n : ℝ) / b k := fun k => div_nonneg hn0 (hbpos k).le
  -- Bounds on `K`: `√n < K ≤ √n + 1`, hence `n / b K ≤ n / K ≤ √n`.
  have hsqrt1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 hn1
  have hKsqrt : Real.sqrt n < K := by
    rw [hK]
    push_cast
    exact Nat.lt_floor_add_one _
  have hKle : (K : ℝ) ≤ Real.sqrt n + 1 := by
    rw [hK]
    push_cast
    linarith [Nat.floor_le (Real.sqrt_nonneg (n : ℝ))]
  have hKpos : (0 : ℝ) < K := (zero_lt_one.trans_le hsqrt1).trans hKsqrt
  have hnK : (n : ℝ) / K ≤ Real.sqrt n := by
    calc (n : ℝ) / K ≤ n / Real.sqrt n :=
          div_le_div_of_nonneg_left hn0 (zero_lt_one.trans_le hsqrt1) hKsqrt.le
      _ = Real.sqrt n := Real.div_sqrt
  have hbK : (n : ℝ) / b K ≤ n / K := div_le_div_of_nonneg_left hn0 hKpos (hbk K)
  -- The terms with `k ≥ K`: two alternating sums of antitone nonnegative sequences.
  have hhi : |∑ k ∈ S.filter (fun k => K ≤ k), (-1) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k)| ≤
      2 * (n / K) := by
    rw [hS_hi]
    have e : ∑ k ∈ Finset.Ico K (⌊x⌋₊ + 1), (-1 : ℝ) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k) =
        ∑ k ∈ Finset.Ico K (⌊x⌋₊ + 1), (-1 : ℝ) ^ k * (⌊x / b k⌋ : ℝ) -
          ∑ k ∈ Finset.Ico K (⌊x⌋₊ + 1), (-1 : ℝ) ^ k * (n / b k) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e]
    have h1 := abs_sum_Ico_neg_one_pow_mul_le hfloor_anti hfloor_nonneg K (⌊x⌋₊ + 1)
    have h2 := abs_sum_Ico_neg_one_pow_mul_le (hanti_div hn0) hdiv_nonneg K (⌊x⌋₊ + 1)
    have h3 : (⌊x / b K⌋ : ℝ) ≤ n / b K :=
      (Int.floor_le _).trans (div_le_div_of_nonneg_right hxn (hbpos K).le)
    calc _ ≤ |∑ k ∈ Finset.Ico K (⌊x⌋₊ + 1), (-1 : ℝ) ^ k * (⌊x / b k⌋ : ℝ)| +
          |∑ k ∈ Finset.Ico K (⌊x⌋₊ + 1), (-1 : ℝ) ^ k * (n / b k)| := abs_sub _ _
      _ ≤ 2 * (n / K) := by linarith
  -- The terms with `k < K`: at most `K` terms, each of absolute value at most `2`.
  have hlo : |∑ k ∈ S.filter (fun k => ¬ K ≤ k), (-1) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k)| ≤
      2 * K := by
    have hcard : (S.filter (fun k => ¬ K ≤ k)).card ≤ K := by
      calc (S.filter (fun k => ¬ K ≤ k)).card ≤ (Finset.range K).card := by
            refine Finset.card_le_card fun k hk => ?_
            simp only [Finset.mem_filter, not_le] at hk
            exact Finset.mem_range.2 hk.2
        _ = K := Finset.card_range K
    have hterm : ∀ k ∈ S.filter (fun k => ¬ K ≤ k),
        |(-1 : ℝ) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k)| ≤ 2 := by
      intro k _
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_le]
      have hfl := Int.floor_le (x / b k)
      have hlt := Int.lt_floor_add_one (x / b k)
      have hxb : x / b k ≤ n / b k := div_le_div_of_nonneg_right hxn (hbpos k).le
      have hnb : (n : ℝ) / b k - x / b k ≤ 1 := by
        rw [← sub_div, div_le_one (hbpos k)]
        linarith [hb₁ k]
      constructor <;> linarith
    calc _ ≤ ∑ k ∈ S.filter (fun k => ¬ K ≤ k), |(-1 : ℝ) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ S.filter (fun k => ¬ K ≤ k), (2 : ℝ) := Finset.sum_le_sum hterm
      _ = 2 * (S.filter (fun k => ¬ K ≤ k)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ 2 * K := by gcongr
  calc _ ≤ |∑ k ∈ S.filter (fun k => K ≤ k), (-1) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k)| +
        |∑ k ∈ S.filter (fun k => ¬ K ≤ k), (-1) ^ k * ((⌊x / b k⌋ : ℝ) - n / b k)| :=
        abs_add_le _ _
    _ ≤ 2 * (n / K) + 2 * K := add_le_add hhi hlo
    _ ≤ 6 * Real.sqrt n := by linarith

end AlternatingSumFloorDiv

/-- **Alternating sums of floor quotients along an increasing sequence.** Let $0 \le \nu < 1$
and let $b_0, b_1, b_2, \dots$ be a strictly increasing sequence of real numbers with $b_k \ge 1$
and $b_k \ge k$ for every $k \ge 0$. Then there is a real constant $C$ such that for every integer
$n \ge 1$, with both sums taken over the integers $k$ satisfying $0 \le k \le n - \nu$,

$$\Bigl| \sum_k (-1)^k \lfloor (n - \nu)/b_k \rfloor - n \sum_k (-1)^k/b_k \Bigr| \le C\sqrt{n}.$$

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 32 (`jis-2024-24.2.5-prop-32`). -/
theorem alternating_sum_floor_div_eq_add_bigO (ν : ℝ)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) (b : ℕ → ℝ) (hb : StrictMono b)
    (hb₁ : ∀ k, 1 ≤ b k) (hbk : ∀ k : ℕ, (k : ℝ) ≤ b k) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
            (⌊((n : ℝ) - ν) / b k⌋ : ℝ) * (-1) ^ k) -
          n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
            (-1) ^ k / b k| ≤ C * Real.sqrt n :=
  ⟨6, fun _ hn => AlternatingSumFloorDiv.abs_sub_le_six_mul_sqrt hν₀ hν₁ hb.monotone hb₁ hbk hn⟩

end MetaMathlibExt
