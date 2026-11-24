/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
import MathlibExt.Combinatorics.Enumerative.CentralTrinomialRecurrence
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Alternating sums of Motzkin numbers

The alternating sums are log-balanced from index 8 and tempered from index 5.
The proof bounds the ratios of consecutive sums using a recurrence with an alternating error.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Alternating sums of Motzkin numbers.** Let $M_k$ denote the $k$-th Motzkin number. For a
natural number $n$, the $n$-th alternating Motzkin sum is the integer
$$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k.$$
It is OEIS A187306, which begins $1, 0, 2, 2, 7, 14, 37, \dots$

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (2). -/
public def motzkinAlternatingSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (motzkinNumber k : ℤ)

/-- **The alternating Motzkin sum at 0.** Let $M_k$ denote the $k$-th Motzkin number and let
$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. Then $T_0 = 1$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 2. -/
public theorem motzkinAlternatingSum_zero : motzkinAlternatingSum 0 = 1 := by
  simp [motzkinAlternatingSum, motzkinNumber_zero]

/-- **Recurrence for alternating Motzkin sums.** Let $M_k$ denote the $k$-th Motzkin number and
let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. For every natural number $n$, $T_{n+1} = M_{n+1} - T_n$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Equation (2). -/
public theorem motzkinAlternatingSum_succ (n : ℕ) :
    motzkinAlternatingSum (n + 1) = motzkinNumber (n + 1) - motzkinAlternatingSum n := by
  rw [motzkinAlternatingSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
    motzkinAlternatingSum, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

/-- **Alternating Motzkin sums at 1 and 2.** Let $M_k$ denote the $k$-th Motzkin number and let
$T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. Then $T_1 = 0$ and $T_2 = 2$.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Table 2. -/
public theorem motzkinAlternatingSum_one_two :
    motzkinAlternatingSum 1 = 0 ∧ motzkinAlternatingSum 2 = 2 := by
  have h1 : motzkinAlternatingSum 1 = 0 := by
    rw [motzkinAlternatingSum_succ, motzkinAlternatingSum_zero, motzkinNumber_one]; norm_num
  refine ⟨h1, ?_⟩
  rw [motzkinAlternatingSum_succ, h1, motzkinNumber_two]; norm_num

namespace motzkinAlternatingSum_logBalanced_tempered

private abbrev M (n : ℕ) : ℤ := motzkinNumber n
private noncomputable abbrev C (n : ℕ) : ℤ := trinomialCoefficient n n
private abbrev T := motzkinAlternatingSum

-- Consecutive central trinomial coefficients differ by a multiple of a Motzkin number.
private lemma central_step (n : ℕ) :
    C (n + 2) = C (n + 1) + 2 * (n + 1 : ℤ) * M n := by
  exact_mod_cast trinomialCoefficient_succ_eq_add_motzkinNumber (n + 1) (by omega)

private lemma motzkin_central (n : ℕ) :
    (n + 3 : ℤ) * M (n + 1) = (n + 1 : ℤ) * M n + 2 * C (n + 1) := by
  have h : (n + 3 : ℤ) * C (n + 3) =
      (2 * (n : ℤ) + 5) * C (n + 2) + 3 * (n + 2 : ℤ) * C (n + 1) := by
    have hr := centralTrinomialCoeff_three_term_recurrence (n + 2)
    rw [show n + 2 - 1 = n + 1 by omega] at hr
    rw [show 2 * (n + 2) + 1 = 2 * n + 5 by omega] at hr
    unfold C
    exact_mod_cast hr
  have hs := central_step (n + 1)
  push_cast at hs
  apply mul_left_cancel₀ (by positivity : (2 * (n + 2 : ℤ)) ≠ 0)
  linear_combination h - (n + 3 : ℤ) * hs + (n + 2 : ℤ) * central_step n

private lemma motzkin_step (n : ℕ) :
    (n + 4 : ℤ) * M (n + 2) =
      (2 * (n : ℤ) + 5) * M (n + 1) + 3 * (n + 1 : ℤ) * M n := by
  have h := motzkin_central (n + 1)
  push_cast at h
  linear_combination h - motzkin_central n + 2 * central_step n

-- Substituting Mₙ₊₁ = Tₙ₊₁ + Tₙ in the Motzkin recurrence leaves a forcing term 2(-1)ⁿ.
private lemma recurrence (n : ℕ) :
    (n + 4 : ℤ) * T (n + 2) =
      2 * (n + 2 : ℤ) * T (n + 1) + 3 * (n + 2 : ℤ) * T n + 2 * (-1) ^ n := by
  induction n with
  | zero => norm_num [T, motzkinAlternatingSum_one_two.1, motzkinAlternatingSum_one_two.2,
      motzkinAlternatingSum_zero]
  | succ n ih =>
    have h := motzkin_step (n + 1)
    push_cast at h ⊢
    rw [pow_succ]
    linear_combination h - ih +
      (n + 5 : ℤ) * motzkinAlternatingSum_succ (n + 2) -
      (2 * (n : ℤ) + 7) * motzkinAlternatingSum_succ (n + 1) -
      3 * (n + 2 : ℤ) * motzkinAlternatingSum_succ n

private lemma small_values :
    T 5 = 14 ∧ T 6 = 37 ∧ T 7 = 90 ∧ T 8 = 233 ∧ T 9 = 602 := by
  simp only [T, motzkinAlternatingSum, motzkinNumber_eq_sum_range_half, catalan_eq_centralBinom_div]
  decide

/-- Propagate the two ratio bounds through one step of the recurrence. -/
private lemma bounds_step {k x y z e : ℤ} (hk : 8 ≤ k) (hy : 8 * (2 * k + 9) ≤ y)
    (he : -1 ≤ e ∧ e ≤ 1)
    (hr : (k + 4) * z = 2 * (k + 2) * y + 3 * (k + 2) * x + 2 * e)
    (hl : (6 * k + 6) * x ≤ (2 * k + 5) * y)
    (hu : (2 * k + 7) * y ≤ (6 * k + 12) * x) :
    (6 * k + 12) * y ≤ (2 * k + 7) * z ∧ (2 * k + 9) * z ≤ (6 * k + 18) * y := by
  have hk₀ : 0 ≤ k := by omega
  constructor
  · apply le_of_mul_le_mul_left (a := 2 * (k + 4)) _ (by positivity)
    have herr : 4 * (2 * k + 7) ≤ 9 * y := by omega
    linear_combination (2 * k + 7) * hu + herr + 4 * (2 * k + 7) * he.1 -
      2 * (2 * k + 7) * hr
  · apply le_of_mul_le_mul_left (a := 2 * (k + 1) * (k + 4)) _ (by positivity)
    have herr : 4 * (k + 1) * (2 * k + 9) ≤ (3 * k - 18) * y := by
      calc
        _ ≤ ((3 * k - 18) * 8) * (2 * k + 9) :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        _ = (3 * k - 18) * (8 * (2 * k + 9)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hy (by omega)
    linear_combination (k + 2) * (2 * k + 9) * hl + herr + 4 * (k + 1) * (2 * k + 9) * he.2 +
      2 * (k + 1) * (2 * k + 9) * hr

/-- The quotient `T (n + 1) / T n` lies between `(6n + 6) / (2n + 5)` and
`(6n + 12) / (2n + 7)`. The growth estimate absorbs the alternating error. -/
private lemma bounds (n : ℕ) (hn : 8 ≤ n) :
    8 * (2 * (n : ℤ) + 9) ≤ T n ∧
      (6 * (n : ℤ) + 6) * T n ≤ (2 * (n : ℤ) + 5) * T (n + 1) ∧
      (2 * (n : ℤ) + 7) * T (n + 1) ≤ (6 * (n : ℤ) + 12) * T n := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨_, _, _, h₈, h₉⟩ := small_values
    norm_num [h₈, h₉]
  | succ n hn ih =>
    obtain ⟨hg, hl, hu⟩ := ih
    have hn' : 8 ≤ (n : ℤ) := by exact_mod_cast hn
    have hx : 0 ≤ T n := by omega
    have hdouble : 2 * T n ≤ T (n + 1) := by
      apply le_of_mul_le_mul_left (a := 2 * (n : ℤ) + 5) _ (by positivity)
      calc
        _ = ((2 * (n : ℤ) + 5) * 2) * T n := by ring
        _ ≤ (6 * (n : ℤ) + 6) * T n :=
          mul_le_mul_of_nonneg_right (by omega) hx
        _ ≤ _ := hl
    have he : -1 ≤ (-1 : ℤ) ^ n ∧ (-1 : ℤ) ^ n ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h]
    obtain ⟨hl', hu'⟩ := bounds_step hn' (by omega) he (recurrence n) hl hu
    push_cast
    exact ⟨by omega, by linear_combination hl', by linear_combination hu'⟩

private lemma tail (k : ℕ) (hk : 8 ≤ k) :
    T (k + 1) ^ 2 ≤ T k * T (k + 2) ∧
      (k + 1 : ℤ) * (T k * T (k + 2)) ≤ (k + 2 : ℤ) * T (k + 1) ^ 2 := by
  obtain ⟨hx, hl, hu⟩ := bounds k hk
  obtain ⟨hy, hl', hu'⟩ := bounds (k + 1) (by omega)
  have hz := (bounds (k + 2) (by omega)).1
  have hx₀ : 0 ≤ T k := by omega
  have hy₀ : 0 ≤ T (k + 1) := by omega
  have hz₀ : 0 ≤ T (k + 2) := by omega
  push_cast at hl' hu'
  constructor
  · apply le_of_mul_le_mul_left (a := 2 * (k : ℤ) + 7) _ (by positivity)
    linear_combination T (k + 1) * hu + T k * hl'
  · apply le_of_mul_le_mul_left (a := 6 * (2 * (k : ℤ) + 9)) _ (by positivity)
    have hgap : ((k : ℤ) + 3) * (2 * k + 5) ≤ (k + 2 : ℤ) * (2 * k + 9) := by
      nlinarith only [Nat.cast_nonneg (α := ℤ) k]
    linear_combination (2 * (k : ℤ) + 9) * T (k + 2) * hl +
      (2 * (k : ℤ) + 5) * T (k + 1) * hu' + 6 * T (k + 1) ^ 2 * hgap

end motzkinAlternatingSum_logBalanced_tempered

open motzkinAlternatingSum_logBalanced_tempered in
/-- **The alternating Motzkin sums are eventually log-balanced and tempered.** Let $M_k$ denote
the $k$-th Motzkin number and let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. For every natural
number $n \ge 9$,
$$T_n^2 \le T_{n-1} T_{n+1} \quad\text{and}\quad n T_{n-1} T_{n+1} \le (n+1) T_n^2,$$
and for every natural number $n \ge 6$,
$$n T_n^2 \le (n+1) T_{n-1} T_{n+1} \quad\text{and}\quad n T_{n-1} T_{n+1} \le (n+1) T_n^2.$$

Following Došlić, a positive sequence $(z_n)_{n \ge N}$ is log-balanced if it is log-convex,
$z_n^2 \le z_{n-1} z_{n+1}$, and $(z_n/n!)$ is log-concave, $n z_{n-1} z_{n+1} \le (n+1) z_n^2$,
for every $n \ge N + 1$; it is tempered if its quotients $x_n = z_{n+1}/z_n$ satisfy
$\frac{n}{n+1} x_{n-1} \le x_n \le \frac{n+1}{n} x_{n-1}$ for every $n \ge N + 1$. So the two
parts say that $(T_n)_{n \ge 8}$ is log-balanced and $(T_n)_{n \ge 5}$ is tempered, with the
inequalities cleared of denominators (all terms are positive here) and the factorials and
quotient weights using the original index $n$, as in the paper's proofs.

Source: Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums
of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 1. -/
public theorem motzkinAlternatingSum_logBalanced_tempered :
    (∀ n, 9 ≤ n →
      motzkinAlternatingSum n ^ 2 ≤
          motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1) ∧
        n * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ≤
          (n + 1) * motzkinAlternatingSum n ^ 2) ∧
    (∀ n, 6 ≤ n →
      n * motzkinAlternatingSum n ^ 2 ≤
          (n + 1) * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ∧
        n * (motzkinAlternatingSum (n - 1) * motzkinAlternatingSum (n + 1)) ≤
          (n + 1) * motzkinAlternatingSum n ^ 2) := by
  have balanced (n : ℕ) (hn : 9 ≤ n) :
      T n ^ 2 ≤ T (n - 1) * T (n + 1) ∧
        n * (T (n - 1) * T (n + 1)) ≤ (n + 1) * T n ^ 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simpa [Nat.cast_add, add_assoc] using tail k (by omega)
  refine ⟨balanced, fun n hn => ?_⟩
  by_cases hn' : 9 ≤ n
  · obtain ⟨hl, hu⟩ := balanced n hn'
    refine ⟨?_, hu⟩
    have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℤ) n)
    nlinarith only [h, hl, sq_nonneg (T n)]
  · obtain ⟨h₅, h₆, h₇, h₈, h₉⟩ := small_values
    change n * T n ^ 2 ≤ (n + 1) * (T (n - 1) * T (n + 1)) ∧
      n * (T (n - 1) * T (n + 1)) ≤ (n + 1) * T n ^ 2
    interval_cases n <;> norm_num [h₅, h₆, h₇, h₈, h₉]

end

end MetaMathlibExt
