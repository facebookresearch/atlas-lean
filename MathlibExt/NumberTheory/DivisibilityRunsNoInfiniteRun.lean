/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedTribonacci
public import MathlibExt.NumberTheory.GibonacciNumber
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.DivisibilityRuns
import MathlibExt.NumberTheory.DivisibilityRunsGibonacciGeneralizedTribonacciGrowthBounds
import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib

/-!
# Global non-divisibility of a generalized Tribonacci sequence by a Gibonacci sequence

For integer initial values, if every Gibonacci term is nonzero and divides the corresponding
Tribonacci term, then the Tribonacci sequence is identically zero. ATLAS starts both sequences at
index zero instead of one. The proof follows Smirnov's quotient argument, using $2$ as an upper
bound for the Tribonacci growth rate and retaining the gcd of the Gibonacci initial values.

## References

- Nicholas Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci
  Sequences*, INTEGERS 26 (2026), Article A122, pp. 1–13, Theorem 1 (Section 3, pp. 5–6).
-/

open scoped Topology

namespace MetaMathlibExt

-- The growth bounds give a lower estimate for the Gibonacci terms and an upper estimate for
-- the integer quotients, with rates φ and 2 / φ respectively.
private theorem quotient_growth (x y a b c : ℤ) (hy : y ≠ 0) (R : ℕ → ℤ)
    (hR : ∀ n, generalizedTribonacci a b c n = gibonacciNumber x y n * R n) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∃ N : ℕ, ∀ n ≥ N,
      A * Real.goldenRatio ^ n ≤ |(gibonacciNumber x y n : ℝ)| ∧
        |(R n : ℝ)| ≤ B * (2 / Real.goldenRatio) ^ n := by
  obtain ⟨_, ⟨c₀, c₁, hc₀, _, hP⟩, hQ⟩ := gibonacci_generalizedTribonacci_growth_bounds
  let φ := Real.goldenRatio
  have hφ : 0 < φ := Real.goldenRatio_pos
  let S : ℝ := |(x : ℝ)| + |(y : ℝ)|
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  have hS : 0 < S := add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr hyR)
  let A := c₀ * φ / S
  have hA : 0 < A := div_pos (mul_pos hc₀ hφ) hS
  let C : ℝ := |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|
  have hC : 0 ≤ C := by positivity
  -- Only an upper bound of two for the real Tribonacci root is needed.
  let f (t : ℝ) := t ^ 3 - t ^ 2 - t - 1
  have hf : Continuous f := ((continuous_id.pow 3).sub (continuous_id.pow 2) |>.sub
    continuous_id).sub continuous_const
  obtain ⟨τ, hτ, hτ₀⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
    hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f 1) (f 2) by norm_num [f])
  have hτeq : τ ^ 3 = τ ^ 2 + τ + 1 := by
    dsimp [f] at hτ₀
    linarith only [hτ₀]
  obtain ⟨N, hN⟩ := exists_nat_ge (c₁ * (Real.log S + 1))
  refine ⟨A, C / A, hA, div_nonneg hC hA.le, N, fun n hn => ?_⟩
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hg : A * φ ^ n ≤ |(gibonacciNumber x y n : ℝ)| := calc
    _ = c₀ * φ ^ (n + 1) / S := by dsimp [A]; rw [pow_succ]; ring
    _ ≤ _ := hP x y (fun h => hy (congrArg Prod.snd h)) n (hN.trans hnR)
  refine ⟨hg, (mul_le_mul_iff_left₀ (mul_pos hA (pow_pos hφ n))).mp ?_⟩
  calc
    |(R n : ℝ)| * (A * φ ^ n) ≤ |(R n : ℝ)| * |(gibonacciNumber x y n : ℝ)| :=
      mul_le_mul_of_nonneg_left hg (abs_nonneg _)
    _ = |(generalizedTribonacci a b c n : ℝ)| := by rw [mul_comm, ← abs_mul, ← Int.cast_mul, ← hR]
    _ ≤ C * (2 : ℝ) ^ n := (hQ τ hτeq a b c n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hτ.1) hτ.2 n) hC)
    _ = C / A * (2 / φ) ^ n * (A * φ ^ n) := by
      rw [div_pow]
      field_simp [hA.ne', (pow_pos hφ n).ne']

/-- **Divisibility by a Gibonacci sequence forces a Tribonacci sequence to vanish.** Let
$x, y, a, b, c$ be integers, let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and
$P_1 = y$, and let $(Q_n)_{n \ge 0}$ be the generalized Tribonacci sequence with $Q_0 = a$,
$Q_1 = b$ and $Q_2 = c$. If $P_n \ne 0$ and $P_n \mid Q_n$ for every $n \ge 0$, then $Q_n = 0$
for every $n \ge 0$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 1
(`integers-2026-A122-thm-1`). -/
public theorem generalizedTribonacci_eq_zero_of_dvd (x y a b c : ℤ)
    (hP : ∀ n : ℕ, gibonacciNumber x y n ≠ 0)
    (hdiv : ∀ n : ℕ, gibonacciNumber x y n ∣ generalizedTribonacci a b c n) :
    ∀ n : ℕ, generalizedTribonacci a b c n = 0 := by
  have hy : y ≠ 0 := by simpa [gibonacciNumber_eq_fib x y 1 (by decide)] using hP 1
  let P := gibonacciNumber x y
  let Q := generalizedTribonacci a b c
  change ∀ n, P n ∣ Q n at hdiv
  choose R hR using hdiv
  let E (n : ℕ) := R (n + 1) - R (n + 2) - 2 * R n
  let g : ℤ := Int.gcd x y
  have hg : g ≠ 0 := by
    change (Int.gcd x y : ℤ) ≠ 0
    exact_mod_cast Int.gcd_ne_zero_right (a := x) hy
  -- Substitute Q = P * R into the Tribonacci recurrence and collect two Gibonacci terms.
  have hrelation (n : ℕ) :
      P (n + 3) * (R (n + 3) - R (n + 2) - R n) = P (n + 1) * E n := by
    have ⟨h₂, h₀⟩ : P (n + 2) = P (n + 3) - P (n + 1) ∧
        P n = P (n + 3) - 2 * P (n + 1) := by
      simpa only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega,
        Nat.add_sub_cancel] using gibonacciNumber_backward x y (n + 3) (by omega)
    have h : Q (n + 3) = Q (n + 2) + Q (n + 1) + Q n := generalizedTribonacci_add_three a b c n
    rw [hR (n + 3), hR (n + 2), hR (n + 1), hR n, h₂, h₀] at h
    dsimp only [E]
    linear_combination h
  have hdvd (n : ℕ) : P (n + 3) ∣ g * E n := by
    have hgcd : Int.gcd (P (n + 3)) (P (n + 1)) = Int.gcd x y := by
      simpa only [show n + 3 - 2 = n + 1 by omega] using
        int_gcd_gibonacciNumber_sub_two x y (n + 3) (by omega)
    have hE : P (n + 3) ∣ P (n + 1) * E n := ⟨_, (hrelation n).symm⟩
    change P (n + 3) ∣ (Int.gcd x y : ℤ) * E n
    rw [← hgcd, Int.gcd_eq_gcd_ab, add_mul, mul_right_comm _ _ (E n), mul_right_comm _ _ (E n)]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (dvd_mul_of_dvd_left hE _)
  obtain ⟨A, B, hA, hB, N, hgrowth⟩ := quotient_growth x y a b c hy R hR
  let φ := Real.goldenRatio
  have hφ : 0 < φ := Real.goldenRatio_pos
  let r : ℝ := 2 / φ
  have hr : 1 ≤ r := (le_div_iff₀ hφ).mpr (by simpa using Real.goldenRatio_lt_two.le)
  have hrφ : r / φ < 1 := by
    apply (div_lt_one hφ).mpr
    apply (div_lt_iff₀ hφ).mpr
    rw [← pow_two, Real.goldenRatio_sq]
    linarith only [Real.one_lt_goldenRatio]
  -- A fixed multiple of (2 / φ²)^n tends to zero, so eventually |g * E n| < |P (n+3)|.
  let M := |(g : ℝ)| * (4 * (B * r ^ 2))
  have hlim : Filter.Tendsto (fun n : ℕ => M * (r / φ) ^ n) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ r / φ) hrφ).const_mul M
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hA)
  have htail (n : ℕ) (hn : max N L ≤ n) : E n = 0 := by
    have hbound (i : ℕ) (hi : N ≤ i) (hin : i ≤ n + 2) : |(R i : ℝ)| ≤ B * r ^ (n + 2) :=
      (hgrowth i hi).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hin) hB)
    obtain ⟨h₀l, h₀u⟩ := abs_le.mp (hbound n (by omega) (by omega))
    obtain ⟨h₁l, h₁u⟩ := abs_le.mp (hbound (n + 1) (by omega) (by omega))
    obtain ⟨h₂l, h₂u⟩ := abs_le.mp (hbound (n + 2) (by omega) le_rfl)
    have hE : |(E n : ℝ)| ≤ 4 * (B * r ^ (n + 2)) := by
      dsimp only [E]
      push_cast
      exact abs_le.mpr ⟨by linarith only [h₀u, h₁l, h₂u], by linarith only [h₀l, h₁u, h₂l]⟩
    have hsmall : M * r ^ n < A * φ ^ n := by
      have h := hL n (by omega)
      rw [div_pow, ← mul_div_assoc] at h
      exact (div_lt_iff₀ (pow_pos hφ n)).mp h
    have hlt : |((g * E n : ℤ) : ℝ)| < |(P (n + 3) : ℝ)| := calc
      _ = |(g : ℝ)| * |(E n : ℝ)| := by rw [Int.cast_mul, abs_mul]
      _ ≤ |(g : ℝ)| * (4 * (B * r ^ (n + 2))) := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
      _ = M * r ^ n := by dsimp [M]; rw [pow_add]; ring
      _ < A * φ ^ n := hsmall
      _ ≤ A * φ ^ (n + 3) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ Real.one_lt_goldenRatio.le (by omega)) hA.le
      _ ≤ _ := (hgrowth (n + 3) (by omega)).1
    have hz := Int.eq_zero_of_abs_lt_dvd ((abs_dvd _ _).mpr (hdvd n)) (by exact_mod_cast hlt)
    exact (mul_eq_zero.mp hz).resolve_left hg
  have hstep (n : ℕ) (hn : max N L ≤ n) : R (n + 3) = R (n + 2) + R n := by
    have h := hrelation n
    rw [htail n hn, mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_left (hP (n + 3))
    omega
  have hzero (n : ℕ) (hn : max N L ≤ n) : Q n = 0 := by
    have e₀ := htail n hn
    have e₁ := htail (n + 1) (by omega)
    have e₂ := htail (n + 2) (by omega)
    have s₀ := hstep n hn
    have s₁ := hstep (n + 1) (by omega)
    norm_num only [E, Nat.add_assoc] at e₀ e₁ e₂ s₁
    have hz : R n = 0 := by omega
    rw [hR, hz, mul_zero]
  -- Propagate the zero tail backwards using the public Tribonacci recurrence.
  have all_zero (k : ℕ) (hk : ∀ n : ℕ, k ≤ n → Q n = 0) : ∀ n, Q n = 0 := by
    induction k with
    | zero => exact fun n => hk n (Nat.zero_le n)
    | succ k ih =>
      apply ih
      intro n hn
      by_cases he : n = k
      · subst n
        have h : Q (k + 3) = Q (k + 2) + Q (k + 1) + Q k :=
          generalizedTribonacci_add_three a b c k
        rw [hk (k + 1) (by omega), hk (k + 2) (by omega), hk (k + 3) (by omega)] at h
        omega
      · exact hk n (by omega)
  exact all_zero (max N L) hzero

end MetaMathlibExt
