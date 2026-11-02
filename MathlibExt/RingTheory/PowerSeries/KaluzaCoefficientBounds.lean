/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Kaluza's bounds for the coefficients of a reciprocal power series

If a real formal power series `f` has strictly positive log-convex coefficients `aₙ`, then the
coefficients `bₙ` of `f⁻¹` satisfy `b₀ = a₀⁻¹ > 0` and `-aₙ / a₀² ≤ bₙ ≤ 0` for `n ≥ 1`.

Source: László Tóth, *Alternating Sums Concerning Multiplicative Arithmetic Functions*,
Journal of Integer Sequences 20, Lemma `lemma_Kaluza`,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.tex>. Tóth attributes the
nonpositivity of `bₙ` to T. Kaluza, Satz 3.
-/

@[expose] public section

namespace MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted

/-- **Positive log-convex coefficients.** A real formal power series $f = \sum_n a_n X^n$ has
positive log-convex coefficients if $a_n > 0$ for every natural number $n$ and
$a_{n+1}^2 \le a_n a_{n+2}$ for every natural number $n$. This is the hypothesis of Kaluza's
bounds for the coefficients of the reciprocal series.

Source: László Tóth, *Alternating Sums Concerning Multiplicative Arithmetic
Functions*, Journal of Integer Sequences 20, Lemma `lemma_Kaluza`,
`https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.tex`, lines 553–562, file sha256
`e225aae50ee869db4df08f1a24bf6448ea544ca356369d5a0c4c7321d92607d8`, span sha256
`2ad887082f5786fc8ff64b75c3a7ddb63bc0a456290eee9cb6a85acf3c868d0f`. -/
def HasPositiveLogConvexCoefficients (f : PowerSeries ℝ) : Prop :=
  0 < PowerSeries.coeff 0 f ∧
    ∀ n : ℕ, 0 < PowerSeries.coeff (n + 1) f ∧
      (PowerSeries.coeff (n + 1) f) ^ 2 ≤
        PowerSeries.coeff n f * PowerSeries.coeff (n + 2) f

/-- **Coefficients of a positive log-convex series are positive.** If a real formal power series
$f$ has positive log-convex coefficients, then the coefficient of $X^n$ in $f$ is strictly
positive for every natural number $n$. -/
theorem HasPositiveLogConvexCoefficients.coeff_pos {f : PowerSeries ℝ}
    (hf : HasPositiveLogConvexCoefficients f) (n : ℕ) : 0 < PowerSeries.coeff n f := by
  cases n with
  | zero => exact hf.1
  | succ n => exact (hf.2 n).1

/-- **Log-convexity of the coefficients.** If a real formal power series $f = \sum_n a_n X^n$
has positive log-convex coefficients, then $a_{n+1}^2 \le a_n a_{n+2}$ for every natural
number $n$. -/
theorem HasPositiveLogConvexCoefficients.sq_coeff_succ_le {f : PowerSeries ℝ}
    (hf : HasPositiveLogConvexCoefficients f) (n : ℕ) :
    (PowerSeries.coeff (n + 1) f) ^ 2 ≤ PowerSeries.coeff n f * PowerSeries.coeff (n + 2) f :=
  (hf.2 n).2

-- Helper: the core induction, stated for abstract coefficient sequences `a`, `b`
-- satisfying positivity, log-convexity, the `b₀` value and the convolution
-- relation from `f * f⁻¹ = 1`.
private theorem kaluza_aux (a b : ℕ → ℝ) (ha0 : 0 < a 0)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hlc : ∀ n : ℕ, (a (n + 1)) ^ 2 ≤ a n * a (n + 2))
    (hb0 : b 0 = (a 0)⁻¹)
    (hsum : ∀ M : ℕ, 1 ≤ M → ∑ k ∈ Finset.range (M + 1), a k * b (M - k) = 0) :
    ∀ n : ℕ, 1 ≤ n → -(a n) / (a 0) ^ 2 ≤ b n ∧ b n ≤ 0 := by
  have hapos : ∀ n, 0 < a n := fun n => match n with
    | 0 => ha0
    | m + 1 => hpos m
  have ha0ne : a 0 ≠ 0 := ne_of_gt ha0
  -- Successive ratios are monotone (division-free form).
  have key : ∀ m : ℕ, ∀ j : ℕ, 1 ≤ j → j ≤ m →
      a j * a m ≤ a (m + 1) * a (j - 1) := by
    intro m
    induction m with
    | zero =>
      intro j h1 hj
      omega
    | succ m ihm =>
      intro j h1 hj
      by_cases hjm : j = m + 1
      · subst hjm
        have h := hlc m
        rw [pow_two] at h
        have e1 : m + 1 + 1 = m + 2 := by omega
        have e2 : m + 1 - 1 = m := by omega
        rw [e1, e2]
        calc a (m + 1) * a (m + 1) ≤ a m * a (m + 2) := h
          _ = a (m + 2) * a m := by ring
      · have hjm' : j ≤ m := by omega
        have ih := ihm j h1 hjm'
        have e1 : m + 1 + 1 = m + 2 := by omega
        rw [e1]
        have hp1 : 0 < a (m + 1) := hapos (m + 1)
        have hpm : 0 < a m := hapos m
        have hpj : 0 < a (j - 1) := hapos (j - 1)
        have step1 : (a j * a (m + 1)) * a m ≤ (a (m + 2) * a (j - 1)) * a m := by
          calc (a j * a (m + 1)) * a m = (a j * a m) * a (m + 1) := by ring
            _ ≤ (a (m + 1) * a (j - 1)) * a (m + 1) :=
                mul_le_mul_of_nonneg_right ih (le_of_lt hp1)
            _ = (a (m + 1)) ^ 2 * a (j - 1) := by ring
            _ ≤ (a m * a (m + 2)) * a (j - 1) :=
                mul_le_mul_of_nonneg_right (hlc m) (le_of_lt hpj)
            _ = (a (m + 2) * a (j - 1)) * a m := by ring
        exact le_of_mul_le_mul_right step1 hpm
  -- Peel both ends off the convolution sum.
  have lowEq : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1 + 1), a k * b (N + 1 - k))
      = a 0 * b (N + 1) + (∑ k ∈ Finset.range N, a (k + 1) * b (N - k))
        + a (N + 1) * b 0 := by
    intro N
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    rw [Nat.sub_self (N + 1), Nat.sub_zero (N + 1)]
    have hmid : (∑ k ∈ Finset.range N, a (k + 1) * b (N + 1 - (k + 1)))
        = (∑ k ∈ Finset.range N, a (k + 1) * b (N - k)) :=
      Finset.sum_congr rfl (fun k _ => by rw [show N + 1 - (k + 1) = N - k from by omega])
    rw [hmid]
    ac_rfl
  -- Scaled convolution sums, first part.
  have upA : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1 + 1), a N * (a k * b (N + 1 - k)))
      = (a N * a 0) * b (N + 1)
        + (∑ k ∈ Finset.range N, a N * (a (k + 1) * b (N - k)))
        + a N * (a (N + 1) * b 0) := by
    intro N
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    rw [Nat.sub_self (N + 1), Nat.sub_zero (N + 1)]
    have hmid : (∑ k ∈ Finset.range N, a N * (a (k + 1) * b (N + 1 - (k + 1))))
        = (∑ k ∈ Finset.range N, a N * (a (k + 1) * b (N - k))) :=
      Finset.sum_congr rfl (fun k _ => by rw [show N + 1 - (k + 1) = N - k from by omega])
    rw [hmid]
    ring
  -- Scaled convolution sums, second part.
  have upB : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1), a (N + 1) * (a k * b (N - k)))
      = (∑ k ∈ Finset.range N, a (N + 1) * (a k * b (N - k)))
        + a (N + 1) * (a N * b 0) := by
    intro N
    rw [Finset.sum_range_succ, show N - N = 0 from Nat.sub_self N]
  -- The two middle sums combine.
  have upC : ∀ N : ℕ, (∑ k ∈ Finset.range N, a N * (a (k + 1) * b (N - k)))
      - (∑ k ∈ Finset.range N, a (N + 1) * (a k * b (N - k)))
      = ∑ k ∈ Finset.range N, ((a N * a (k + 1) - a (N + 1) * a k) * b (N - k)) := by
    intro N
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  -- Kaluza's shift identity.
  have upEq : ∀ N : ℕ, a N * (∑ k ∈ Finset.range (N + 1 + 1), a k * b (N + 1 - k))
      - a (N + 1) * (∑ k ∈ Finset.range (N + 1), a k * b (N - k))
      = (a N * a 0) * b (N + 1)
        + ∑ k ∈ Finset.range N, ((a N * a (k + 1) - a (N + 1) * a k) * b (N - k)) := by
    intro N
    have hA := upA N
    have hB := upB N
    have hC := upC N
    have e1 : a N * (∑ k ∈ Finset.range (N + 1 + 1), a k * b (N + 1 - k))
        = (a N * a 0) * b (N + 1)
          + (∑ k ∈ Finset.range N, a N * (a (k + 1) * b (N - k)))
          + a N * (a (N + 1) * b 0) := by
      rw [Finset.mul_sum]
      exact hA
    have e2 : a (N + 1) * (∑ k ∈ Finset.range (N + 1), a k * b (N - k))
        = (∑ k ∈ Finset.range N, a (N + 1) * (a k * b (N - k)))
          + a (N + 1) * (a N * b 0) := by
      rw [Finset.mul_sum]
      exact hB
    rw [e1, e2]
    have h0 : a N * (a (N + 1) * b 0) - a (N + 1) * (a N * b 0) = 0 := by ring
    linear_combination hC + h0
  -- Main induction.
  suffices H : ∀ N : ℕ, ∀ m : ℕ, m ≤ N → 1 ≤ m → -(a m) / (a 0) ^ 2 ≤ b m ∧ b m ≤ 0 by
    intro n hn
    exact H n n le_rfl hn
  intro N
  induction N with
  | zero =>
    intro m hm h1
    omega
  | succ N ihN =>
    intro m hm h1
    by_cases hmN : m ≤ N
    · exact ihN m hmN h1
    · have mEq : m = N + 1 := by omega
      subst mEq
      have hS : (∑ k ∈ Finset.range (N + 1 + 1), a k * b (N + 1 - k)) = 0 :=
        hsum (N + 1) (by omega)
      rw [lowEq N] at hS
      rw [hb0] at hS
      have hmid_nonpos : (∑ k ∈ Finset.range N, a (k + 1) * b (N - k)) ≤ 0 := by
        apply Finset.sum_nonpos
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        have hbound := ihN (N - k) (by omega) (by omega)
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hapos (k + 1))) hbound.2
      have hlower : -(a (N + 1)) / (a 0) ^ 2 ≤ b (N + 1) := by
        have hlow : -(a (N + 1) * (a 0)⁻¹) ≤ a 0 * b (N + 1) := by
          have hnn : 0 ≤ -(∑ k ∈ Finset.range N, a (k + 1) * b (N - k)) :=
            neg_nonneg.mpr hmid_nonpos
          linarith
        rw [div_le_iff₀ (pow_pos (hapos 0) 2)]
        have h2 : (-(a (N + 1) * (a 0)⁻¹)) * a 0 ≤ (a 0 * b (N + 1)) * a 0 :=
          mul_le_mul_of_nonneg_right hlow (le_of_lt (hapos 0))
        have e1 : (-(a (N + 1) * (a 0)⁻¹)) * a 0 = -(a (N + 1)) := by
          rw [neg_mul, mul_assoc, inv_mul_cancel₀ ha0ne, mul_one]
        have e2 : (a 0 * b (N + 1)) * a 0 = b (N + 1) * (a 0) ^ 2 := by ring
        rwa [e1, e2] at h2
      have hupper : b (N + 1) ≤ 0 := by
        by_cases hN0 : N = 0
        · subst hN0
          rw [Finset.range_zero, Finset.sum_empty, add_zero] at hS
          have hnn : 0 ≤ a (0 + 1) * (a 0)⁻¹ :=
            mul_nonneg (le_of_lt (hapos (0 + 1))) (le_of_lt (inv_pos.mpr (hapos 0)))
          have hle : a 0 * b (0 + 1) ≤ 0 := by linarith
          exact le_of_mul_le_mul_left (by rwa [mul_zero]) (hapos 0)
        · have hE := upEq N
          have hS1 : (∑ k ∈ Finset.range (N + 1 + 1), a k * b (N + 1 - k)) = 0 :=
            hsum (N + 1) (by omega)
          have hS0 : (∑ k ∈ Finset.range (N + 1), a k * b (N - k)) = 0 :=
            hsum N (by omega)
          rw [hS1, hS0] at hE
          have hmid_nonneg : 0 ≤ (∑ k ∈ Finset.range N,
              ((a N * a (k + 1) - a (N + 1) * a k) * b (N - k))) := by
            apply Finset.sum_nonneg
            intro k hk
            have hkN : k < N := Finset.mem_range.mp hk
            have hkey := key N (k + 1) (by omega) (by omega)
            rw [show k + 1 - 1 = k from by omega] at hkey
            have hbound := ihN (N - k) (by omega) (by omega)
            have hcoeff : a N * a (k + 1) - a (N + 1) * a k ≤ 0 := by
              have h2 : a N * a (k + 1) ≤ a (N + 1) * a k := by linear_combination hkey
              linarith
            exact mul_nonneg_of_nonpos_of_nonpos hcoeff hbound.2
          have hfin : (a N * a 0) * b (N + 1) ≤ 0 := by linarith
          exact le_of_mul_le_mul_left (by rwa [mul_zero]) (mul_pos (hapos N) (hapos 0))
      exact ⟨hlower, hupper⟩

/-- **Kaluza's bounds for the coefficients of a reciprocal power series.** Let
$f = \sum_n a_n X^n$ be a real formal power series with positive log-convex coefficients, and
let $f^{-1} = \sum_n b_n X^n$ be its reciprocal in the ring of formal power series. Then
$b_0 = a_0^{-1}$, $b_0 > 0$, and $-a_n / a_0^2 \le b_n \le 0$ for every $n \ge 1$.

The reciprocal is formal; no convergence is assumed.

Source: László Tóth, *Alternating Sums Concerning Multiplicative Arithmetic
Functions*, Journal of Integer Sequences 20, Lemma `lemma_Kaluza`,
`https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.tex`, lines 553–562, file sha256
`e225aae50ee869db4df08f1a24bf6448ea544ca356369d5a0c4c7321d92607d8`, span sha256
`2ad887082f5786fc8ff64b75c3a7ddb63bc0a456290eee9cb6a85acf3c868d0f`.
Tóth attributes the nonpositivity of `bₙ` to T. Kaluza, Satz 3.
Proves `Wanted` entry `kaluza_coeff_inv_bounds`.
-/
theorem kaluza_coeff_inv_bounds (f : PowerSeries ℝ)
    (hf : HasPositiveLogConvexCoefficients f) :
    PowerSeries.coeff 0 (f⁻¹) = (PowerSeries.coeff 0 f)⁻¹ ∧
      0 < PowerSeries.coeff 0 (f⁻¹) ∧
        ∀ n : ℕ, 1 ≤ n →
          -(PowerSeries.coeff n f) / (PowerSeries.coeff 0 f) ^ 2 ≤
            PowerSeries.coeff n (f⁻¹) ∧
          PowerSeries.coeff n (f⁻¹) ≤ 0 := by
  have ha0 : 0 < PowerSeries.coeff 0 f := hf.coeff_pos 0
  have ha0ne : PowerSeries.coeff 0 f ≠ 0 := ne_of_gt ha0
  have hconst : PowerSeries.constantCoeff f ≠ 0 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hmul : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f hconst
  have hb0 : PowerSeries.coeff 0 f⁻¹ = (PowerSeries.coeff 0 f)⁻¹ := by
    have h := PowerSeries.coeff_inv 0 f
    rw [ite_eq_left rfl] at h
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  have hsum : ∀ M : ℕ, 1 ≤ M → ∑ k ∈ Finset.range (M + 1),
      PowerSeries.coeff k f * PowerSeries.coeff (M - k) f⁻¹ = 0 := by
    intro M hM
    have h := congrArg (PowerSeries.coeff M) hmul
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    dsimp only at h
    rw [PowerSeries.coeff_one, ite_eq_right (by omega : ¬M = 0)] at h
    exact h
  have hmain := kaluza_aux (fun n => PowerSeries.coeff n f)
    (fun n => PowerSeries.coeff n f⁻¹) ha0 (fun n => hf.coeff_pos (n + 1))
    hf.sq_coeff_succ_le hb0 hsum
  refine ⟨hb0, ?_, hmain⟩
  rw [hb0]
  exact inv_pos.mpr ha0

end MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted
