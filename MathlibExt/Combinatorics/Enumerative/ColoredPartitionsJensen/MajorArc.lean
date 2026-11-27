/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.CircleMethod
public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.BesselMain

/-!
# The Bessel series behind the major arc

The major arc of the circle method for `F(q)^r` produces the integral
`(2π)⁻¹ ∫ τ^{r/2} e^{A/τ + mτ} dθ` (`τ = y + iθ`, `A = rπ²/6`, `m = n − r/24`). Its value is the
series

  `S(s, m) = ∑_k A^k m^{s+k−1} / (k! Γ(s+k)) = m^{s−1} bT(s, Am)`   at `s = −r/2`,

where `bT s w = ∑_k w^k / (k! Γ(s+k))` (Mathlib's `Γ` vanishes at the poles, so `1/Γ` is the entire
reciprocal gamma there). This file proves, with no integral over an unbounded line:

* `bT_rec`: `bT s w = s · bT (s+1) w + w · bT (s+2) w` for every real `s` (the three-term recurrence
that
  `MajorArcIntegral` matches against the finite-arc integral by one integration by parts);
* `besselInt_eq_bT`: the **positive representation**
  `besselInt a z = M₀(a) Γ(a + 3/2) bT (a + 3/2) (z²/4)`, `a ≥ 0`,
`M₀(a) = ∫_{−1}^{1} (1−t²)^a dt > 0`
  (from the moment recurrence `M_{k+1}(a)(2a+2k+3) = (2k+1) M_k(a)`, one integration by parts);
* `bH_*`: the **reflection defect** `bH ν w = bT (1−ν) w − w^ν bT (1+ν) w` satisfies
  `bH (ν+1) = −ν bH ν + w bH (ν−1)`, vanishes at every natural `ν`, and
`bH (1/2) w = e^{−2√w}/√Real.pi`;
  so `|bH (r/2 + 1) w| ≤ (r+2)! (w+1)^{r+1} e^{−2√w}` (`abs_bH_le`);
* `bT_neg_half_eq`:
`bT (−r/2) w = w^{r/2+1} besselInt ((r+1)/2) (2√w) / (M₀ Γ(r/2+2)) + bH (r/2+1) w`.

So the major-arc series is the `BesselMain` model `besselInt ((r+1)/2) (2√(Am))` up to an explicit
positive constant and
an additive error `e^{−2√w}·poly`, i.e. relatively `e^{−4√(Am)}·poly` (`le_besselInt` gives the
lower bound
`besselInt a z ≥ e^{z−1} z^{−(a+1)}/(a+1)` for `z ≥ 1`).
-/

open Filter Topology Set MeasureTheory
open scoped Nat

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

noncomputable section

/-! ### The series `bT s w = ∑ w^k / (k! Γ(s+k))` -/

/-- The `k`-th term `w^k / k! · Γ(s+k)⁻¹`. -/
def bTt (s w : ℝ) (k : ℕ) : ℝ := w ^ k / k ! * (Real.Gamma (s + k))⁻¹

/-- `bT s w = ∑_k w^k / (k! Γ(s+k))`. -/
def bT (s w : ℝ) : ℝ := ∑' k, bTt s w k

/-- `x / Γ(x+1) = 1/Γ(x)` for every real `x` (both sides vanish at the poles). -/
theorem div_Gamma_add_one (x : ℝ) : x * (Real.Gamma (x + 1))⁻¹ = (Real.Gamma x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.Gamma_zero]
  · rw [Real.Gamma_add_one hx, ← div_eq_mul_inv, div_mul_cancel_left₀ hx]

theorem one_le_Gamma {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.Gamma x := by
  have := Real.Gamma_strictMonoOn_Ici.monotoneOn Set.self_mem_Ici hx hx
  rwa [Real.Gamma_two] at this

theorem summable_bTt (s w : ℝ) : Summable (bTt s w) := by
  refine (Real.summable_pow_div_factorial |w|).of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈2 - s⌉₊, fun k hk => ?_⟩
  have hk' : 2 - s ≤ k := Nat.ceil_le.1 hk
  have hG : 1 ≤ Real.Gamma (s + k) := one_le_Gamma (by linarith)
  have hGi : 0 ≤ (Real.Gamma (s + k))⁻¹ := inv_nonneg.2 (by linarith)
  have hGi1 : (Real.Gamma (s + k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hG
  rw [bTt, Real.norm_eq_abs, abs_mul, abs_of_nonneg hGi, abs_div, abs_pow,
    abs_of_pos (by exact_mod_cast Nat.factorial_pos k : (0 : ℝ) < k !)]
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg (abs_nonneg w) _) (by positivity)) hGi1

theorem hasSum_bT (s w : ℝ) : HasSum (bTt s w) (bT s w) := (summable_bTt s w).hasSum

/-- **The three-term recurrence** `bT s = s · bT (s+1) + w · bT (s+2)`, every real `s`. -/
theorem bT_rec (s w : ℝ) : bT s w = s * bT (s + 1) w + w * bT (s + 2) w := by
  -- `w · bTt (s+2) k = (k+1) · bTt (s+1) (k+1)`, so `w · bT (s+2) = ∑ k · bTt (s+1) k`.
  have h2 : HasSum (fun k : ℕ => (k : ℝ) * bTt (s + 1) w k) (w * bT (s + 2) w) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    refine ((hasSum_bT (s + 2) w).mul_left w).congr_fun fun k => ?_
    simp only [bTt, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show s + 1 + ((k : ℝ) + 1) = s + 2 + k by ring]
    have : (k ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    field_simp
  have h1 := ((hasSum_bT (s + 1) w).mul_left s).add h2
  refine ((hasSum_bT s w).unique (h1.congr_fun fun k => ?_)).trans (by ring)
  simp only [bTt]
  rw [show s + 1 + (k : ℝ) = (s + k) + 1 by ring, ← div_Gamma_add_one (s + k)]
  ring

/-! ### The reflection defect `bH ν w = bT (1−ν) w − w^ν bT (1+ν) w` -/

/-- The reflection defect (`= Γ`-normalised `I_{−ν} − I_ν`). -/
def bH (ν w : ℝ) : ℝ := bT (1 - ν) w - w ^ ν * bT (1 + ν) w

theorem bH_rec {w : ℝ} (hw : 0 < w) (ν : ℝ) :
    bH (ν + 1) w = -ν * bH ν w + w * bH (ν - 1) w := by
  have r1 := bT_rec (-ν) w
  have r2 := bT_rec ν w
  have e1 : w ^ (ν + 1) = w ^ ν * w := Real.rpow_add_one hw.ne' ν
  have e2 : w ^ (ν - 1) * w = w ^ ν := by
    rw [Real.rpow_sub_one hw.ne', div_mul_cancel₀ _ hw.ne']
  simp only [bH]
  rw [show 1 - (ν + 1) = -ν by ring, show 1 + (ν + 1) = ν + 2 by ring, show 1 - (ν - 1) = -ν + 2
      by ring,
    show 1 + (ν - 1) = ν by ring, show 1 - ν = -ν + 1 by ring, show 1 + ν = ν + 1 by ring, e1]
  linear_combination r1 + w ^ ν * r2 + bT ν w * e2

theorem bH_zero (w : ℝ) : bH 0 w = 0 := by simp [bH]

theorem bH_one (w : ℝ) : bH 1 w = 0 := by
  have h := bT_rec 0 w
  simp only [zero_mul, zero_add] at h
  rw [bH, show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_one, h]
  ring

theorem bH_nat {w : ℝ} (hw : 0 < w) (n : ℕ) : bH n w = 0 := by
  suffices ∀ n : ℕ, bH n w = 0 ∧ bH (n + 1) w = 0 from (this n).1
  intro n
  induction n with
  | zero => simpa using ⟨bH_zero w, bH_one w⟩
  | succ n ih =>
    refine ⟨by exact_mod_cast ih.2, ?_⟩
    rw [bH_rec hw, show ((n + 1 : ℕ) : ℝ) - 1 = n by push_cast; ring]
    push_cast; rw [ih.2, ih.1]; ring

theorem bH_neg_half {w : ℝ} (hw : 0 < w) : bH (-(1 / 2)) w = -(w ^ (-(1 / 2) : ℝ)) * bH (1 / 2) w
    := by
  simp only [bH]
  have : w ^ (-(1 / 2) : ℝ) * w ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hw]; norm_num
  rw [show (1 : ℝ) - -(1 / 2) = 1 + 1 / 2 by ring, show (1 : ℝ) + -(1 / 2) = 1 - 1 / 2 by ring]
  linear_combination (-(bT (1 + 1 / 2) w)) * this

/-! ### The positive representation `besselInt a z = M₀ Γ(a+3/2) bT (a+3/2) (z²/4)` -/

/-- The even moments `M_k(a) = ∫_{−1}^{1} (1−t²)^a t^{2k} dt`. -/
def bMom (a : ℝ) (k : ℕ) : ℝ := ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ a * t ^ (2 * k)

section Moments

variable {a : ℝ}

theorem continuous_bWt (ha : 0 ≤ a) : Continuous fun t : ℝ => (1 - t ^ 2) ^ a :=
  (continuous_const.sub (continuous_pow 2)).rpow_const fun _ => Or.inr ha

theorem one_sub_sq_nonneg {t : ℝ} (ht : t ∈ uIcc (-1 : ℝ) 1) : 0 ≤ 1 - t ^ 2 := by
  rw [uIcc_of_le (by norm_num)] at ht; nlinarith [ht.1, ht.2]

theorem intervalIntegrable_bMom (ha : 0 ≤ a) (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ a * t ^ n) volume (-1) 1 :=
  ((continuous_bWt ha).mul (continuous_pow n)).intervalIntegrable _ _

/-- **Moment recurrence** `M_{k+1}(a) (2a + 2k + 3) = (2k + 1) M_k(a)` (one integration by parts).
-/
theorem bMom_succ (ha : 0 ≤ a) (k : ℕ) :
    bMom a (k + 1) * (2 * a + 2 * k + 3) = (2 * k + 1) * bMom a k := by
  have ha1 : 0 < a + 1 := by linarith
  have hsplit : ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (a + 1) * t ^ (2 * k) = bMom a k - bMom a (k +
      1) := by
    unfold bMom
    rw [← intervalIntegral.integral_sub (intervalIntegrable_bMom ha _) (intervalIntegrable_bMom ha
        _)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Real.rpow_add' (one_sub_sq_nonneg ht) ha1.ne', Real.rpow_one]; ring
  have hu : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun t : ℝ => t ^ (2 * k + 1)) (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) x := fun x _
          => by
    simpa using hasDerivAt_pow (2 * k + 1) x
  have hv : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -(1 - t ^ 2) ^ (a + 1) / (2 * (a + 1))) (x * (1 - x ^ 2) ^ a) x :=
    fun x _ => by
      have := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).rpow_const (p := a + 1)
        (Or.inr (by linarith))
      convert this.neg.div_const (2 * (a + 1)) using 1
      simp only [Pi.sub_apply]
      rw [show a + 1 - 1 = a by ring]
      field_simp
      ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)
    ((continuous_id.mul (continuous_bWt ha)).intervalIntegrable _ _)
  have h0 : ((1 : ℝ) - 1 ^ 2) ^ (a + 1) = 0 := by norm_num; exact Real.zero_rpow ha1.ne'
  have h0' : ((1 : ℝ) - (-1) ^ 2) ^ (a + 1) = 0 := by norm_num; exact Real.zero_rpow ha1.ne'
  rw [h0, h0'] at hibp
  have hl : bMom a (k + 1) = ∫ x in (-1 : ℝ)..1, x ^ (2 * k + 1) * (x * (1 - x ^ 2) ^ a) := by
    unfold bMom
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hr : ∫ x in (-1 : ℝ)..1, ((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k) * (-(1 - x ^ 2) ^ (a + 1) / (2
      * (a + 1)))
      = -((2 * k + 1) / (2 * (a + 1))) * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (a + 1) * t ^ (2 * k)
          := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  rw [← hl, hr, hsplit] at hibp
  have e : bMom a (k + 1) = (2 * k + 1) / (2 * (a + 1)) * (bMom a k - bMom a (k + 1)) := by
    nth_rw 1 [hibp]; ring
  field_simp at e
  linear_combination e

theorem bMom_zero_pos (ha : 0 ≤ a) : 0 < bMom a 0 := by
  unfold bMom
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_bMom ha _) (fun t ht
      => ?_)
    (by norm_num)
  simp only [mul_zero, pow_zero, mul_one]
  exact Real.rpow_pos_of_pos (by nlinarith [ht.1, ht.2]) _

/-- Closed form `M_k(a) · 4^k k! Γ(a+3/2+k) = M₀(a) Γ(a+3/2) (2k)!`. -/
theorem bMom_closed (ha : 0 ≤ a) (k : ℕ) :
    bMom a k * (4 ^ k * k ! * Real.Gamma (a + 3 / 2 + k)) = bMom a 0 * Real.Gamma (a + 3 / 2) * (2
        * k) ! := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := bMom_succ ha k
    have hG : Real.Gamma (a + 3 / 2 + (k + 1 : ℕ)) = (a + 3 / 2 + k) * Real.Gamma (a + 3 / 2 + k)
        := by
      rw [show a + 3 / 2 + ((k + 1 : ℕ) : ℝ) = (a + 3 / 2 + k) + 1 by push_cast; ring]
      exact Real.Gamma_add_one (by positivity)
    rw [hG, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    push_cast
    linear_combination (2 * 4 ^ k * (k + 1) * k ! * Real.Gamma (a + 3 / 2 + k)) * hs +
      (2 * (k + 1) * (2 * k + 1)) * ih

/-- Termwise expansion of `e^{zt}`: `besselInt a z = ∑_n z^n/n! ∫ (1−t²)^a t^n`. -/
theorem hasSum_besselInt_all (ha : 0 ≤ a) (z : ℝ) :
    HasSum (fun n : ℕ => z ^ n / n ! * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ a * t ^ n) (besselInt a
        z) := by
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -1) (b
      := 1)
    (F := fun (n : ℕ) (t : ℝ) => z ^ n / n ! * ((1 - t ^ 2) ^ a * t ^ n))
    (f := fun t => (1 - t ^ 2) ^ a * Real.exp (z * t))
    (fun n _ => |z| ^ n / n !)
    (fun n => (((continuous_bWt ha).mul (continuous_pow n)).const_mul _).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun _ _ => Real.summable_pow_div_factorial _)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ => ?_)
  · refine key.congr_fun fun n => ?_
    simp only [intervalIntegral.integral_const_mul]
  · rw [uIoc_of_le (by norm_num)] at ht
    have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h1 : (1 - t ^ 2) ^ a ≤ 1 := Real.rpow_le_one h0 (by nlinarith) ha
    have ht1 : |t| ≤ 1 := abs_le.2 ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_mul, abs_pow,
      abs_of_nonneg (Real.rpow_nonneg h0 a), Nat.abs_cast]
    have : (1 - t ^ 2) ^ a * |t| ^ n ≤ 1 :=
      (mul_le_mul h1 (pow_le_one₀ (abs_nonneg _) ht1) (pow_nonneg (abs_nonneg _) _)
          zero_le_one).trans_eq
        (one_mul 1)
    exact mul_le_of_le_one_right (by positivity) this
  · have := (NormedSpace.expSeries_div_hasSum_exp (z * t)).mul_left ((1 - t ^ 2) ^ a)
    rw [← Real.exp_eq_exp_ℝ] at this
    refine this.congr_fun fun n => ?_
    simp only [mul_pow]; ring

theorem bMom_odd (k : ℕ) : ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ a * t ^ (2 * k + 1) = 0 := by
  have hf : ∀ t : ℝ, (1 - (-t) ^ 2) ^ a * (-t) ^ (2 * k + 1) = -((1 - t ^ 2) ^ a * t ^ (2 * k +
      1)) := by
    intro t; rw [neg_sq, Odd.neg_pow ⟨k, rfl⟩]; ring
  have h := intervalIntegral.integral_comp_neg (a := -1) (b := 1)
    (fun t : ℝ => (1 - t ^ 2) ^ a * t ^ (2 * k + 1))
  simp only [hf, neg_neg, intervalIntegral.integral_neg] at h
  linarith

/-- **Positive representation**: `besselInt a z = M₀(a) Γ(a+3/2) bT (a+3/2) (z²/4)`. -/
theorem besselInt_eq_bT (ha : 0 ≤ a) (z : ℝ) :
    besselInt a z = bMom a 0 * Real.Gamma (a + 3 / 2) * bT (a + 3 / 2) (z ^ 2 / 4) := by
  have h := hasSum_besselInt_all ha z
  have h2 : HasSum (fun k : ℕ => z ^ (2 * k) / (2 * k) ! * bMom a k) (besselInt a z) := by
    rw [← (Function.Injective.hasSum_iff (g := fun k : ℕ => 2 * k) (fun x y hxy => by simpa using
        hxy)
      (fun n hn => ?_))] at h
    · exact h
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
        rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact absurd ⟨k, by simp [hk]; ring⟩ hn
        · exact ⟨k, hk⟩
      simp [bMom_odd]
  refine h2.unique (((hasSum_bT _ _).mul_left (bMom a 0 * Real.Gamma (a + 3 / 2))).congr_fun fun k
      => ?_)
  have hc := bMom_closed ha k
  have hG : 0 < Real.Gamma (a + 3 / 2 + k) := Real.Gamma_pos_of_pos (by positivity)
  have hf : (0 : ℝ) < (2 * k) ! := by exact_mod_cast Nat.factorial_pos _
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos _
  simp only [bTt]
  rw [show bMom a k = bMom a 0 * Real.Gamma (a + 3 / 2) * (2 * k) ! / (4 ^ k * k ! * Real.Gamma (a
      + 3 / 2 + k))
    by rw [← hc]; field_simp]
  rw [div_pow, pow_mul]
  field_simp

end Moments

/-! ### The half-integer value `bH (1/2) w = e^{−2√w}/√Real.pi` -/

theorem factorial_two_mul_eq (k : ℕ) : (2 * k)! = 2 ^ k * k ! * (2 * k - 1)‼ := by
  cases k with
  | zero => rfl
  | succ j =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.doubleFactorial_two_mul,
      show 2 * (j + 1) - 1 = 2 * j + 1 by omega]

theorem factorial_two_mul_add_one_eq (k : ℕ) : (2 * k + 1)! = 2 ^ k * k ! * (2 * k + 1)‼ := by
  rw [Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]; ring

theorem bTt_half {w : ℝ} (hw : 0 ≤ w) (k : ℕ) :
    bTt (1 / 2) w k = (2 * √w) ^ (2 * k) / (2 * k)! / √Real.pi := by
  have hG := Real.Gamma_nat_add_half k
  have hf : (((2 * k)! : ℕ) : ℝ) = 2 ^ k * k ! * ((2 * k - 1)‼ : ℕ) := by
    exact_mod_cast factorial_two_mul_eq k
  have hd : (0 : ℝ) < ((2 * k - 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos _
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  simp only [bTt]
  rw [add_comm, hG, hf, mul_pow, pow_mul, pow_mul, Real.sq_sqrt hw, show (2 : ℝ) ^ 2 = 4
      by norm_num]
  field_simp
  rw [show (4 : ℝ) ^ k = 2 ^ (k * 2) by rw [pow_mul']; norm_num]
  ring

theorem bTt_three_half {w : ℝ} (hw : 0 ≤ w) (k : ℕ) :
    √w * bTt (3 / 2) w k = (2 * √w) ^ (2 * k + 1) / (2 * k + 1)! / √Real.pi := by
  have hG := Real.Gamma_nat_add_half (k + 1)
  have hf : (((2 * k + 1)! : ℕ) : ℝ) = 2 ^ k * k ! * ((2 * k + 1)‼ : ℕ) := by
    exact_mod_cast factorial_two_mul_add_one_eq k
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hG
  have hd : (0 : ℝ) < ((2 * k + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos _
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  simp only [bTt]
  rw [show (3 / 2 : ℝ) + k = ((k + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring, hG, hf, pow_succ (2 *
      √w), mul_pow,
    pow_mul, pow_mul, Real.sq_sqrt hw, show (2 : ℝ) ^ 2 = 4 by norm_num]
  field_simp
  rw [show (4 : ℝ) ^ k = 2 ^ (k * 2) by rw [pow_mul']; norm_num]
  ring

theorem bH_half {w : ℝ} (hw : 0 ≤ w) : bH (1 / 2) w = Real.exp (-(2 * √w)) / √Real.pi := by
  have hc : HasSum (bTt (1 / 2) w) (Real.cosh (2 * √w) / √Real.pi) :=
    ((Real.hasSum_cosh (2 * √w)).div_const √Real.pi).congr_fun fun k => bTt_half hw k
  have hs : HasSum (fun k => √w * bTt (3 / 2) w k) (Real.sinh (2 * √w) / √Real.pi) :=
    ((Real.hasSum_sinh (2 * √w)).div_const √Real.pi).congr_fun fun k => bTt_three_half hw k
  have h1 : bT (1 / 2) w = Real.cosh (2 * √w) / √Real.pi := (hasSum_bT _ _).unique hc
  have h2 : √w * bT (3 / 2) w = Real.sinh (2 * √w) / √Real.pi := ((hasSum_bT _ _).mul_left
      _).unique hs
  simp only [bH]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, h1, h2, ← sub_div, Real.cosh_sub_sinh]

/-! ### The reflection bound -/

theorem abs_bH_half_le {w : ℝ} (hw : 1 ≤ w) (n : ℕ) :
    |bH (n + 1 / 2) w| ≤ (n + 1)! * (w + 1) ^ n * Real.exp (-(2 * √w)) ∧
      |bH (n - 1 / 2) w| ≤ n ! * (w + 1) ^ n * Real.exp (-(2 * √w)) := by
  have hw0 : 0 < w := by linarith
  set E := Real.exp (-(2 * √w)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpi : 1 ≤ √Real.pi := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have h0 : |bH (1 / 2) w| ≤ E := by
    rw [bH_half hw0.le, abs_of_nonneg (div_nonneg hE0 (Real.sqrt_nonneg _))]
    exact div_le_self hE0 hpi
  induction n with
  | zero =>
    refine ⟨by simpa using h0, ?_⟩
    simp only [Nat.cast_zero, zero_sub, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul]
    rw [bH_neg_half hw0, abs_mul, abs_neg, abs_of_pos (Real.rpow_pos_of_pos hw0 _)]
    have : w ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw (by norm_num)
    calc _ ≤ 1 * E := mul_le_mul this h0 (abs_nonneg _) zero_le_one
      _ = E := one_mul E
  | succ n ih =>
    have hn1 : ((n + 1 : ℕ) : ℝ) - 1 / 2 = n + 1 / 2 := by push_cast; ring
    have hn2 : ((n + 1 : ℕ) : ℝ) + 1 / 2 = (n + 1 / 2) + 1 := by push_cast; ring
    have hn3 : (n : ℝ) + 1 / 2 - 1 = n - 1 / 2 := by ring
    have hw1 : 1 ≤ w + 1 := by linarith
    have hp : (w + 1) ^ n ≤ (w + 1) ^ (n + 1) := pow_le_pow_right₀ hw1 n.le_succ
    have hf : (n ! : ℝ) ≤ (n + 1)! := by exact_mod_cast Nat.factorial_le n.le_succ
    have hpos : 0 ≤ (w + 1) ^ n * E := mul_nonneg (pow_nonneg (by linarith) _) hE0
    refine ⟨?_, ?_⟩
    · rw [hn2, bH_rec hw0, hn3]
      calc |-(n + 1 / 2 : ℝ) * bH (n + 1 / 2) w + w * bH (n - 1 / 2) w|
          ≤ (n + 1 / 2) * |bH (n + 1 / 2) w| + w * |bH (n - 1 / 2) w| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < n + 1 / 2),
              abs_of_pos hw0]
        _ ≤ (n + 1 / 2) * ((n + 1)! * (w + 1) ^ n * E) + w * (n ! * (w + 1) ^ n * E) := by
            gcongr
            · exact ih.1
            · exact ih.2
        _ ≤ (n + 1) * ((n + 1)! * (w + 1) ^ (n + 1) * E) + (w + 1) * ((n + 1)! * (w + 1) ^ n * E)
            := by
            have h1 : (n + 1)! * (w + 1) ^ n * E ≤ (n + 1)! * (w + 1) ^ (n + 1) * E := by gcongr
            have h2 : (n ! : ℝ) * (w + 1) ^ n * E ≤ (n + 1)! * (w + 1) ^ n * E := by gcongr
            have h3 : 0 ≤ ((n + 1)! : ℝ) * (w + 1) ^ n * E := by positivity
            nlinarith
        _ = ((n + 1 + 1)! : ℕ) * (w + 1) ^ (n + 1) * E := by
            rw [Nat.factorial_succ (n + 1)]; push_cast; ring
    · rw [hn1]
      calc |bH (n + 1 / 2) w| ≤ (n + 1)! * (w + 1) ^ n * E := ih.1
        _ ≤ (n + 1)! * (w + 1) ^ (n + 1) * E := by gcongr

/-- **Reflection bound** at the order the major arc needs:
`|bH (r/2 + 1) w| ≤ (r+2)! (w+1)^{r+1} e^{−2√w}`
(`= 0` for even `r`). -/
theorem abs_bH_le (r : ℕ) {w : ℝ} (hw : 1 ≤ w) :
    |bH ((r : ℝ) / 2 + 1) w| ≤ (r + 2)! * (w + 1) ^ (r + 1) * Real.exp (-(2 * √w)) := by
  have hw0 : 0 < w := by linarith
  have hR : 0 ≤ ((r + 2)! : ℝ) * (w + 1) ^ (r + 1) * Real.exp (-(2 * √w)) := by positivity
  rcases Nat.even_or_odd r with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show ((k + k : ℕ) : ℝ) / 2 + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, bH_nat hw0, abs_zero]
    exact hR
  · rw [show ((2 * k + 1 : ℕ) : ℝ) / 2 + 1 = ((k + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring]
    refine (abs_bH_half_le hw (k + 1)).1.trans ?_
    have hw1 : 1 ≤ w + 1 := by linarith
    have hf : ((k + 1 + 1)! : ℝ) ≤ (2 * k + 1 + 2)! := by exact_mod_cast Nat.factorial_le (by omega)
    have hp : (w + 1) ^ (k + 1) ≤ (w + 1) ^ (2 * k + 1 + 1) := pow_le_pow_right₀ hw1 (by omega)
    gcongr

/-- **The major-arc series at `s = −r/2`** is the `BesselMain` model plus the reflection defect:
`bT (−r/2) w = w^{r/2+1} besselInt ((r+1)/2) (2√w) / (M₀ Γ(r/2+2)) + bH (r/2+1) w`. -/
theorem bT_neg_half_eq (r : ℕ) {w : ℝ} (hw : 0 < w) :
    bT (-((r : ℝ) / 2)) w = w ^ ((r : ℝ) / 2 + 1) * besselInt (((r : ℝ) + 1) / 2) (2 * √w) /
      (bMom (((r : ℝ) + 1) / 2) 0 * Real.Gamma ((r : ℝ) / 2 + 2)) + bH ((r : ℝ) / 2 + 1) w := by
  have ha : (0 : ℝ) ≤ ((r : ℝ) + 1) / 2 := by positivity
  have hM := bMom_zero_pos ha
  have hG : 0 < Real.Gamma ((r : ℝ) / 2 + 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [besselInt_eq_bT ha, show ((r : ℝ) + 1) / 2 + 3 / 2 = (r : ℝ) / 2 + 2 by ring,
    show (2 * √w) ^ 2 / 4 = w by rw [mul_pow, Real.sq_sqrt hw.le]; ring]
  simp only [bH]
  rw [show (1 : ℝ) - ((r : ℝ) / 2 + 1) = -((r : ℝ) / 2) by ring,
    show (1 : ℝ) + ((r : ℝ) / 2 + 1) = (r : ℝ) / 2 + 2 by ring]
  field_simp
  ring

/-- Lower bound `besselInt a z ≥ e^{z−1} z^{−(a+1)} / (a+1)` for `z ≥ 1`. -/
theorem le_besselInt {a z : ℝ} (ha : 0 ≤ a) (hz : 1 ≤ z) :
    Real.exp (z - 1) * (z⁻¹ ^ (a + 1) / (a + 1)) ≤ besselInt a z := by
  have hz0 : 0 < z := by linarith
  have hzi : z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
  have hzi0 : 0 < z⁻¹ := inv_pos.2 hz0
  rw [besselInt_eq ha, Real.exp_sub, div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos 1), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos z).le
  -- `∫_0^{1/z} s^a e^{-1} ≤ ∫_0^2 s^a (2−s)^a e^{−zs}`
  have hsub : (∫ s in (0 : ℝ)..z⁻¹, (s ^ 0 * bW a s) * Real.exp (-(z * s))) ≤ bN a 0 z :=
    intervalIntegral.integral_mono_interval le_rfl hzi0.le (by linarith)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_) ((continuous_bN_integrand ha 0
          z).intervalIntegrable _ _)
  · have hlow : (∫ s in (0 : ℝ)..z⁻¹, s ^ a * (Real.exp 1)⁻¹) ≤
        ∫ s in (0 : ℝ)..z⁻¹, (s ^ 0 * bW a s) * Real.exp (-(z * s)) := by
      refine intervalIntegral.integral_mono_on hzi0.le
        (((continuous_id.rpow_const fun _ => Or.inr ha).mul continuous_const).intervalIntegrable _
            _)
        ((continuous_bN_integrand ha 0 z).intervalIntegrable _ _) fun s hs => ?_
      have h1 : 1 ≤ (2 - s) ^ a := Real.one_le_rpow (by linarith [hs.2]) ha
      have h2 : (Real.exp 1)⁻¹ ≤ Real.exp (-(z * s)) := by
        rw [← Real.exp_neg]; refine Real.exp_le_exp.2 ?_
        have : z * s ≤ z * z⁻¹ := mul_le_mul_of_nonneg_left hs.2 hz0.le
        rw [mul_inv_cancel₀ hz0.ne'] at this; linarith
      have h3 : 0 ≤ s ^ a := Real.rpow_nonneg hs.1 a
      simp only [pow_zero, one_mul, bW]
      have : s ^ a ≤ s ^ a * (2 - s) ^ a := le_mul_of_one_le_right h3 h1
      exact mul_le_mul this h2 (by positivity) (by positivity)
    have hI : (∫ s in (0 : ℝ)..z⁻¹, s ^ a * (Real.exp 1)⁻¹) = z⁻¹ ^ (a + 1) / (a + 1) * (Real.exp
        1)⁻¹ := by
      rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by linarith)),
        Real.zero_rpow (by linarith), sub_zero]
    rw [hI] at hlow
    have := hlow.trans hsub
    rw [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos 1)] at this
    linarith
  · exact mul_nonneg (mul_nonneg (pow_nonneg hs.1.le _) (bW_nonneg ⟨hs.1.le, by linarith [hs.2]⟩))
      (Real.exp_pos _).le

end

end

end MetaMathlibExt.ColoredPartitionsJensen
