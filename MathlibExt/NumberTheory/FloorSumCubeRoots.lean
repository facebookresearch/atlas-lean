/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Convex.HermiteHadamard

/-! # Floor of a sum of cube roots

Concavity puts each trapezoid below the graph of the cube root. The first interval contributes
an error of `1 / 4`. On a later unit interval, extending the preceding chord gives an upper
bound, so the error on that interval is at most half the drop between adjacent chord slopes.
These slope differences telescope, bounding the total error by `3 / 4`. Evaluating the
integral up to `10 ^ (3 * m)` then locates the sum between consecutive integers.
-/

open MeasureTheory intervalIntegral Set Finset

namespace MathlibExt.NumberTheory.OeisConjecturesWanted

private theorem integral_unit_affine (a c v : ℝ) :
    (∫ t in a..a + 1, c + (t - a) * v) = c + v / 2 := by
  have h : (fun t : ℝ => c + (t - a) * v) = fun t => (c - a * v) + v * t := by
    funext t
    ring
  have h₁ : IntervalIntegrable (fun _ : ℝ => c - a * v) volume a (a + 1) :=
    continuous_const.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t : ℝ => v * t) volume a (a + 1) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [h, intervalIntegral.integral_add h₁ h₂, integral_const_on_unit_interval,
    intervalIntegral.integral_const_mul, integral_id]
  ring

private theorem unit_trapezoid_eq (f : ℝ → ℝ) (a : ℝ) :
    trapezoidal_integral f 1 a (a + 1) = (f a + f (a + 1)) / 2 := by
  rw [trapezoidal_integral_one]
  ring

-- Apply the endpoint bound in Hermite–Hadamard to the negative of a concave function.
private theorem unit_average_le_integral {f : ℝ → ℝ}
    (hc : ConcaveOn ℝ (Ici 0) f) {a : ℝ} (ha : 0 ≤ a) :
    (f a + f (a + 1)) / 2 ≤ ∫ t in a..a + 1, f t := by
  have hsub : Set.Icc a (a + 1) ⊆ Set.Ici (0 : ℝ) := fun _ ht => ha.trans ht.1
  have hcvx := hc.neg.subset hsub (convex_Icc a (a + 1))
  have h := (MetaMathlibExt.hermite_hadamard (by linarith : a < a + 1) hcvx).2
  rw [show a + 1 - a = (1 : ℝ) by ring] at h
  simp only [div_one, one_mul, Pi.neg_apply, intervalIntegral.integral_neg] at h
  linarith only [h]

-- The preceding unit chord, extended to the right, is above the graph.
private theorem integral_unit_le_previous_chord {f : ℝ → ℝ} (hf : Continuous f)
    (hc : ConcaveOn ℝ (Ici 0) f) {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in a..a + 1, f t) ≤ f a + (f a - f (a - 1)) / 2 := by
  rw [← integral_unit_affine a (f a) (f a - f (a - 1))]
  have hcont : Continuous (fun t : ℝ => f a + (t - a) * (f a - f (a - 1))) := by fun_prop
  refine intervalIntegral.integral_mono_on (by linarith) (hf.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _) ?_
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · simp
  · have hprev : a - 1 ∈ Set.Ici (0 : ℝ) := sub_nonneg.mpr ha
    have ht₀ : t ∈ Set.Ici (0 : ℝ) := zero_le_one.trans (ha.trans hat.le)
    have hprevlt : a - 1 < a := by linarith
    have h := hc.slope_anti_adjacent hprev ht₀ hprevlt hat
    rw [show a - (a - 1) = 1 by ring, div_one, div_le_iff₀ (sub_pos.mpr hat)] at h
    rw [mul_comm (f a - f (a - 1)) (t - a)] at h
    linarith only [h]

private noncomputable def cubeRoot (t : ℝ) : ℝ := t ^ (1 / 3 : ℝ)

private theorem cubeRoot_continuous : Continuous cubeRoot :=
  Real.continuous_rpow_const (by norm_num)

private theorem cubeRoot_concave : ConcaveOn ℝ (Ici 0) cubeRoot :=
  Real.concaveOn_rpow (by norm_num) (by norm_num)

@[simp] private theorem cubeRoot_zero : cubeRoot 0 = 0 :=
  Real.zero_rpow (by norm_num)

@[simp] private theorem cubeRoot_one : cubeRoot 1 = 1 :=
  Real.one_rpow _

private theorem integral_cubeRoot (a b : ℝ) :
    (∫ t in a..b, cubeRoot t) = (b ^ (4 / 3 : ℝ) - a ^ (4 / 3 : ℝ)) / (4 / 3 : ℝ) := by
  simpa only [cubeRoot, show (1 / 3 : ℝ) + 1 = 4 / 3 by norm_num] using
    (integral_rpow (a := a) (b := b) (r := (1 / 3 : ℝ)) (Or.inl (by norm_num)))

-- Mathlib's trapezoidal error is approximation minus integral, so negate it here.
private noncomputable def cubeRootError (n : ℕ) : ℝ :=
  -trapezoidal_error cubeRoot n 0 (n : ℝ)

private theorem cubeRootError_add_one (n : ℕ) (hn : 0 < n) :
    cubeRootError (n + 1) = cubeRootError n +
      ((∫ t in (n : ℝ)..(n : ℝ) + 1, cubeRoot t) -
        (cubeRoot (n : ℝ) + cubeRoot ((n : ℝ) + 1)) / 2) := by
  have hI := intervalIntegral.integral_add_adjacent_intervals
    (cubeRoot_continuous.intervalIntegrable (μ := volume) 0 (n : ℝ))
    (cubeRoot_continuous.intervalIntegrable (μ := volume) (n : ℝ) ((n : ℝ) + 1))
  have hT := trapezoidal_integral_ext (f := cubeRoot) (a := 0) (h := 1) hn
  simp only [mul_one, zero_add, unit_trapezoid_eq] at hT
  unfold cubeRootError trapezoidal_error
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hI, ← hT]
  ring

-- The first cell gives a strict gap. Starting at the second, the upper error estimate
-- telescopes by the difference between consecutive unit slopes.
private theorem cubeRootError_bounds (n : ℕ) :
    (1 / 4 : ℝ) ≤ cubeRootError (n + 1) ∧
      cubeRootError (n + 1) + (cubeRoot ((n : ℝ) + 1) - cubeRoot (n : ℝ)) / 2 ≤ 3 / 4 := by
  induction n with
  | zero =>
    have hI : (∫ t in (0 : ℝ)..1, cubeRoot t) = 3 / 4 := by
      rw [integral_cubeRoot, Real.one_rpow, Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0)]
      norm_num
    have hT : trapezoidal_integral cubeRoot 1 0 1 = (1 / 2 : ℝ) := by
      simpa only [zero_add, cubeRoot_zero, cubeRoot_one] using unit_trapezoid_eq cubeRoot 0
    norm_num [cubeRootError, trapezoidal_error, hI, hT]
  | succ n ih =>
    have hn : 0 < n + 1 := Nat.succ_pos _
    have ha : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    have hlow := unit_average_le_integral cubeRoot_concave (zero_le_one.trans ha)
    have hhigh := integral_unit_le_previous_chord cubeRoot_continuous cubeRoot_concave ha
    rw [cubeRootError_add_one (n + 1) hn]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hlow hhigh ⊢
    constructor <;> linarith only [ih.1, ih.2, hlow, hhigh]

private theorem cubeRoot_trapezoid_eq_sum (n : ℕ) (hn : 0 < n) :
    trapezoidal_integral cubeRoot n 0 (n : ℝ) =
      (∑ i ∈ Finset.Icc 1 n, cubeRoot (i : ℝ)) - cubeRoot (n : ℝ) / 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      norm_num [trapezoidal_integral_one]
    · have hn' := Nat.pos_of_ne_zero hz
      have hT := trapezoidal_integral_ext (f := cubeRoot) (a := 0) (h := 1) hn'
      simp only [mul_one, zero_add, unit_trapezoid_eq] at hT
      rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, Nat.cast_one, ← hT, ih hn']
      ring

private theorem cubeRoot_sum_bounds (n : ℕ) (hn : 0 < n) :
    ((∫ t in 0..(n : ℝ), cubeRoot t) + cubeRoot (n : ℝ) / 2 - 1 ≤
        ∑ i ∈ Finset.Icc 1 n, cubeRoot (i : ℝ)) ∧
      (∑ i ∈ Finset.Icc 1 n, cubeRoot (i : ℝ)) <
        (∫ t in 0..(n : ℝ), cubeRoot t) + cubeRoot (n : ℝ) / 2 := by
  cases n with
  | zero => omega
  | succ n =>
    have hE := cubeRootError_bounds n
    unfold cubeRootError trapezoidal_error at hE
    rw [cubeRoot_trapezoid_eq_sum _ (Nat.succ_pos n)] at hE
    have hm : cubeRoot (n : ℝ) ≤ cubeRoot ((n : ℝ) + 1) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    simp only [Nat.cast_succ] at hE ⊢
    constructor <;> linarith only [hE.1, hE.2, hm]

private theorem ten_pow_triple_rpow (m : ℕ) (r : ℝ) :
    ((10 ^ (3 * m) : ℕ) : ℝ) ^ r = ((10 : ℝ) ^ m) ^ (3 * r) := by
  rw [Nat.cast_pow, show 3 * m = m * 3 by omega, pow_mul]
  norm_num only [Nat.cast_ofNat]
  simpa only [Nat.cast_ofNat] using
    (Real.rpow_natCast_mul (x := (10 : ℝ) ^ m) (by positivity) 3 r).symm

/-- **Floor of a sum of cube roots.** For every integer $m \ge 1$, the sum
$S_m = \sum_{i=1}^{10^{3m}} i^{1/3}$ of the real cube roots of $1, 2, \dots, 10^{3m}$ satisfies

$$\lfloor S_m \rfloor = \frac{3 \cdot 10^{4m}}{4} + 5 \cdot 10^{m-1} - 1.$$

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 7. -/
public theorem floor_sum_cbrt (m : ℕ) (hm : 1 ≤ m) :
    Nat.floor (∑ i ∈ Finset.Icc (1 : ℕ) (10 ^ (3 * m)),
        (i : ℝ) ^ (1 / 3 : ℝ)) =
      3 * 10 ^ (4 * m) / 4 + 5 * 10 ^ (m - 1) - 1 := by
  let A : ℕ := 3 * 10 ^ (4 * m) / 4
  let B : ℕ := 5 * 10 ^ (m - 1)
  let N : ℕ := 10 ^ (3 * m)
  have hN : 0 < N := by dsimp [N]; positivity
  have hroot : cubeRoot (N : ℝ) = (10 : ℝ) ^ m := by
    change cubeRoot ((10 ^ (3 * m) : ℕ) : ℝ) = (10 : ℝ) ^ m
    rw [cubeRoot, ten_pow_triple_rpow, show (3 : ℝ) * (1 / 3) = 1 by norm_num,
      Real.rpow_one]
  have hdiv : 4 ∣ 3 * 10 ^ (4 * m) := by
    have hp : 4 ∣ 10 ^ (4 * m) := by
      rw [show 4 * m = 2 + (4 * m - 2) by omega, pow_add]
      exact dvd_mul_of_dvd_left (by decide : (4 : ℕ) ∣ 10 ^ 2) _
    exact dvd_mul_of_dvd_right hp _
  have hmul : A * 4 = 3 * 10 ^ (4 * m) := Nat.div_mul_cancel hdiv
  have hmulR : (A : ℝ) * 4 = 3 * (10 : ℝ) ^ (4 * m) := by exact_mod_cast hmul
  have hI : (∫ t in 0..(N : ℝ), cubeRoot t) = (A : ℝ) := by
    change (∫ t in 0..((10 ^ (3 * m) : ℕ) : ℝ), cubeRoot t) = (A : ℝ)
    have hp : ((10 : ℝ) ^ m) ^ (4 : ℝ) = ((10 : ℝ) ^ m) ^ (4 : ℕ) :=
      Real.rpow_natCast _ _
    rw [integral_cubeRoot, Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0), sub_zero,
      ten_pow_triple_rpow, show (3 : ℝ) * (4 / 3) = 4 by norm_num, hp,
      ← pow_mul, show m * 4 = 4 * m by omega]
    linarith only [hmulR]
  have hpow : (10 : ℝ) ^ m = (10 : ℝ) ^ (m - 1) * 10 := by
    conv_lhs => rw [show m = m - 1 + 1 by omega]
    rw [pow_succ]
  have hB : (B : ℝ) = (10 : ℝ) ^ m / 2 := by
    dsimp [B]
    push_cast
    rw [hpow]
    ring
  have hAB : 1 ≤ A + B := by
    have hB₀ : 0 < B := by dsimp [B]; positivity
    omega
  have hpred : ((A + B - 1 : ℕ) : ℝ) + 1 = (A : ℝ) + (B : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hAB)
  have hb := cubeRoot_sum_bounds N hN
  rw [hI, hroot, ← hB] at hb
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc 1 N, cubeRoot (i : ℝ) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  change Nat.floor (∑ i ∈ Finset.Icc 1 N, cubeRoot (i : ℝ)) = A + B - 1
  refine (Nat.floor_eq_iff hsum).mpr ⟨?_, ?_⟩
  · linarith only [hb.1, hpred]
  · linarith only [hb.2, hpred]

end MathlibExt.NumberTheory.OeisConjecturesWanted
