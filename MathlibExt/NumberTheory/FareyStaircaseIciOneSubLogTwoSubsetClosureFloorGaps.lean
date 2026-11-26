/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.FareyStaircase
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Floor gaps of Farey staircases are dense above `1 - log 2`

For a rational number `t = p / q ≥ 1` with `m = ⌊t⌋₊`, the floor gap `⌊nx⌋ - n * A_n(x)` taken
at `x = t / n` (so that `nx = t`) converges, along `n = pqM` as `M → ∞`, to the gap limit
`m - ∑_{k=1}^m log (t / k)`. For each `m ≥ 1`, the gap limits at the rationals `t ∈ [m, m + 1)`
are dense in the envelope interval from the left-hand limit as `t` approaches `m + 1` to the
value at `t = m`. These intervals cover `[1 - log 2, ∞)`, so the set of floor gaps is dense in
`[1 - log 2, ∞)`.

Statements from David Harry Richman, *Lower Rational Approximations and Farey Staircases*,
INTEGERS 24 (2024), Article A37 (primary text: arXiv:2303.02935).
-/

namespace MetaMathlibExt

@[expose] public section

/-- Gap limit function: `m - ∑_{k=1}^m log (t / k)`. -/
private noncomputable def gapLimit (m : ℕ) (t : ℝ) : ℝ :=
  (m : ℝ) - ∑ k ∈ Finset.Icc 1 m, Real.log (t / k)

/-- Upper envelope value at `m`. -/
private noncomputable def gapUB (m : ℕ) : ℝ :=
  (m : ℝ) - (m : ℝ) * Real.log m + Real.log (Nat.factorial m : ℝ)

/-- Lower envelope value at `m`. -/
private noncomputable def gapLB (m : ℕ) : ℝ :=
  (m : ℝ) - (m : ℝ) * Real.log ((m : ℝ) + 1) + Real.log (Nat.factorial m : ℝ)

/-- Product over `Icc 1 m` equals the factorial. -/
private theorem prod_Icc_one_eq_factorial (m : ℕ) :
    ∏ k ∈ Finset.Icc 1 m, (k : ℝ) = (Nat.factorial m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1) (fun k => (k : ℝ)), ih,
      Nat.factorial_succ]
    push_cast
    ring

/-- Sum of `log (t / k)` over `Icc 1 m`. -/
private theorem sum_log_div {t : ℝ} (ht : t ≠ 0) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, Real.log (t / k)
      = (m : ℝ) * Real.log t - Real.log (Nat.factorial m : ℝ) := by
  have hmem : ∀ k ∈ Finset.Icc 1 m, (k : ℝ) ≠ 0 := fun k hk => by
    have h1k : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  have h2 : ∑ k ∈ Finset.Icc 1 m, Real.log (k : ℝ) = Real.log (Nat.factorial m : ℝ) := by
    rw [← Real.log_prod (fun k hk => hmem k hk)]
    congr 1
    exact prod_Icc_one_eq_factorial m
  have h1 : ∑ k ∈ Finset.Icc 1 m, Real.log (t / k)
      = ∑ k ∈ Finset.Icc 1 m, Real.log t - ∑ k ∈ Finset.Icc 1 m, Real.log (k : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact Real.log_div ht (hmem k hk)
  rw [h1, h2]
  simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]

/-- Factorial logarithm at a successor. -/
private theorem log_factorial_succ' (m : ℕ) :
    Real.log (Nat.factorial (m + 1) : ℝ)
      = Real.log ((m : ℝ) + 1) + Real.log (Nat.factorial m : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  exact Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero m)

/-- The gap limit at `t = m` equals the upper envelope. -/
private theorem gapLimit_self {m : ℕ} (hm : 1 ≤ m) : gapLimit m m = gapUB m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [gapLimit, gapUB, sum_log_div hm0 m]
  ring

/-- The endpoint of the fixed-`m` branch at `t = m + 1` (the left-hand limit of the gap limit as
`t` approaches `m + 1`, with `m` held fixed) equals the lower envelope. -/
private theorem gapLimit_succ {m : ℕ} (_hm : 1 ≤ m) :
    gapLimit m ((m : ℝ) + 1) = gapLB m := by
  have ht0 : (m : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  rw [gapLimit, gapLB, sum_log_div ht0 m]
  ring

/-- Lower envelope at `1`. -/
private theorem gapLB_one : gapLB 1 = 1 - Real.log 2 := by
  rw [gapLB]
  norm_num [Nat.factorial_one, Real.log_one]

/-- Upper envelope at `1`. -/
private theorem gapUB_one : gapUB 1 = 1 := by
  rw [gapUB]
  norm_num [Nat.factorial_one, Real.log_one]

/-- Successive upper envelope values differ by `1 - m log ((m + 1) / m)`. -/
private theorem gapUB_sub {m : ℕ} (hm : 1 ≤ m) :
    gapUB (m + 1) - gapUB m = 1 - (m : ℝ) * Real.log (((m : ℝ) + 1) / m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiv : Real.log (((m : ℝ) + 1) / m) = Real.log ((m : ℝ) + 1) - Real.log m :=
    Real.log_div (by positivity) hm0
  rw [gapUB, gapUB, log_factorial_succ' m, hdiv]
  push_cast
  ring

/-- Lower envelope in terms of the upper envelope. -/
private theorem gapLB_eq {m : ℕ} (_hm : 1 ≤ m) : gapLB m = gapUB (m + 1) - 1 := by
  rw [gapLB, gapUB, log_factorial_succ' m]
  push_cast
  ring

/-- Each envelope step is less than one half. -/
private theorem delta_lt_half {m : ℕ} (hm : 1 ≤ m) :
    1 - (m : ℝ) * Real.log (((m : ℝ) + 1) / m) < 1 / 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have heq : ((m : ℝ) + 1) / m = 1 + 1 / (m : ℝ) := by
    rw [add_div, div_self hm0]
  have hpos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hbern : (2 : ℝ) ≤ (1 + 1 / (m : ℝ)) ^ m := by
    have h := one_add_mul_le_pow (a := 1 / (m : ℝ)) (by linarith) m
    rw [mul_one_div_cancel hm0] at h
    linarith
  have hlog : Real.log 2 ≤ (m : ℝ) * Real.log (((m : ℝ) + 1) / m) := by
    rw [heq, ← Real.log_pow]
    exact Real.log_le_log (by norm_num) hbern
  linarith [Real.log_two_gt_d9]

/-- Consecutive envelope intervals overlap. -/
private theorem gapLB_succ_lt {m : ℕ} (hm : 1 ≤ m) : gapLB (m + 1) < gapUB m := by
  have e1 := gapLB_eq (show 1 ≤ m + 1 by omega)
  have e2 := gapUB_sub hm
  have e3 := gapUB_sub (show 1 ≤ m + 1 by omega)
  have d1 := delta_lt_half hm
  have d2 := delta_lt_half (show 1 ≤ m + 1 by omega)
  linarith

/-- The first envelope interval is nonempty. -/
private theorem gapLB_one_le_gapUB_one : gapLB 1 ≤ gapUB 1 := by
  rw [gapLB_one, gapUB_one]
  have h : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- Auxiliary function for the logarithm Taylor bound. -/
private noncomputable def psi (x : ℝ) : ℝ := x + x ^ 2 / 2 - (1 + x) * Real.log (1 + x)

/-- Derivative of the auxiliary function. -/
private theorem hasDerivAt_psi {x : ℝ} (hx : x ≠ -1) :
    HasDerivAt psi (x - Real.log (1 + x)) x := by
  have h1x : (1 : ℝ) + x ≠ 0 := fun h => hx (by linarith)
  have hA : HasDerivAt (fun x : ℝ => x + x ^ 2 / 2)
      (1 + (((2 : ℕ) : ℝ) * x ^ (2 - 1) * 1) / 2) x :=
    (hasDerivAt_id x).add (((hasDerivAt_id x).pow 2).div_const 2)
  have h1px : HasDerivAt (fun x : ℝ => 1 + x) (0 + 1) x :=
    (hasDerivAt_const x 1).add (hasDerivAt_id x)
  have hB : HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x))
      ((0 + 1) * Real.log (1 + x) + (1 + x) * ((0 + 1) / (1 + x))) x :=
    h1px.mul (h1px.log h1x)
  have hpsi : HasDerivAt psi
      ((1 + (((2 : ℕ) : ℝ) * x ^ (2 - 1) * 1) / 2)
        - ((0 + 1) * Real.log (1 + x) + (1 + x) * ((0 + 1) / (1 + x)))) x :=
    hA.sub hB
  have hder : (1 + (((2 : ℕ) : ℝ) * x ^ (2 - 1) * 1) / 2)
      - ((0 + 1) * Real.log (1 + x) + (1 + x) * ((0 + 1) / (1 + x)))
      = x - Real.log (1 + x) := by
    have e21 : (2 : ℕ) - 1 = 1 := rfl
    simp only [e21, pow_one]
    push_cast
    field_simp
    ring
  rwa [hder] at hpsi

/-- The auxiliary function is nonnegative on `[0, ∞)`. -/
private theorem psi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psi x := by
  have hmono : MonotoneOn psi (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · unfold psi
      apply ContinuousOn.sub
      · exact continuousOn_id.add ((continuousOn_id.pow 2).div_const 2)
      · apply ContinuousOn.mul
        · exact continuousOn_const.add continuousOn_id
        · apply Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id)
          intro y hy
          have h0y : (0 : ℝ) ≤ y := Set.mem_Ici.mp hy
          change (1 : ℝ) + y ≠ 0
          exact ne_of_gt (by linarith)
    · rw [interior_Ici]
      intro y hy
      have hy0 : (0 : ℝ) < y := Set.mem_Ioi.mp hy
      exact (hasDerivAt_psi (by linarith)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro y hy
      have hy0 : (0 : ℝ) < y := Set.mem_Ioi.mp hy
      rw [(hasDerivAt_psi (by linarith)).deriv]
      have hle : Real.log (1 + y) ≤ y := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + y by linarith)
        linarith
      linarith
  have h0 : psi 0 = 0 := by simp [psi]
  have hle := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rwa [h0] at hle

/-- Quadratic upper bound for `log (1 + x)`. -/
private theorem log_one_add_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / (2 * (1 + x)) := by
  have hpsi := psi_nonneg hx
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hne : (1 : ℝ) + x ≠ 0 := ne_of_gt hpos
  unfold psi at hpsi
  have h1 : (1 + x) * Real.log (1 + x) ≤ x + x ^ 2 / 2 := by linarith
  have h2 : Real.log (1 + x) ≤ (x + x ^ 2 / 2) / (1 + x) := by
    rw [le_div_iff₀ hpos]
    linarith
  have heq : (x + x ^ 2 / 2) / (1 + x) = x - x ^ 2 / (2 * (1 + x)) := by
    field_simp
    ring
  rwa [heq] at h2

/-- Each envelope step is at least `1 / (4 * j)`. -/
private theorem delta_ge {j : ℕ} (hj : 1 ≤ j) :
    1 / (4 * (j : ℝ)) ≤ 1 - (j : ℝ) * Real.log (((j : ℝ) + 1) / j) := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hj0 : (j : ℝ) ≠ 0 := ne_of_gt hjpos
  have heq : ((j : ℝ) + 1) / j = 1 + 1 / (j : ℝ) := by
    rw [add_div, div_self hj0]
  have hbound := log_one_add_le (show (0 : ℝ) ≤ 1 / (j : ℝ) by positivity)
  have hmul : (j : ℝ) * Real.log (1 + 1 / (j : ℝ))
      ≤ (j : ℝ) * (1 / (j : ℝ) - (1 / (j : ℝ)) ^ 2 / (2 * (1 + 1 / (j : ℝ)))) :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt hjpos)
  have h1ne : (1 : ℝ) + 1 / (j : ℝ) ≠ 0 := by positivity
  have h2ne : (j : ℝ) + 1 ≠ 0 := by positivity
  have hcomp : (j : ℝ) * (1 / (j : ℝ) - (1 / (j : ℝ)) ^ 2 / (2 * (1 + 1 / (j : ℝ))))
      = 1 - 1 / (2 * ((j : ℝ) + 1)) := by
    field_simp
  have hle : (j : ℝ) * Real.log (1 + 1 / (j : ℝ)) ≤ 1 - 1 / (2 * ((j : ℝ) + 1)) := by
    rw [← hcomp]
    exact hmul
  have hfrac : (1 : ℝ) / (4 * j) ≤ 1 / (2 * ((j : ℝ) + 1)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  rw [heq]
  linarith

/-- Harmonic sums over `range` and `Icc` agree. -/
private theorem sum_range_one_div_eq (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1)
      = ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) _, ih]
    congr 1
    norm_cast

/-- The upper envelope is unbounded. -/
private theorem gapUB_unbounded (Y : ℝ) : ∃ m : ℕ, 1 ≤ m ∧ Y < gapUB m := by
  have hG : ∀ m : ℕ,
      gapUB (m + 1) = 1 + ∑ j ∈ Finset.Icc 1 m, (gapUB (j + 1) - gapUB j) := by
    intro m
    induction m with
    | zero => simp [gapUB_one]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) _]
      linarith
  obtain ⟨N, hN⟩ := (Filter.Tendsto.eventually_gt_atTop
    Real.tendsto_sum_range_one_div_nat_succ_atTop (4 * (Y - 1))).exists
  refine ⟨N + 1, by omega, ?_⟩
  rw [sum_range_one_div_eq N] at hN
  rw [hG N]
  have hsum : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (4 * j)
      ≤ ∑ j ∈ Finset.Icc 1 N, (gapUB (j + 1) - gapUB j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [gapUB_sub hj1]
    exact delta_ge hj1
  have hdiv : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (4 * j)
      = (∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / j) / 4 := by
    have e : ∀ j ∈ Finset.Icc 1 N, (1 : ℝ) / (4 * (j : ℝ)) = (1 / 4) * ((1 : ℝ) / (j : ℝ)) :=
      fun j _ => by ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    ring
  linarith

/-- Floor gap value. -/
private noncomputable def gapVal (n : ℕ) (x : ℝ) : ℝ :=
  ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x

/-- The floor gap at `x = t / n` is `(1 - 1/n)` times the rescaled Farey staircase increment
`n² (A_n(t / n) - A_{n-1}(t / n))`, so it converges to the gap limit along all orders. -/
private theorem tendsto_gapVal {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun n : ℕ => gapVal n (t / n)) Filter.atTop (nhds (gapLimit ⌊t⌋₊ t)) := by
  have hone : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - (n : ℝ)⁻¹) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hval : gapLimit ⌊t⌋₊ t = 1 * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 - Real.log (t / k)) := by
    simp [gapLimit, Finset.sum_sub_distrib]
  rw [hval]
  refine (hone.mul (tendsto_sq_mul_fareyStaircase_sub ht)).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [(fareyStaircase_sub_eq hn (t / n)).2, gapVal]
  generalize ((⌊(n : ℝ) * (t / n)⌋ : ℤ) : ℝ) = F
  generalize fareyStaircase n (t / n) = A
  field_simp

/-- Floor gaps at rational points converge to the gap limit. -/
private theorem tendsto_gapVal_rat {p q : ℕ} (hq : 0 < q) (hle : q ≤ p) :
    Filter.Tendsto
      (fun M : ℕ => gapVal (p * q * (M + 1)) (((p : ℝ) / q) / (((p * q * (M + 1) : ℕ)) : ℝ)))
      Filter.atTop (nhds (gapLimit ⌊(p : ℝ) / q⌋₊ ((p : ℝ) / q))) := by
  have hpq : 0 < p * q := Nat.mul_pos (by omega) hq
  have hN : Filter.Tendsto (fun M : ℕ => p * q * (M + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun M => (Nat.le_succ M).trans (Nat.le_mul_of_pos_left _ hpq))
      Filter.tendsto_id
  exact (tendsto_gapVal (by positivity)).comp hN

/-- The gap limit is continuous in `t`. -/
private theorem gapLimit_continuousOn {m : ℕ} (hm : 1 ≤ m) :
    ContinuousOn (gapLimit m) (Set.Icc (m : ℝ) ((m : ℝ) + 1)) := by
  unfold gapLimit
  apply ContinuousOn.sub continuousOn_const
  refine continuousOn_finsetSum _ (fun k hk => ?_)
  refine Real.continuousOn_log.comp (continuousOn_id.div_const _) ?_
  intro y hy
  have hylo : (m : ℝ) ≤ y := (Set.mem_Icc.mp hy).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (k : ℝ) ≠ 0 := by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  change y / (k : ℝ) ≠ 0
  exact div_ne_zero (ne_of_gt (lt_of_lt_of_le hmpos hylo)) hk0

/-- Rational points with controlled floor approximate any envelope value. -/
private theorem rat_approx {m : ℕ} (hm : 1 ≤ m) {y : ℝ} (hlo : gapLB m ≤ y) (hhi : y ≤ gapUB m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, ∃ p q : ℕ, 0 < q ∧ q ≤ p ∧ t = (p : ℝ) / q ∧ (m : ℝ) ≤ t ∧ t < (m : ℝ) + 1
      ∧ ⌊t⌋₊ = m ∧ |gapLimit m t - y| < ε := by
  have hcont := gapLimit_continuousOn hm
  have hmem : y ∈ Set.Icc (gapLimit m ((m : ℝ) + 1)) (gapLimit m m) := by
    rw [gapLimit_succ hm, gapLimit_self hm]
    exact ⟨hlo, hhi⟩
  obtain ⟨t₀, ht₀mem, ht₀eq⟩ :=
    intermediate_value_Icc' (by linarith : (m : ℝ) ≤ (m : ℝ) + 1) hcont hmem
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousOn_iff.mp hcont) t₀ ht₀mem ε hε
  set a : ℝ := max m (t₀ - δ) with ha
  set b : ℝ := min ((m : ℝ) + 1) (t₀ + δ) with hb
  have hab : a < b := by
    have ht0lo : (m : ℝ) ≤ t₀ := (Set.mem_Icc.mp ht₀mem).1
    have ht0hi : t₀ ≤ (m : ℝ) + 1 := (Set.mem_Icc.mp ht₀mem).2
    rw [ha, hb]
    apply max_lt_iff.mpr
    constructor
    · apply lt_min_iff.mpr
      constructor <;> linarith
    · apply lt_min_iff.mpr
      constructor <;> linarith
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn hab
  have htrng : (m : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (m : ℝ) + 1 := by
    have ha : (m : ℝ) ≤ a := le_max_left _ _
    have hb : b ≤ (m : ℝ) + 1 := min_le_left _ _
    constructor <;> linarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := le_trans (by exact_mod_cast hm) htrng.1
  have hr1Q : (1 : ℚ) ≤ r := by exact_mod_cast hr1
  have hdenQ : (r.den : ℚ) ≤ (r.num : ℚ) := by
    have hposQ : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
    have h2 : (1 : ℚ) ≤ (r.num : ℚ) / (r.den : ℚ) := by
      rw [Rat.num_div_den r]
      exact hr1Q
    have h := (le_div_iff₀ hposQ).mp h2
    rwa [one_mul] at h
  have hnpos : 0 ≤ r.num := by
    have hr0 : (0 : ℚ) < r := lt_of_lt_of_le (by norm_num) hr1Q
    exact (Rat.num_pos.mpr hr0).le
  have hnatAbs := Int.natAbs_of_nonneg hnpos
  have hden : r.den ≤ r.num.natAbs := by
    have h2 : (r.den : ℤ) ≤ r.num := by exact_mod_cast hdenQ
    omega
  have h1 : (r : ℝ) = ((r.num : ℤ) : ℝ) / ((r.den : ℕ) : ℝ) := by
    exact_mod_cast (Rat.num_div_den r).symm
  have eR : ((r.num.natAbs : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) := by rw [← Int.cast_natCast, hnatAbs]
  have htpq : (r : ℝ) = ((r.num.natAbs : ℕ) : ℝ) / ((r.den : ℕ) : ℝ) := by
    rw [h1, ← eR]
  have hfloor : ⌊(r : ℝ)⌋₊ = m :=
    (Nat.floor_eq_iff (le_trans (by positivity) htrng.1)).mpr htrng
  have hmemr : (r : ℝ) ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := ⟨htrng.1, htrng.2.le⟩
  have hdist : dist (r : ℝ) t₀ < δ := by
    rw [Real.dist_eq, abs_lt]
    have ha2 : t₀ - δ ≤ a := le_max_right _ _
    have hb2 : b ≤ t₀ + δ := min_le_right _ _
    constructor <;> linarith
  have hclose : |gapLimit m (r : ℝ) - y| < ε := by
    have h := hδ _ hmemr hdist
    rw [Real.dist_eq, ht₀eq] at h
    exact h
  exact ⟨(r : ℝ), r.num.natAbs, r.den, r.den_pos, hden, htpq, htrng.1, htrng.2, hfloor, hclose⟩

/-- Gap limits at rationals lie in the closure. -/
private theorem gapLimit_mem_closure {p q : ℕ} (hq : 0 < q) (hle : q ≤ p) :
    gapLimit ⌊(p : ℝ) / q⌋₊ ((p : ℝ) / q)
      ∈ closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x} := by
  have hp : 0 < p := by omega
  apply mem_closure_of_tendsto (tendsto_gapVal_rat hq hle)
  filter_upwards with M
  refine ⟨p * q * (M + 1), ?_, _, rfl⟩
  have hpos : 0 < p * q * (M + 1) := by positivity
  omega

/-- Every number above `1 - log 2` lies in some envelope interval. -/
private theorem mem_envelope {y : ℝ} (hy : 1 - Real.log 2 ≤ y) :
    ∃ k : ℕ, 1 ≤ k ∧ gapLB k ≤ y ∧ y ≤ gapUB k := by
  rw [← gapLB_one] at hy
  rcases eq_or_lt_of_le hy with rfl | hlt
  · exact ⟨1, le_rfl, le_rfl, gapLB_one_le_gapUB_one⟩
  · obtain ⟨m, hm1, hGm⟩ := gapUB_unbounded y
    have chain : ∀ m : ℕ, 1 ≤ m → ∀ y : ℝ, gapLB 1 < y → y ≤ gapUB m →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ gapLB k ≤ y ∧ y ≤ gapUB k := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro y h1y hym
        exact ⟨1, le_rfl, le_rfl, h1y.le, hym⟩
      | succ m hm ih =>
        intro y h1y hym
        rcases lt_or_ge y (gapUB m) with hlt | hge
        · obtain ⟨k, hk1, hkm, hlk, huk⟩ := ih y h1y hlt.le
          exact ⟨k, hk1, by omega, hlk, huk⟩
        · rcases eq_or_lt_of_le hge with heq | hlt2
          · have hle : y ≤ gapUB m := le_of_eq heq.symm
            obtain ⟨k, hk1, hkm, hlk, huk⟩ := ih y h1y hle
            exact ⟨k, hk1, by omega, hlk, huk⟩
          · exact ⟨m + 1, by omega, le_rfl, (lt_trans (gapLB_succ_lt hm) hlt2).le, hym⟩
    obtain ⟨k, hk1, _hkm, hlk, huk⟩ := chain m hm1 y hlt hGm.le
    exact ⟨k, hk1, hlk, huk⟩

/-- **Floor gaps of Farey staircases are dense above $1 - \log 2$.** For $n \ge 1$ and
$x \in \mathbb{R}$ let $f_n(x) = \lfloor nx \rfloor - n A_n(x)$, where $A_n$ is the Farey staircase
of order $n$; thus $f_n(x) = \lfloor nx \rfloor - \sum_{k=1}^n \lfloor kx \rfloor / k$. Every real
number $y \ge 1 - \log 2$ lies in the closure of the set
$S = \{f_n(x) : n \ge 1,\ x \in \mathbb{R}\}$, that is, $S$ is dense in $[1 - \log 2, \infty)$.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Theorem 5 (i) (`integers-2024-A37-thm-5`), also Corollary 6
(`integers-2024-A37-cor-6`). -/
public theorem Ici_one_sub_log_two_subset_closure_floor_gaps :
    Set.Ici (1 - Real.log 2) ⊆
      closure {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x} := by
  intro y hy
  have hy' : 1 - Real.log 2 ≤ y := Set.mem_Ici.mp hy
  obtain ⟨k, hk1, hlk, huk⟩ := mem_envelope hy'
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t, p, q, hq, hle, htpq, _, _, hfloor, hclose⟩ :=
    rat_approx hk1 hlk huk (ε / 2) (by linarith)
  have hmem : gapLimit k t ∈ closure
      {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ x : ℝ, y = ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x} := by
    rw [← hfloor, htpq]
    exact gapLimit_mem_closure hq hle
  obtain ⟨s, hsS, hdist⟩ := (Metric.mem_closure_iff.mp hmem) (ε / 2) (by linarith)
  refine ⟨s, hsS, ?_⟩
  have hgy : dist (gapLimit k t) y < ε / 2 := by
    rw [Real.dist_eq]
    exact hclose
  have h1 : dist s (gapLimit k t) < ε / 2 := by rwa [dist_comm]
  calc dist y s = dist s y := dist_comm _ _
    _ ≤ dist s (gapLimit k t) + dist (gapLimit k t) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end

end MetaMathlibExt
