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

For `n ≥ 1` and `x ∈ ℝ`, the floor gap `⌊nx⌋ - n * A_n(x)` at the rational point `t = p / q`
converges, along `n = pqM`, to the gap limit `m - ∑_{k=1}^m log (t / k)` where `m = ⌊t⌋₊`.
These limits cover every envelope interval, so the set of floor gaps is dense in `[1 - log 2, ∞)`.

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

/-- Factorial logarithm splits off the top factor. -/
private theorem log_factorial_succ {m : ℕ} (hm : 1 ≤ m) :
    Real.log (Nat.factorial m : ℝ) = Real.log m + Real.log (Nat.factorial (m - 1) : ℝ) := by
  have hfact : Nat.factorial m = m * Nat.factorial (m - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hm]
  rw [hfact]
  push_cast
  exact Real.log_mul (by exact_mod_cast (by omega : m ≠ 0))
    (by exact_mod_cast Nat.factorial_ne_zero (m - 1))

/-- Factorial logarithm at a successor. -/
private theorem log_factorial_succ' (m : ℕ) :
    Real.log (Nat.factorial (m + 1) : ℝ)
      = Real.log ((m : ℝ) + 1) + Real.log (Nat.factorial m : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  exact Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero m)

/-- Telescoping sum of `j * log ((j + 1) / j)`. -/
private theorem sum_mul_log_succ {m : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Icc 1 (m - 1), (j : ℝ) * Real.log ((j + 1) / j)
      = ((m - 1 : ℕ) : ℝ) * Real.log m - Real.log (Nat.factorial (m - 1) : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [show (1 : ℕ) - 1 = 0 by rfl]
    simp
  | succ m hm ih =>
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hlog := log_factorial_succ hm
    have hdiv : Real.log (((m : ℝ) + 1) / m) = Real.log ((m : ℝ) + 1) - Real.log m :=
      Real.log_div (by positivity) hm0
    rw [Nat.add_sub_cancel]
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m - 1 + 1) _, Nat.sub_add_cancel hm, ih,
      hdiv, hlog, Nat.cast_sub hm]
    push_cast
    ring

/-- The block limits sum to the logarithmic sum. -/
private theorem telescope {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ≠ 0) :
    ∑ j ∈ Finset.Icc 1 (m - 1), (j : ℝ) * Real.log ((j + 1) / j)
        + (m : ℝ) * Real.log (t / m)
      = ∑ k ∈ Finset.Icc 1 m, Real.log (t / k) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hT1 := sum_log_div ht m
  have hT2 := sum_mul_log_succ hm
  have hdiv : Real.log (t / m) = Real.log t - Real.log m := Real.log_div ht hm0
  rw [hdiv, hT1, hT2, Nat.cast_sub hm]
  push_cast
  linear_combination log_factorial_succ hm

/-- The gap limit at `t = m` equals the upper envelope. -/
private theorem gapLimit_self {m : ℕ} (hm : 1 ≤ m) : gapLimit m m = gapUB m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [gapLimit, gapUB, sum_log_div hm0 m]
  ring

/-- The gap limit at `t = m + 1` equals the lower envelope. -/
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

/-- Successive upper envelope values differ by `δ`. -/
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
  have h4 : (1 : ℝ) < Real.log 4 := by
    have h := Real.log_lt_log (Real.exp_pos 1) (show Real.exp 1 < 4 by linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

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
          show (1 : ℝ) + y ≠ 0
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

/-- Full harmonic blocks converge to the logarithmic ratio. -/
private theorem tendsto_block_full {q j : ℕ} (hq : 0 < q) (hj : 1 ≤ j) :
    Filter.Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (j * (q * q * (M + 1)))
        ((j + 1) * (q * q * (M + 1)) - 1), (1 : ℝ) / k)
      Filter.atTop (nhds (Real.log (((j : ℝ) + 1) / j))) := by
  have hjpos : 0 < j := by omega
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqqW : ∀ M : ℕ, 1 ≤ q * q * (M + 1) := fun M => by
    have hpos : 0 < q * q * (M + 1) := by positivity
    omega
  have hab : ∀ M : ℕ, j * (q * q * (M + 1)) ≤ (j + 1) * (q * q * (M + 1)) - 1 := by
    intro M
    have e : (j + 1) * (q * q * (M + 1))
        = j * (q * q * (M + 1)) + q * q * (M + 1) := by ring
    have h1 := hqqW M
    omega
  have ha : Filter.Tendsto (fun M : ℕ => j * (q * q * (M + 1))) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun M => ?_) Filter.tendsto_id
    show M ≤ j * (q * q * (M + 1))
    have hJ : 1 ≤ j * (q * q) := by
      have hpos : 0 < j * (q * q) := by positivity
      omega
    have e : j * (q * q * (M + 1)) = (j * (q * q)) * (M + 1) := by ring
    rw [e]
    calc M ≤ M + 1 := Nat.le_succ M
      _ = 1 * (M + 1) := (one_mul _).symm
      _ ≤ (j * (q * q)) * (M + 1) := mul_le_mul_of_nonneg_right hJ (Nat.zero_le _)
  have hsub := tendsto_harmonic_block_sub_integral hab ha
  have hC1 : ∀ M : ℕ, 1 ≤ (j + 1) * (q * q * (M + 1)) := fun M => by
    have hpos : 0 < (j + 1) * (q * q * (M + 1)) := by positivity
    omega
  have heq : ∀ M : ℕ, ((((j + 1) * (q * q * (M + 1)) - 1 : ℕ)) : ℝ)
      / (((j * (q * q * (M + 1)) : ℕ)) : ℝ)
      = ((j : ℝ) + 1) / j - 1 / ((j : ℝ) * (q * q * (M + 1))) := by
    intro M
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.cast_sub (hC1 M)]
    push_cast
    field_simp
  have hsmall : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / ((j : ℝ) * (q * q * (M + 1))))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / (((M : ℝ)) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heq2 : ∀ M : ℕ, (1 : ℝ) / ((j : ℝ) * (q * q * (M + 1)))
        = (1 / ((j : ℝ) * (q : ℝ) * q)) * (1 / (((M : ℝ)) + 1)) := by
      intro M
      have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have h2 := h1.const_mul (1 / ((j : ℝ) * (q : ℝ) * q))
    rw [mul_zero] at h2
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun M => (heq2 M).symm)) h2
  have hratio : Filter.Tendsto (fun M : ℕ => ((((j + 1) * (q * q * (M + 1)) - 1 : ℕ)) : ℝ)
      / (((j * (q * q * (M + 1)) : ℕ)) : ℝ))
      Filter.atTop (nhds (((j : ℝ) + 1) / j)) := by
    have hlim : Filter.Tendsto
        (fun M : ℕ => ((j : ℝ) + 1) / j - 1 / ((j : ℝ) * (q * q * (M + 1))))
        Filter.atTop (nhds (((j : ℝ) + 1) / j - 0)) :=
      tendsto_const_nhds.sub hsmall
    rw [sub_zero] at hlim
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun M => (heq M).symm)) hlim
  have hI : Filter.Tendsto
      (fun M : ℕ => ∫ t in (((j * (q * q * (M + 1)) : ℕ)) : ℝ)..((((j + 1) * (q * q * (M + 1)) - 1 : ℕ)) : ℝ), t⁻¹)
      Filter.atTop (nhds (Real.log (((j : ℝ) + 1) / j))) := by
    have hne : ((j : ℝ) + 1) / j ≠ 0 := div_ne_zero (by positivity) hj0
    have hlog := (Real.continuousAt_log hne).tendsto.comp hratio
    apply Filter.Tendsto.congr' _ hlog
    filter_upwards with M
    rw [Function.comp_apply]
    symm
    apply integral_inv_of_pos
    · have hpos : 0 < j * (q * q * (M + 1)) := by positivity
      exact_mod_cast hpos
    · have hpos : 0 < (j + 1) * (q * q * (M + 1)) - 1 := by
        have e : (j + 1) * (q * q * (M + 1))
            = j * (q * q * (M + 1)) + q * q * (M + 1) := by ring
        have h1 := hqqW M
        have hA : 1 ≤ j * (q * q * (M + 1)) := by
          have hp : 0 < j * (q * q * (M + 1)) := by positivity
          omega
        omega
      exact_mod_cast hpos
  have hadd := hsub.add hI
  rw [zero_add] at hadd
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun M => sub_add_cancel _ _)) hadd

/-- The last harmonic block converges to the logarithmic ratio. -/
private theorem tendsto_block_last {p q m : ℕ} (hq : 0 < q) (hm : 1 ≤ m) (hle : m * q ≤ p) :
    Filter.Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (m * (q * q * (M + 1))) (p * q * (M + 1)),
        (1 : ℝ) / k)
      Filter.atTop (nhds (Real.log ((p : ℝ) / ((m : ℝ) * q)))) := by
  have hmpos : 0 < m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hab : ∀ M : ℕ, m * (q * q * (M + 1)) ≤ p * q * (M + 1) := by
    intro M
    have e1 : m * (q * q * (M + 1)) = (m * q) * (q * (M + 1)) := by ring
    have e2 : p * q * (M + 1) = p * (q * (M + 1)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hle (Nat.zero_le _)
  have ha : Filter.Tendsto (fun M : ℕ => m * (q * q * (M + 1))) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun M => ?_) Filter.tendsto_id
    show M ≤ m * (q * q * (M + 1))
    have hJ : 1 ≤ m * (q * q) := by
      have hpos : 0 < m * (q * q) := by positivity
      omega
    have e : m * (q * q * (M + 1)) = (m * (q * q)) * (M + 1) := by ring
    rw [e]
    calc M ≤ M + 1 := Nat.le_succ M
      _ = 1 * (M + 1) := (one_mul _).symm
      _ ≤ (m * (q * q)) * (M + 1) := mul_le_mul_of_nonneg_right hJ (Nat.zero_le _)
  have hsub := tendsto_harmonic_block_sub_integral hab ha
  have hratio : ∀ M : ℕ, ((((p * q * (M + 1) : ℕ))) : ℝ) / ((((m * (q * q * (M + 1)) : ℕ))) : ℝ)
      = (p : ℝ) / ((m : ℝ) * q) := by
    intro M
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  have hI : Filter.Tendsto
      (fun M : ℕ => ∫ t in ((((m * (q * q * (M + 1)) : ℕ))) : ℝ)..((((p * q * (M + 1) : ℕ))) : ℝ), t⁻¹)
      Filter.atTop (nhds (Real.log ((p : ℝ) / ((m : ℝ) * q)))) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => Real.log ((p : ℝ) / ((m : ℝ) * q))) Filter.atTop
        (nhds (Real.log ((p : ℝ) / ((m : ℝ) * q)))) :=
      tendsto_const_nhds
    apply Filter.Tendsto.congr' _ hconst
    filter_upwards with M
    rw [← hratio M]
    symm
    apply integral_inv_of_pos
    · have hpos : 0 < m * (q * q * (M + 1)) := by positivity
      exact_mod_cast hpos
    · have hpos : 0 < p * q * (M + 1) := by
        have hmq : 0 < m * q := by positivity
        have hp : 0 < p := by omega
        positivity
      exact_mod_cast hpos
  have hadd := hsub.add hI
  rw [zero_add] at hadd
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun M => sub_add_cancel _ _)) hadd

/-- Floor gap value. -/
private noncomputable def gapVal (n : ℕ) (x : ℝ) : ℝ :=
  ⌊(n : ℝ) * x⌋ - n * fareyStaircase n x

/-- Block decomposition of the floor gap at a rational point. -/
private theorem gapVal_rat_eq {p q W : ℕ} (hq : 0 < q) (hle : q ≤ p) (hW : 1 ≤ W) :
    gapVal (p * q * W) (((p : ℝ) / q) / (((p * q * W : ℕ)) : ℝ))
      = (⌊(p : ℝ) / q⌋₊ : ℝ) - (∑ j ∈ Finset.Icc 1 (⌊(p : ℝ) / q⌋₊ - 1),
          (j : ℝ) * ∑ k ∈ Finset.Icc (j * (q * q * W)) ((j + 1) * (q * q * W) - 1), (1 : ℝ) / k
        + (⌊(p : ℝ) / q⌋₊ : ℝ)
          * ∑ k ∈ Finset.Icc (⌊(p : ℝ) / q⌋₊ * (q * q * W)) (p * q * W), (1 : ℝ) / k) := by
  set t : ℝ := (p : ℝ) / q with ht
  set m : ℕ := ⌊t⌋₊ with hm_def
  set n : ℕ := p * q * W with hn
  set c : ℕ := q * q * W with hc
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hW0 : 0 < W := by omega
  have hp : 0 < p := by omega
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have ht0 : (0 : ℝ) ≤ t := by
    rw [ht]
    positivity
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hqpos, one_mul]
    exact_mod_cast hle
  have hm1 : 1 ≤ m := by
    rw [hm_def]
    exact Nat.le_floor (by exact_mod_cast ht1)
  have hmt : (m : ℝ) ≤ t := by
    rw [hm_def]
    exact Nat.floor_le ht0
  have htm1 : t < (m : ℝ) + 1 := by
    rw [hm_def]
    exact Nat.lt_floor_add_one t
  have hfloor : ⌊t⌋ = (m : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hmt
    · exact_mod_cast htm1
  have hmq : m * q ≤ p := by
    rw [ht] at hmt
    have h := (le_div_iff₀ hqpos).mp hmt
    exact_mod_cast h
  have hpmq : p < (m + 1) * q := by
    rw [ht] at htm1
    have h := (div_lt_iff₀ hqpos).mp htm1
    exact_mod_cast h
  have htm1' : t < (m : ℝ) + 1 := by rwa [ht]
  have hnpos : 0 < p * q * W := by positivity
  have hn1 : 1 ≤ n := by omega
  have hcpos : 0 < q * q * W := by positivity
  have hc1 : 1 ≤ c := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hcposR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hcnonneg : (0 : ℝ) ≤ c := le_of_lt hcposR
  have hmc : m * c ≤ n := by
    have e1 : m * (q * q * W) = (m * q) * (q * W) := by ring
    have e2 : p * q * W = p * (q * W) := by ring
    rw [hn, hc, e1, e2]
    exact mul_le_mul_of_nonneg_right hmq (Nat.zero_le _)
  have hnm1c : n + 1 ≤ (m + 1) * c := by
    have hpmq1 : p + 1 ≤ (m + 1) * q := by omega
    have hqw1 : 1 ≤ q * W := by
      have hpos : 0 < q * W := by positivity
      omega
    have e1 : (m + 1) * (q * q * W) = ((m + 1) * q) * (q * W) := by ring
    have e2 : p * q * W + 1 ≤ ((m + 1) * q) * (q * W) := by
      have h4 : (p + 1) * (q * W) ≤ ((m + 1) * q) * (q * W) :=
        mul_le_mul_of_nonneg_right hpmq1 (Nat.zero_le _)
      have e3 : (p + 1) * (q * W) = p * q * W + q * W := by ring
      omega
    rw [hn, hc, e1]
    exact e2
  have hnc : (n : ℝ) / (c : ℝ) = t := by
    have hW0R : (W : ℝ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
    have hqqW0 : (q : ℝ) * q * W ≠ 0 := mul_ne_zero (mul_ne_zero hq0 hq0) hW0R
    rw [ht, hn, hc]
    push_cast
    rw [div_eq_div_iff hqqW0 hq0]
    ring
  have hterm : ∀ k : ℕ, (k : ℝ) / (n : ℝ) * t = (k : ℝ) / (c : ℝ) := by
    intro k
    have hW0R : (W : ℝ) ≠ 0 := by exact_mod_cast (by omega : W ≠ 0)
    have hpqw0 : (p : ℝ) * q * W ≠ 0 := mul_ne_zero (mul_ne_zero hp0 hq0) hW0R
    have hqqW0 : (q : ℝ) * q * W ≠ 0 := mul_ne_zero (mul_ne_zero hq0 hq0) hW0R
    rw [ht, hn, hc]
    push_cast
    field_simp
  have hgap : gapVal n (t / n)
      = (m : ℝ) - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) / (c : ℝ)⌋ : ℝ) / k := by
    have hnt : (n : ℝ) * (t / n) = t := by field_simp
    have hB : (n : ℝ) * fareyStaircase n (t / n) = fareyZoom n t := rfl
    unfold gapVal
    rw [hnt, hfloor, Int.cast_natCast, hB, fareyZoom_eq_sum hn1 t]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hterm k]
  have hnat : ∀ k : ℕ, (⌊(k : ℝ) / (c : ℝ)⌋ : ℝ) = ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) := by
    intro k
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) / (c : ℝ) := by positivity
    have e := Int.natCast_floor_eq_floor hnonneg
    have e2 := congrArg (Int.cast : ℤ → ℝ) e
    rw [Int.cast_natCast] at e2
    exact e2.symm
  have hgap2 : gapVal n (t / n)
      = (m : ℝ) - ∑ k ∈ Finset.Icc 1 n, ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) / k := by
    rw [hgap]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hnat k]
  have hmaps : ∀ k ∈ Finset.Icc 1 n, ⌊(k : ℝ) / (c : ℝ)⌋₊ ∈ Finset.Icc 0 m := by
    intro k hk
    have hk1n := Finset.mem_Icc.mp hk
    have hkc0 : (0 : ℝ) ≤ (k : ℝ) / (c : ℝ) := by positivity
    have hle : (k : ℝ) / (c : ℝ) ≤ (n : ℝ) / (c : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hk1n.2) hcnonneg
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    have h1 : ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) / (c : ℝ) := Nat.floor_le hkc0
    have h2 : (k : ℝ) / (c : ℝ) ≤ t := by
      rw [← hnc]
      exact hle
    have h3 : ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) < (m : ℝ) + 1 :=
      lt_of_le_of_lt (le_trans h1 h2) htm1'
    have h4 : ⌊(k : ℝ) / (c : ℝ)⌋₊ < m + 1 := by exact_mod_cast h3
    omega
  have hfiber : ∀ (k j : ℕ), ⌊(k : ℝ) / (c : ℝ)⌋₊ = j ↔ j * c ≤ k ∧ k < (j + 1) * c := by
    intro k j
    have hkc0 : (0 : ℝ) ≤ (k : ℝ) / (c : ℝ) := by positivity
    rw [Nat.floor_eq_iff hkc0]
    constructor
    · intro h
      constructor
      · have h' := (le_div_iff₀ hcposR).mp h.1
        exact_mod_cast h'
      · have h' := (div_lt_iff₀ hcposR).mp h.2
        exact_mod_cast h'
    · intro h
      constructor
      · have h' : ((j * c : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h.1
        push_cast at h'
        exact (le_div_iff₀ hcposR).mpr h'
      · have h' : (k : ℝ) < (((j + 1) * c : ℕ) : ℝ) := by exact_mod_cast h.2
        push_cast at h'
        exact (div_lt_iff₀ hcposR).mpr h'
  have hfilter : ∀ j ∈ Finset.Icc 1 m,
      Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = j) (Finset.Icc 1 n)
        = Finset.Icc (j * c) (min n ((j + 1) * c - 1)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjc1 : 1 ≤ j * c := by
      have hj0' : 0 < j := by omega
      have hc0' : 0 < c := by omega
      have hpos : 0 < j * c := by positivity
      omega
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, hfiber, le_min_iff]
    omega
  have hinner : ∀ j ∈ Finset.Icc 1 m,
      ∑ k ∈ Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = j) (Finset.Icc 1 n),
        ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) / k
      = (j : ℝ) * ∑ k ∈ Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = j) (Finset.Icc 1 n),
        (1 : ℝ) / k := by
    intro j hj
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : ⌊(k : ℝ) / (c : ℝ)⌋₊ = j := (Finset.mem_filter.mp hk).2
    rw [hkj]
    ring
  have hfull : ∀ j ∈ Finset.Icc 1 (m - 1),
      Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = j) (Finset.Icc 1 n)
        = Finset.Icc (j * c) ((j + 1) * c - 1) := by
    intro j hj
    have hj1m : j ∈ Finset.Icc 1 m := by
      rw [Finset.mem_Icc] at hj ⊢
      omega
    have hle : (j + 1) * c - 1 ≤ n := by
      have hjm : j + 1 ≤ m := by
        have h2 := (Finset.mem_Icc.mp hj).2
        omega
      have e : (j + 1) * c ≤ m * c := mul_le_mul_of_nonneg_right hjm (Nat.zero_le _)
      omega
    rw [hfilter j hj1m, min_eq_right hle]
  have hlast :
      Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = m) (Finset.Icc 1 n)
        = Finset.Icc (m * c) n := by
    have hm1m : m ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hm1, le_rfl⟩
    have hle : n ≤ (m + 1) * c - 1 := by omega
    rw [hfilter m hm1m, min_eq_left hle]
  have hzero : ∑ k ∈ Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = 0) (Finset.Icc 1 n),
      ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) / k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : ⌊(k : ℝ) / (c : ℝ)⌋₊ = 0 := (Finset.mem_filter.mp hk).2
    rw [hk0]
    norm_num
  have hsplit0 : Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun (k : ℕ) => ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) / k)
  beta_reduce at hfib
  rw [hsplit0, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 m), hzero, zero_add] at hfib
  have hmain : (∑ j ∈ Finset.Icc 1 m,
        ∑ k ∈ Finset.filter (fun (k : ℕ) => ⌊(k : ℝ) / (c : ℝ)⌋₊ = j) (Finset.Icc 1 n),
          ((⌊(k : ℝ) / (c : ℝ)⌋₊ : ℕ) : ℝ) / k)
      = (∑ j ∈ Finset.Icc 1 (m - 1),
          (j : ℝ) * ∑ k ∈ Finset.Icc (j * c) ((j + 1) * c - 1), (1 : ℝ) / k)
        + (m : ℝ) * ∑ k ∈ Finset.Icc (m * c) n, (1 : ℝ) / k := by
    conv_lhs => rw [← Nat.sub_add_cancel hm1]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m - 1 + 1), Nat.sub_add_cancel hm1]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj1m : j ∈ Finset.Icc 1 m := by
        rw [Finset.mem_Icc] at hj ⊢
        omega
      rw [hinner j hj1m, hfull j hj]
    · have hm1m : m ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hm1, le_rfl⟩
      rw [hinner m hm1m, hlast]
  rw [hgap2, ← hfib, hmain]

/-- Floor gaps at rational points converge to the gap limit. -/
private theorem tendsto_gapVal_rat {p q : ℕ} (hq : 0 < q) (hle : q ≤ p) :
    Filter.Tendsto
      (fun M : ℕ => gapVal (p * q * (M + 1)) (((p : ℝ) / q) / (((p * q * (M + 1) : ℕ)) : ℝ)))
      Filter.atTop (nhds (gapLimit ⌊(p : ℝ) / q⌋₊ ((p : ℝ) / q))) := by
  set t : ℝ := (p : ℝ) / q with ht
  set m : ℕ := ⌊t⌋₊ with hm_def
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have ht0 : (0 : ℝ) ≤ t := by
    rw [ht]
    positivity
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hqpos, one_mul]
    exact_mod_cast hle
  have htne : t ≠ 0 := by linarith
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast ht1)
  have hmt : (m : ℝ) ≤ t := Nat.floor_le ht0
  have hmq : m * q ≤ p := by
    rw [ht] at hmt
    have h := (le_div_iff₀ hqpos).mp hmt
    exact_mod_cast h
  have heq : ∀ M : ℕ, gapVal (p * q * (M + 1)) (t / (((p * q * (M + 1) : ℕ)) : ℝ))
      = (m : ℝ) - (∑ j ∈ Finset.Icc 1 (m - 1),
          (j : ℝ) * ∑ k ∈ Finset.Icc (j * (q * q * (M + 1))) ((j + 1) * (q * q * (M + 1)) - 1),
            (1 : ℝ) / k
        + (m : ℝ) * ∑ k ∈ Finset.Icc (m * (q * q * (M + 1))) (p * q * (M + 1)), (1 : ℝ) / k) :=
    fun M => gapVal_rat_eq hq hle (by omega)
  have hsum : Filter.Tendsto
      (fun M : ℕ => ∑ j ∈ Finset.Icc 1 (m - 1),
        (j : ℝ) * ∑ k ∈ Finset.Icc (j * (q * q * (M + 1))) ((j + 1) * (q * q * (M + 1)) - 1),
          (1 : ℝ) / k)
      Filter.atTop (nhds (∑ j ∈ Finset.Icc 1 (m - 1), (j : ℝ) * Real.log (((j : ℝ) + 1) / j))) := by
    refine tendsto_finsetSum _ (fun j hj => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact (tendsto_block_full hq hj1).const_mul _
  have hlastM : Filter.Tendsto
      (fun M : ℕ => (m : ℝ)
        * ∑ k ∈ Finset.Icc (m * (q * q * (M + 1))) (p * q * (M + 1)), (1 : ℝ) / k)
      Filter.atTop (nhds ((m : ℝ) * Real.log (t / m))) := by
    have h := (tendsto_block_last hq hm1 hmq).const_mul (m : ℝ)
    have e : (p : ℝ) / ((m : ℝ) * q) = t / m := by
      rw [ht, div_div, mul_comm (m : ℝ) q]
    rw [e] at h
    exact h
  have hadd := hsum.add hlastM
  have hfinal : Filter.Tendsto
      (fun M : ℕ => gapVal (p * q * (M + 1)) (t / (((p * q * (M + 1) : ℕ)) : ℝ)))
      Filter.atTop (nhds ((m : ℝ) - (∑ j ∈ Finset.Icc 1 (m - 1),
        (j : ℝ) * Real.log (((j : ℝ) + 1) / j) + (m : ℝ) * Real.log (t / m)))) := by
    have hsub := hadd.const_sub (m : ℝ)
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun M => (heq M).symm)) hsub
  have htel := telescope hm1 htne
  have hlim : gapLimit m t
      = (m : ℝ) - (∑ j ∈ Finset.Icc 1 (m - 1), (j : ℝ) * Real.log (((j : ℝ) + 1) / j)
        + (m : ℝ) * Real.log (t / m)) := by
    rw [gapLimit, htel]
  rw [hlim]
  exact hfinal

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
  show y / (k : ℝ) ≠ 0
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
