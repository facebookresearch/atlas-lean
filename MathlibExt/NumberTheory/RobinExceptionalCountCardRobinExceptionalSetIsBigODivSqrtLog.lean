/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
public import MathlibExt.NumberTheory.RobinExceptionalCount

/-!
# Failures of Robin's inequality number `O(x / √log x)`

Using the Robin exceptional set defined in `MathlibExt.NumberTheory.RobinExceptionalCount`,
this module proves that its counting function `N_R(x)` is `O(x / √log x)` as `x → ∞`.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 2.
-/

open Filter

namespace MetaMathlibExt

/-- Lower bound for `e ^ γ`: since `γ > 1 / 2`, `e ^ γ > e ^ (1 / 2) > 8 / 5`. -/
private theorem exp_eulerMascheroniConstant_gt :
    8 / 5 < Real.exp Real.eulerMascheroniConstant := by
  have hγ : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hmono : Real.exp (1 / 2 : ℝ) < Real.exp Real.eulerMascheroniConstant :=
    Real.exp_strictMono hγ
  have hexp1 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
    have hring : (Real.exp (1 / 2 : ℝ)) ^ 2
        = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by ring
    rw [hring, ← Real.exp_add]
    congr 1
    norm_num
  have hsq : (8 / 5 : ℝ) ^ 2 < (Real.exp (1 / 2 : ℝ)) ^ 2 := by
    rw [hexp1]
    have h9 := Real.exp_one_gt_d9
    norm_num at h9 ⊢
    linarith
  have hbase : (8 / 5 : ℝ) < Real.exp (1 / 2 : ℝ) :=
    (sq_lt_sq₀ (by norm_num) (Real.exp_pos _).le).mp hsq
  exact hbase.trans hmono

/-- Harmonic sum over `Icc 1 K` is at most `1 + log K`. -/
private theorem harmonic_real_le {K : ℕ} :
    ∑ k ∈ Finset.Icc 1 K, (1 / (k : ℝ)) ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  have heq : (∑ k ∈ Finset.Icc 1 K, (1 / (k : ℝ))) = ((harmonic K : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [one_div]
  rw [heq]
  exact_mod_cast h

/-- `σ(n) / n` equals the sum of reciprocal divisors of `n`. -/
private theorem sigma_div_eq_sum_inv {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)
      = ∑ d ∈ n.divisors, (1 / (d : ℝ)) := by
  have hσ : ArithmeticFunction.sigma 1 n
      = ∑ d ∈ n.divisors, (n / d) := by
    simpa [pow_one] using ArithmeticFunction.sigma_eq_sum_div 1 n
  have hcast : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)
      = ∑ d ∈ n.divisors, (((n / d : ℕ)) : ℝ) := by
    rw [hσ]
    push_cast
    rfl
  rw [hcast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  have hmulR : (d : ℝ) * (((n / d : ℕ)) : ℝ) = (n : ℝ) := by exact_mod_cast hmul
  have hkpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hdpos
  field_simp
  linarith

open Finset in
/-- Sum of `τ` over `Icc 1 N` is at most `N * (1 + log N)`. -/
private theorem sum_tau_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ)
      ≤ (N : ℝ) * (1 + Real.log N) := by
  have h : ∑ n ∈ Icc 1 N, n.divisors.card = ∑ d ∈ Icc 1 N, N / d := by
    rw [show Icc 1 N = Ioc 0 N from Icc_add_one_left_eq_Ioc 0 N]
    simpa only [ArithmeticFunction.sigma_zero_apply] using
      ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div N
  have hR : ∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ) = ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [hR]
  calc ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ)
        ≤ ∑ d ∈ Icc 1 N, ((N : ℝ) / (d : ℝ)) :=
          sum_le_sum fun _ _ => Nat.cast_div_le
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, (1 / (d : ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro d _
          rw [mul_one_div]
    _ ≤ (N : ℝ) * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left harmonic_real_le (Nat.cast_nonneg _)

/-- If `τ(n) < Y` then `σ(n) / n < 2 + (3 / 2) * log log x`. -/
private theorem sigma_div_lt_of_tau_lt {x : ℝ} {n K : ℕ} {Y : ℝ}
    (hx1 : 1 < x) (hY : Y = Real.log x * Real.sqrt (Real.log x))
    (hY1 : 1 ≤ Y) (hK : K = ⌊Y⌋₊) (hn0 : n ≠ 0)
    (htau : ((n.divisors.card : ℕ) : ℝ) < Y) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)
      < 2 + (3 / 2 : ℝ) * Real.log (Real.log x) := by
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY1
  have hK1 : 1 ≤ K := by rw [hK]; exact (Nat.one_le_floor_iff Y).mpr hY1
  have hKY : (K : ℝ) ≤ Y := by rw [hK]; exact Nat.floor_le hYpos.le
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hK1
  have hlogY : Real.log Y = (3 / 2 : ℝ) * Real.log (Real.log x) := by
    rw [hY, Real.log_mul (ne_of_gt hLpos) (ne_of_gt (Real.sqrt_pos.mpr hLpos))]
    rw [Real.log_sqrt hLpos.le]
    ring
  have hlogK : Real.log K ≤ (3 / 2 : ℝ) * Real.log (Real.log x) := by
    rw [← hlogY]
    exact Real.log_le_log hKpos hKY
  rw [sigma_div_eq_sum_inv hn0]
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ K)
    (fun d => (1 / (d : ℝ)))
  have hS1 : ∑ d ∈ n.divisors.filter (fun d => d ≤ K), (1 / (d : ℝ))
      ≤ 1 + (3 / 2 : ℝ) * Real.log (Real.log x) := by
    have hsub : n.divisors.filter (fun d => d ≤ K) ⊆ Finset.Icc 1 K := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      obtain ⟨hdmem, hdK⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
      exact ⟨hdpos, hdK⟩
    have hnn : ∀ d ∈ Finset.Icc 1 K, d ∉ n.divisors.filter (fun d => d ≤ K) →
        (0 : ℝ) ≤ 1 / (d : ℝ) := by
      intro d _ _
      positivity
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have hH := harmonic_real_le (K := K)
    have hlog : (1 : ℝ) + Real.log K ≤ 1 + (3 / 2 : ℝ) * Real.log (Real.log x) := by
      linarith [hlogK]
    exact le_trans hle (le_trans hH hlog)
  have hS2 : ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ K), (1 / (d : ℝ)) < 1 := by
    have hYne : Y ≠ 0 := ne_of_gt hYpos
    have hterm : ∀ d ∈ n.divisors.filter (fun d => ¬ d ≤ K),
        (1 / (d : ℝ)) ≤ 1 / Y := by
      intro d hd
      simp only [Finset.mem_filter] at hd
      obtain ⟨hdmem, hdK⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
      have hdgt : K < d := Nat.not_le.mp hdK
      have hKr : (K : ℝ) < (d : ℝ) := by exact_mod_cast hdgt
      have hYlt : Y < (d : ℝ) := by
        have hflt : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
        have hKd' : ⌊Y⌋₊ + 1 ≤ d := by rw [← hK]; exact hdgt
        have hKd : ((⌊Y⌋₊ : ℕ) : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hKd'
        linarith
      exact one_div_le_one_div_of_le hYpos hYlt.le
    have hsumle := Finset.sum_le_card_nsmul
      (n.divisors.filter (fun d => ¬ d ≤ K)) (fun d => (1 / (d : ℝ))) (1 / Y) hterm
    have hcardle : ((n.divisors.filter (fun d => ¬ d ≤ K)).card : ℝ)
        ≤ ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hnsmul : (n.divisors.filter (fun d => ¬ d ≤ K)).card • (1 / Y)
        = (((n.divisors.filter (fun d => ¬ d ≤ K)).card : ℕ) : ℝ) * (1 / Y) :=
      nsmul_eq_mul _ _
    rw [hnsmul] at hsumle
    have hlt : ((n.divisors.filter (fun d => ¬ d ≤ K)).card : ℝ) * (1 / Y) < 1 := by
      have h1 : ((n.divisors.filter (fun d => ¬ d ≤ K)).card : ℝ) * (1 / Y)
          ≤ ((n.divisors.card : ℕ) : ℝ) * (1 / Y) := by
        apply mul_le_mul_of_nonneg_right hcardle
        positivity
      have h2 : ((n.divisors.card : ℕ) : ℝ) * (1 / Y) < 1 := by
        rw [mul_one_div]
        rw [div_lt_one hYpos]
        exact htau
      exact lt_of_le_of_lt h1 h2
    exact lt_of_le_of_lt hsumle hlt
  have hcomb := add_lt_add_of_le_of_lt hS1 hS2
  rw [hsplit] at hcomb
  linarith [hcomb]

/-- For `√N < n ≤ N`, `log log x - log 4 ≤ log log n`. -/
private theorem log_log_ge {x : ℝ} {N M n : ℕ}
    (hx2 : 2 < x) (hN : N = ⌊x⌋₊) (hM : M = Nat.sqrt N)
    (hMn : M < n) (_hnN : n ≤ N)
    (hlog2 : 2 * Real.log 2 ≤ Real.log x) :
    Real.log (Real.log x) - Real.log 4 ≤ Real.log (Real.log (n : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h2x : (2 : ℝ) ≤ x := le_of_lt hx2
  have hN2 : 2 ≤ N := by rw [hN]; exact Nat.le_floor h2x
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hN2
  have hn1 : 1 ≤ n := by
    have hM0 : 0 ≤ M := Nat.zero_le _
    omega
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hNlt : N < n ^ 2 := by
    have hsq : Nat.sqrt N < n := by rw [← hM]; exact hMn
    exact Nat.sqrt_lt'.mp hsq
  have hNltR : (N : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hNlt
  have hlogN : Real.log N < 2 * Real.log (n : ℝ) := by
    have h1 : Real.log (N : ℝ) < Real.log ((n : ℝ) ^ 2) :=
      Real.log_lt_log hNpos hNltR
    have h2 : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [pow_two, Real.log_mul (ne_of_gt hn0') (ne_of_gt hn0')]
      ring
    rw [h2] at h1
    exact h1
  have hNx : x / 2 ≤ (N : ℝ) := by
    have hflt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    rw [← hN] at hflt
    linarith
  have hx2pos : (0 : ℝ) < x / 2 := by linarith
  have hlogx2 : Real.log (x / 2) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hx2pos hNx
  have hlogx2eq : Real.log (x / 2) = Real.log x - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hx0) (by norm_num)]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : (0 : ℝ) < Real.log x := by linarith [hlog2, hlog2pos]
  have hA : (Real.log x - Real.log 2) / 2 < Real.log (n : ℝ) := by
    linarith [hlogN, hlogx2, hlogx2eq]
  have hApos : (0 : ℝ) < (Real.log x - Real.log 2) / 2 := by
    linarith [hlog2, hlog2pos]
  have hlogA : Real.log ((Real.log x - Real.log 2) / 2)
      < Real.log (Real.log (n : ℝ)) :=
    Real.log_lt_log hApos hA
  have hAge : Real.log x / 4 ≤ (Real.log x - Real.log 2) / 2 := by
    linarith [hlog2]
  have hlogx4pos : (0 : ℝ) < Real.log x / 4 := by linarith [hLpos]
  have hlogge : Real.log (Real.log x / 4)
      ≤ Real.log ((Real.log x - Real.log 2) / 2) :=
    Real.log_le_log hlogx4pos hAge
  have hlogx4eq : Real.log (Real.log x / 4)
      = Real.log (Real.log x) - Real.log 4 := by
    rw [Real.log_div (ne_of_gt hLpos) (by norm_num)]
  linarith [hlogA, hlogge, hlogx4eq]

/-- Robin's inequality holds for `√N < n ≤ N` when `τ(n) < Y`. -/
private theorem robin_holds_of_tau_lt {x : ℝ} {N M n K : ℕ} {Y : ℝ}
    (hx2 : 2 < x) (hN : N = ⌊x⌋₊) (hM : M = Nat.sqrt N)
    (hY : Y = Real.log x * Real.sqrt (Real.log x)) (hY1 : 1 ≤ Y) (hK : K = ⌊Y⌋₊)
    (hMn : M < n) (hnN : n ≤ N) (hn0 : n ≠ 0)
    (hlog2 : 2 * Real.log 2 ≤ Real.log x)
    (hloglog : 10 * (2 + (8 / 5 : ℝ) * Real.log 4) ≤ Real.log (Real.log x))
    (htau : ((n.divisors.card : ℕ) : ℝ) < Y) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)
      < Real.exp Real.eulerMascheroniConstant * (n : ℝ)
        * Real.log (Real.log (n : ℝ)) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hdiv := sigma_div_lt_of_tau_lt hx1 hY hY1 hK hn0 htau
  have hge := log_log_ge hx2 hN hM hMn hnN hlog2
  have hexp := exp_eulerMascheroniConstant_gt
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hLppos : (0 : ℝ) < Real.log (Real.log (n : ℝ)) := by
    have h4pos : (0 : ℝ) ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
    have h4 : Real.log 4 < Real.log (Real.log x) := by linarith [hloglog]
    linarith [hge, h4]
  have hle : 2 + (3 / 2 : ℝ) * Real.log (Real.log x)
      ≤ (8 / 5 : ℝ) * Real.log (Real.log (n : ℝ)) := by
    linarith [hge, hloglog]
  have hlt : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)
      < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
    have h1 : (8 / 5 : ℝ) * Real.log (Real.log (n : ℝ))
        < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) :=
      mul_lt_mul_of_pos_right hexp hLppos
    exact lt_trans (lt_of_lt_of_le hdiv hle) h1
  have hmul : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)
      < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) * (n : ℝ) :=
    (div_lt_iff₀ hnpos).mp hlt
  calc ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)
      < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) * (n : ℝ) :=
        hmul
    _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ)
          * Real.log (Real.log (n : ℝ)) := by ring

/-- `√x ≤ x / √log x` for `1 < x`. -/
private theorem sqrt_le_div {x : ℝ} (hx1 : 1 < x) :
    Real.sqrt x ≤ x / Real.sqrt (Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hLle : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  have hsqrt : Real.sqrt (Real.log x) ≤ Real.sqrt x :=
    Real.sqrt_le_sqrt hLle
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLpos
  have hsqrtxpos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hinv : 1 / Real.sqrt x ≤ 1 / Real.sqrt (Real.log x) :=
    one_div_le_one_div_of_le hsqrtpos hsqrt
  have hmul : x * (1 / Real.sqrt x) ≤ x * (1 / Real.sqrt (Real.log x)) :=
    mul_le_mul_of_nonneg_left hinv hx0.le
  have hxeq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have e1 : Real.sqrt x = x * (1 / Real.sqrt x) := by
    have hne : Real.sqrt x ≠ 0 := ne_of_gt hsqrtxpos
    field_simp
    linarith [hxeq]
  have e2 : x / Real.sqrt (Real.log x) = x * (1 / Real.sqrt (Real.log x)) := by
    rw [div_eq_mul_one_div]
  rw [e1, e2]
  exact hmul

/-- `(√⌊x⌋₊ : ℝ) ≤ x / √log x` for `1 < x`. -/
private theorem natSqrt_le_div {x : ℝ} (hx1 : 1 < x) :
    ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ≤ x / Real.sqrt (Real.log x) := by
  have hx0 : (0 : ℝ) ≤ x := le_of_lt (by linarith : (0 : ℝ) < x)
  have hsq : ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ^ 2 ≤ x := by
    have h1 : Nat.sqrt ⌊x⌋₊ ^ 2 ≤ ⌊x⌋₊ := Nat.sqrt_le' _
    have h2 : ((Nat.sqrt ⌊x⌋₊ ^ 2 : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have h4 : (((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ^ 2) = (((Nat.sqrt ⌊x⌋₊ ^ 2 : ℕ)) : ℝ) := by
      norm_cast
    linarith [h2, h3, h4]
  have hM0 : (0 : ℝ) ≤ ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hMle : ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ≤ Real.sqrt x := by
    have heq : ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ)
        = Real.sqrt (((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ^ 2) :=
      (Real.sqrt_sq hM0).symm
    rw [heq]
    exact Real.sqrt_le_sqrt hsq
  exact le_trans hMle (sqrt_le_div hx1)

/-- Any set of large exceptional numbers has card `≤ 2 * (x / √log x)`. -/
private theorem card_large_le {x : ℝ} {N M : ℕ} {Y : ℝ}
    (hx2 : 2 < x) (hN : N = ⌊x⌋₊) (hM : M = Nat.sqrt N)
    (hY : Y = Real.log x * Real.sqrt (Real.log x)) (hY1 : 1 ≤ Y)
    (hx3 : 3 ≤ x) (hlog2 : 2 * Real.log 2 ≤ Real.log x)
    (hloglog : 10 * (2 + (8 / 5 : ℝ) * Real.log 4) ≤ Real.log (Real.log x))
    (s : Finset ℕ)
    (hs : ∀ n ∈ s, M < n ∧ n ≤ N ∧
      Real.exp Real.eulerMascheroniConstant * (n : ℝ)
        * Real.log (Real.log (n : ℝ)) ≤ ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)) :
    ((s.card : ℕ) : ℝ) ≤ 2 * (x / Real.sqrt (Real.log x)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY1
  have hYle : ∀ n ∈ s, Y ≤ ((n.divisors.card : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨hMn, hnN, hP⟩ := hs n hn
    by_contra hcon
    have htau : ((n.divisors.card : ℕ) : ℝ) < Y := lt_of_not_ge hcon
    have hn0 : n ≠ 0 := by
      have hM0 : 0 ≤ M := Nat.zero_le _
      omega
    have hrob := robin_holds_of_tau_lt hx2 hN hM hY hY1 rfl hMn hnN hn0
      hlog2 hloglog htau
    linarith [hrob, hP]
  have hsum : (s.card : ℝ) * Y ≤ ∑ n ∈ s, ((n.divisors.card : ℕ) : ℝ) := by
    have h1 : (s.card : ℝ) * Y = ∑ _n ∈ s, Y := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    exact Finset.sum_le_sum (fun n hn => hYle n hn)
  have hsub1 : s ⊆ Finset.Ioc M N := by
    intro n hn
    obtain ⟨hMn, hnN, _⟩ := hs n hn
    exact Finset.mem_Ioc.mpr ⟨hMn, hnN⟩
  have hsub2 : Finset.Ioc M N ⊆ Finset.Icc 1 N := by
    intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    obtain ⟨hMn, hnN⟩ := hn
    have hM0 : 0 ≤ M := Nat.zero_le _
    exact ⟨by omega, hnN⟩
  have hle1 : ∑ n ∈ s, ((n.divisors.card : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Ioc M N, ((n.divisors.card : ℕ) : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub1
    intro n _ _
    positivity
  have hle2 : ∑ n ∈ Finset.Ioc M N, ((n.divisors.card : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub2
    intro n _ _
    positivity
  have hle3 := sum_tau_le N
  have hNle : (N : ℝ) ≤ x := by rw [hN]; exact Nat.floor_le hx0.le
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h2x : (2 : ℝ) ≤ x := le_of_lt hx2
    have hN2 : 2 ≤ N := by rw [hN]; exact Nat.le_floor h2x
    exact_mod_cast lt_of_lt_of_le (by norm_num) hN2
  have hlogN : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hNpos hNle
  have h1logx : (1 : ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by
      have hexp : Real.exp 1 < 3 := by
        have h9 := Real.exp_one_lt_d9
        norm_num at h9 ⊢
        linarith
      linarith [hx3]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hbound : (N : ℝ) * (1 + Real.log (N : ℝ)) ≤ 2 * x * Real.log x := by
    have hN1 : (0 : ℝ) ≤ 1 + Real.log (N : ℝ) := by
      have h2N : (2 : ℝ) ≤ (N : ℝ) := by
        have h2x : (2 : ℝ) ≤ x := le_of_lt hx2
        have hN2 : 2 ≤ N := by rw [hN]; exact Nat.le_floor h2x
        exact_mod_cast hN2
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hle := Real.log_le_log (by norm_num) h2N
      linarith [hle, hlog2pos]
    have a1 : (N : ℝ) * (1 + Real.log (N : ℝ)) ≤ x * (1 + Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hNle hN1
    have a2 : x * (1 + Real.log (N : ℝ)) ≤ x * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_left (by linarith [hlogN]) hx0.le
    have g2 : x * (1 + Real.log x) ≤ 2 * x * Real.log x := by
      have hmul : x * (1 + Real.log x) ≤ x * (2 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith [h1logx]) hx0.le
      linarith [hmul]
    linarith [a1, a2, g2]
  have hchain : (s.card : ℝ) * Y ≤ 2 * x * Real.log x :=
    le_trans hsum (le_trans (le_trans hle1 hle2) (le_trans hle3 hbound))
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLpos
  have hpos : (0 : ℝ) < Real.log x * Real.sqrt (Real.log x) := mul_pos hLpos hsqrtpos
  have hlediv : (s.card : ℝ)
      ≤ (2 * x * Real.log x) / (Real.log x * Real.sqrt (Real.log x)) := by
    rw [hY] at hchain
    rw [le_div_iff₀ hpos]
    linarith [hchain]
  have heq : (2 * x * Real.log x) / (Real.log x * Real.sqrt (Real.log x))
      = 2 * (x / Real.sqrt (Real.log x)) := by
    have hLne : Real.log x ≠ 0 := ne_of_gt hLpos
    have hsqrtne : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt hsqrtpos
    field_simp
  linarith [hlediv, heq]

@[expose] public section

/-- **Failures of Robin's inequality number $O(x/\sqrt{\log x})$.** Let $N_R(x)$ be the number
of elements of the Robin exceptional set up to $x$. Then $N_R(x) = O(x / \sqrt{\log x})$ as the
real number $x$ tends to infinity.

Source: Florian Luca and Patrick Solé, *On Robin's Inequality*, INTEGERS 25 (2025), Article A8,
Theorem 2 (`integers-2025-A8-thm-2`). -/
public theorem card_robinExceptionalSet_isBigO_div_sqrt_log :
    (fun x : ℝ => ((robinExceptionalSet x).card : ℝ)) =O[atTop]
      fun x : ℝ => x / Real.sqrt (Real.log x) := by
  classical
  apply Asymptotics.IsBigO.of_bound 3
  have ev3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have evY1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x * Real.sqrt (Real.log x) := by
    have hev : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x := eventually_ge_atTop _
    filter_upwards [hev] with x hx
    have h1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hx
      rwa [Real.log_exp] at h
    have h2 : (1 : ℝ) ≤ Real.sqrt (Real.log x) := by
      have h := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at h
    have h1nn : (0 : ℝ) ≤ Real.log x := by linarith
    have h2nn : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    nlinarith [h1, h2, h1nn, h2nn]
  have evlog2 : ∀ᶠ x : ℝ in atTop, 2 * Real.log 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  have evloglog : ∀ᶠ x : ℝ in atTop,
      10 * (2 + (8 / 5 : ℝ) * Real.log 4) ≤ Real.log (Real.log x) := by
    have htend : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    exact htend.eventually (eventually_ge_atTop _)
  filter_upwards [ev3, evY1, evlog2, evloglog] with x hx3 hY1 hlog2 hloglog
  have hcardnn : (0 : ℝ) ≤ ((robinExceptionalSet x).card : ℝ) := Nat.cast_nonneg _
  have hgnn : (0 : ℝ) ≤ x / Real.sqrt (Real.log x) := by
    apply div_nonneg (by linarith)
    exact Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcardnn, abs_of_nonneg hgnn]
  set N := ⌊x⌋₊ with hNdef
  set M := Nat.sqrt N with hMdef
  have hx2 : (2 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hlarge : ((((robinExceptionalSet x).filter (fun n => M < n)).card : ℕ) : ℝ)
      ≤ 2 * (x / Real.sqrt (Real.log x)) := by
    apply card_large_le hx2 hNdef hMdef rfl hY1 hx3 hlog2 hloglog
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨hnmem, hMn⟩ := hn
    unfold robinExceptionalSet at hnmem
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hnmem
    obtain ⟨⟨h5040, hnN⟩, hP⟩ := hnmem
    refine ⟨hMn, ?_, hP⟩
    rwa [hNdef]
  have hsmall : ((((robinExceptionalSet x).filter (fun n => ¬ M < n)).card : ℕ) : ℝ)
      ≤ x / Real.sqrt (Real.log x) := by
    have hsub : (robinExceptionalSet x).filter (fun n => ¬ M < n)
        ⊆ Finset.Icc 1 M := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨hnmem, hMn⟩ := hn
      unfold robinExceptionalSet at hnmem
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hnmem
      obtain ⟨⟨h5040, _⟩, _⟩ := hnmem
      have hle : n ≤ M := Nat.le_of_not_gt hMn
      exact ⟨by omega, hle⟩
    have hcard : ((((robinExceptionalSet x).filter (fun n => ¬ M < n)).card : ℕ) : ℝ)
        ≤ ((Finset.Icc 1 M).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hIcc : (Finset.Icc 1 M).card = M := by
      rw [Nat.card_Icc]
      simp
    rw [hIcc] at hcard
    have hMle : (M : ℝ) ≤ x / Real.sqrt (Real.log x) := by
      rw [hMdef, hNdef]
      exact natSqrt_le_div hx1
    exact le_trans hcard hMle
  have hcardEq : ((robinExceptionalSet x).card : ℝ)
      = ((((robinExceptionalSet x).filter (fun n => M < n)).card : ℕ) : ℝ)
        + ((((robinExceptionalSet x).filter (fun n => ¬ M < n)).card : ℕ) : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (fun n => M < n)
      (s := robinExceptionalSet x)
    have hcast : ((((robinExceptionalSet x).filter (fun n => M < n)).card : ℕ) : ℝ)
        + ((((robinExceptionalSet x).filter (fun n => ¬ M < n)).card : ℕ) : ℝ)
        = (((robinExceptionalSet x).card : ℕ) : ℝ) := by exact_mod_cast h
    linarith [hcast]
  linarith [hcardEq, hlarge, hsmall]

end

end MetaMathlibExt
