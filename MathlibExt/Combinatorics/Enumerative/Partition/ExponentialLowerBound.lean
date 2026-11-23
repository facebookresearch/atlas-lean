/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical integer partitions and cardinalities, narrow the public interface, and add
importing-client tests.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.NumberTheory.ZetaValues
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-! # A lower bound for the number of partitions

`exists_exp_div_pow_le_card`: there are constants H > 0 and B with the number of partitions
of E at least H·exp(c·√E)/E^B for all E ≥ 1, where c = π·√(2/3).
Appendix B of [*A 2^o(n) Time Algorithm for 3-SAT*](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/paper.pdf)
by Claude (Anthropic) quotes the asymptotic formula of Hardy and
Ramanujan, which gives B = 1; here B = 3890, which is enough where the bound is used.

The proofs are adapted from `eth/proof/rates/ClauseBound/Part/Lower.lean` in
https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean.

The proof is Erdős's induction on n through the recurrence n·p(n) = Σ_{k,v ≥ 1, kv ≤ n} v·p(n − kv).
Write f(m) = exp(c·√m)/m^B and s = √n. For small n the bound holds because
H is small. For large n:

* f(n − x)/f(n) ≥ exp(−α·x)·(1 − γ·x²) for 0 ≤ x < n, with α = c/(2s) − B/n and γ = c/(2s³)
  (`ratio_ge`), and the right-hand side is not positive for x ≥ n;
* so for every k the sum of v·f(n − kv)/f(n) over the v with kv < n is at least the whole series Σ_v
  v·e^{−αkv}·(1 − γk²v²), which is at least
  1/(αk)² − 1/4 − 486·γ·k²/(αk)⁴ as long as αk ≤ 2 (`sum_v_ge`, from the closed form of Σ v·r^v,
  1/sinh² z ≥ 1/z² − 1, and Σ v³·r^v ≤ 6/(1 − r)⁴);
* the sum of this over k ≤ K = ⌈1/α⌉ is at least (ζ(2) − 1/K)/α² − K/4 − 486·γ·ζ(2)/α⁴ (`sum_k_ge`),
  with ζ(2) = π²/6 = c²/4;
* ζ(2)/α² ≥ n + 4B·s/c, and the three losses are together at most 15557·s/c + 1/4 (`step_arith`).

All analytic and arithmetic support statements are private. -/

@[expose] public section

noncomputable section

namespace Nat.Partition

open Finset

private abbrev p (n : ℕ) : ℝ := Fintype.card (Partition n)

private abbrev cHR : ℝ := Real.pi * Real.sqrt ((2 : ℝ) / 3)

private theorem p_pos (n : ℕ) : 1 ≤ p n := by
  exact_mod_cast Fintype.card_pos (α := Partition n)

private theorem mul_p_eq (n : ℕ) :
    n * p n = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), v * p (n - k * v) := by
  exact_mod_cast mul_card_eq_sum n

namespace ExponentialLowerBound

/-! ### Real-variable lemmas -/

/-- √(1 − y) ≥ 1 − y/2 − y²/2 on [0, 1], scaled: √(N − x) ≥ √N − x/(2√N) − x²/(2N√N) for 0 ≤ x ≤ N. -/
private theorem sqrt_sub_ge {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hxs : x ≤ s ^ 2) :
    s - x / (2 * s) - x ^ 2 / (2 * s ^ 3) ≤ Real.sqrt (s ^ 2 - x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y * s ^ 2 := ⟨x / s ^ 2, by field_simp⟩
  have hs2 : 0 < s ^ 2 := by positivity
  have hy0 : 0 ≤ y := by
    by_contra h
    have : y * s ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.1 h) hs2
    linarith
  have hy1 : y ≤ 1 := by
    by_contra h
    have : 1 * s ^ 2 < y * s ^ 2 := mul_lt_mul_of_pos_right (not_le.1 h) hs2
    linarith
  have e : s - y * s ^ 2 / (2 * s) - (y * s ^ 2) ^ 2 / (2 * s ^ 3) = s * (1 - y / 2 - y ^ 2 / 2) := by
    field_simp
  rw [e]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h1 : (1 - y / 2 - y ^ 2 / 2) ^ 2 ≤ 1 - y := by nlinarith [mul_nonneg hy0 hy0, mul_nonneg (mul_nonneg hy0 hy0) (sub_nonneg.2 hy1), mul_nonneg (mul_nonneg hy0 hy0) hy0]
  calc (s * (1 - y / 2 - y ^ 2 / 2)) ^ 2 = s ^ 2 * (1 - y / 2 - y ^ 2 / 2) ^ 2 := by ring
    _ ≤ s ^ 2 * (1 - y) := mul_le_mul_of_nonneg_left h1 hs2.le
    _ = s ^ 2 - y * s ^ 2 := by ring

/-- The comparison function exp(c√m)/m^B at m = s² − x against its value at s²: the quotient is at
least exp(−(c/(2s) − B/s²)·x)·(1 − c·x²/(2s³)). -/
private theorem ratio_ge {c s x : ℝ} (B : ℕ) (hc : 0 ≤ c) (hs : 0 < s) (hx : 0 ≤ x) (hxs : x < s ^ 2) :
    Real.exp (c * s) / (s ^ 2) ^ B * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * (1 - c / (2 * s ^ 3) * x ^ 2))
      ≤ Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hd : 0 < s ^ 2 - x := by linarith
  have h1 : 1 - c / (2 * s ^ 3) * x ^ 2 ≤ Real.exp (-(c / (2 * s ^ 3) * x ^ 2)) := Real.one_sub_le_exp_neg _
  have h2 : (s ^ 2 - x) * Real.exp (x / s ^ 2) ≤ s ^ 2 := by
    have h3 : 1 - x / s ^ 2 ≤ Real.exp (-(x / s ^ 2)) := Real.one_sub_le_exp_neg _
    have h4 : s ^ 2 - x = s ^ 2 * (1 - x / s ^ 2) := by field_simp
    rw [h4, mul_assoc]
    have h5 : (1 - x / s ^ 2) * Real.exp (x / s ^ 2) ≤ 1 := by
      calc _ ≤ Real.exp (-(x / s ^ 2)) * Real.exp (x / s ^ 2) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h6 : (s ^ 2 - x) ^ B * Real.exp (B * (x / s ^ 2)) ≤ (s ^ 2) ^ B := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 B
  have h7 : c * s - c / (2 * s) * x - c / (2 * s ^ 3) * x ^ 2 ≤ c * Real.sqrt (s ^ 2 - x) := by
    have := mul_le_mul_of_nonneg_left (sqrt_sub_ge hs hx hxs.le) hc
    calc _ = c * (s - x / (2 * s) - x ^ 2 / (2 * s ^ 3)) := by ring
      _ ≤ _ := this
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc Real.exp (c * s) * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * (1 - c / (2 * s ^ 3) * x ^ 2)) * (s ^ 2 - x) ^ B
      ≤ Real.exp (c * s) * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * Real.exp (-(c / (2 * s ^ 3) * x ^ 2))) * (s ^ 2 - x) ^ B := by
        gcongr
    _ = Real.exp (c * s - c / (2 * s) * x - c / (2 * s ^ 3) * x ^ 2) * ((s ^ 2 - x) ^ B * Real.exp (B * (x / s ^ 2))) := by
        rw [← Real.exp_add, ← Real.exp_add, mul_comm ((s ^ 2 - x) ^ B) (Real.exp _), ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ Real.exp (c * Real.sqrt (s ^ 2 - x)) * (s ^ 2) ^ B := by
        gcongr

/-- sinh z ≤ z·cosh z for z ≥ 0. -/
private theorem sinh_le_mul_cosh {z : ℝ} (hz : 0 ≤ z) : Real.sinh z ≤ z * Real.cosh z := by
  have h := (convex_Icc (0 : ℝ) z).image_sub_le_mul_sub_of_deriv_le (f := Real.sinh) (C := Real.cosh z)
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [Real.deriv_sinh, Real.cosh_le_cosh, abs_of_pos hx.1, abs_of_nonneg hz]
      exact hx.2.le) 0 (Set.left_mem_Icc.2 hz) z (Set.right_mem_Icc.2 hz) hz
  rw [Real.sinh_zero] at h
  linarith

/-- 1/z² − 1 ≤ 1/sinh² z for z > 0. -/
private theorem inv_sq_sub_one_le {z : ℝ} (hz : 0 < z) : 1 / z ^ 2 - 1 ≤ 1 / Real.sinh z ^ 2 := by
  have hsh : 0 < Real.sinh z := Real.sinh_pos_iff.2 hz
  have hch : 0 < Real.cosh z := Real.cosh_pos z
  have key : (1 - z ^ 2) * Real.sinh z ^ 2 ≤ z ^ 2 := by
    rcases le_total (1 - z ^ 2) 0 with h | h
    · have : (1 - z ^ 2) * Real.sinh z ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
      nlinarith
    · have h1 : Real.sinh z ^ 2 ≤ (z * Real.cosh z) ^ 2 := pow_le_pow_left₀ hsh.le (sinh_le_mul_cosh hz.le) 2
      have h2 : Real.cosh z ^ 2 ≤ Real.exp (z ^ 2) := by
        calc Real.cosh z ^ 2 ≤ Real.exp (z ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hch.le (Real.cosh_le_exp_half_sq z) 2
          _ = Real.exp (z ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have h3 : (1 - z ^ 2) * Real.exp (z ^ 2) ≤ 1 := by
        calc _ ≤ Real.exp (-z ^ 2) * Real.exp (z ^ 2) := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      calc (1 - z ^ 2) * Real.sinh z ^ 2 ≤ (1 - z ^ 2) * (z * Real.cosh z) ^ 2 := mul_le_mul_of_nonneg_left h1 h
        _ = z ^ 2 * ((1 - z ^ 2) * Real.cosh z ^ 2) := by ring
        _ ≤ z ^ 2 * ((1 - z ^ 2) * Real.exp (z ^ 2)) := by gcongr
        _ ≤ z ^ 2 * 1 := by gcongr
        _ = z ^ 2 := mul_one _
  rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Σ_v v·e^{−yv} in closed form is at least 1/y² − 1/4. -/
private theorem T1_ge {y : ℝ} (hy : 0 < y) : 1 / y ^ 2 - 1 / 4 ≤ Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 := by
  have h := inv_sq_sub_one_le (z := y / 2) (by positivity)
  have hE : 0 < Real.exp (y / 2) := Real.exp_pos _
  have hE1 : 1 < Real.exp (y / 2) := Real.one_lt_exp_iff.2 (by positivity)
  have e1 : Real.exp (-y) = 1 / Real.exp (y / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]; congr 1; push_cast; ring
  have e2 : Real.sinh (y / 2) = (Real.exp (y / 2) - 1 / Real.exp (y / 2)) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, one_div]
  rw [e2] at h
  rw [e1]
  generalize Real.exp (y / 2) = E at *
  have hE2 : 0 < E ^ 2 - 1 := by nlinarith
  have e3 : 1 / E ^ 2 / (1 - 1 / E ^ 2) ^ 2 = 1 / 4 * (1 / ((E - 1 / E) / 2) ^ 2) := by
    have : E - 1 / E = (E ^ 2 - 1) / E := by field_simp
    have h' : 1 - 1 / E ^ 2 = (E ^ 2 - 1) / E ^ 2 := by field_simp
    rw [this, h']
    field_simp
    norm_num
  rw [e3]
  have e4 : 1 / y ^ 2 - 1 / 4 = 1 / 4 * (1 / (y / 2) ^ 2 - 1) := by field_simp; norm_num
  rw [e4]
  gcongr

/-- v³ ≤ 6·C(v+3, 3). -/
private theorem cube_le (v : ℕ) : (v : ℝ) ^ 3 ≤ 6 * ((v + 3).choose 3 : ℝ) := by
  have h1 : (v + 3 + 1 - 3) ^ 3 ≤ (v + 3).descFactorial 3 := Nat.pow_sub_le_descFactorial _ _
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : v ^ 3 ≤ (v + 3 + 1 - 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : v ^ 3 ≤ 6 * (v + 3).choose 3 := h2.trans h1
  exact_mod_cast h3

/-- Σ_v v³·r^v ≤ 6/(1 − r)⁴ for 0 ≤ r < 1. -/
private theorem T3_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 6 / (1 - r) ^ 4 := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 3 hr).hasSum
  have hc := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hr).mul_left 6
  refine (hasSum_le (fun v => ?_) hs hc).trans (le_of_eq (by ring))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (cube_le v) (by positivity)

/-- 1 − e^{−y} ≥ y/3 for 0 ≤ y ≤ 2. -/
private theorem one_sub_exp_neg_ge {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) : y / 3 ≤ 1 - Real.exp (-y) := by
  have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have h2 : Real.exp (-y) ≤ 1 / (y + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) h1
  have h3 : 1 / (y + 1) ≤ 1 - y / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### The sum over v for one k -/

/-- Σ_{1 ≤ v ≤ n} v·e^{−yv}·(1 − η·v²) ≥ 1/y² − 1/4 − 486·η/y⁴ if 0 < y ≤ 2 and the terms with v > n
are not positive. -/
private theorem sum_v_ge {y η : ℝ} (hy : 0 < y) (hy2 : y ≤ 2) (hη : 0 ≤ η) (n : ℕ) (hn : 1 ≤ η * (n : ℝ) ^ 2) :
    1 / y ^ 2 - 1 / 4 - 486 * η / y ^ 4 ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(y * v)) * (1 - η * (v : ℝ) ^ 2) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Real.exp (-y) := ⟨_, rfl⟩
  have r0 : 0 < r := hr ▸ Real.exp_pos _
  have r1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg r0.le]
  have e (v : ℕ) : Real.exp (-(y * v)) = r ^ v := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; ring
  have hG : HasSum (fun v : ℕ => (v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) (r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).sub ((summable_pow_mul_geometric_of_norm_lt_one 3 hnorm).hasSum.mul_left η)
  have hle : r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ ∑ v ∈ Icc 1 n, ((v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) := by
    have h := sum_le_hasSum (Icc 1 n) (fun v hv => ?_) hG.neg
    · rw [Finset.sum_neg_distrib] at h
      linarith
    · have e2 : -((v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) = (v : ℝ) * r ^ v * (η * (v : ℝ) ^ 2 - 1) := by ring
      rw [e2]
      rcases Nat.eq_zero_or_pos v with rfl | hv0
      · simp
      · have hvn : n < v := by
          by_contra hcon
          exact hv (Finset.mem_Icc.2 ⟨hv0, not_lt.1 hcon⟩)
        have hvn' : (n : ℝ) ≤ v := by exact_mod_cast hvn.le
        have h2 : η * (n : ℝ) ^ 2 ≤ η * (v : ℝ) ^ 2 := by gcongr
        exact mul_nonneg (by positivity) (by linarith)
  have h3 : ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 486 / y ^ 4 := by
    have h4 : y / 3 ≤ 1 - r := hr ▸ one_sub_exp_neg_ge hy.le hy2
    calc _ ≤ 6 / (1 - r) ^ 4 := T3_le r0.le r1
      _ ≤ 6 / (y / 3) ^ 4 := by gcongr
      _ = 486 / y ^ 4 := by field_simp; norm_num
  have h5 : 1 / y ^ 2 - 1 / 4 ≤ r / (1 - r) ^ 2 := hr ▸ T1_ge hy
  have h6 : η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 486 * η / y ^ 4 := by
    calc _ ≤ η * (486 / y ^ 4) := by gcongr
      _ = _ := by ring
  calc _ ≤ r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v := by linarith
    _ ≤ _ := hle
    _ = _ := Finset.sum_congr rfl fun v _ => by rw [e]; ring

/-! ### The sum over k -/

/-- Σ_{k ≤ K} 1/k² ≤ π²/6. -/
private theorem sum_inv_sq_le (K : ℕ) : ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two

/-- Σ_{k ≤ K} 1/k² ≥ π²/6 − 1/K. -/
private theorem le_sum_inv_sq {K : ℕ} (hK : 1 ≤ K) : Real.pi ^ 2 / 6 - 1 / K ≤ ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 := by
  have h : Real.pi ^ 2 / 6 ≤ ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 + 1 / K := by
    rw [← hasSum_zeta_two.tsum_eq]
    refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun M => ?_
    have h1 : range M ⊆ insert 0 (Ioc 0 (max K M)) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_Ioc.2 ⟨h0, (Finset.mem_range.1 hi).le.trans (le_max_right _ _)⟩)
    have h2 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := K) (n := max K M) (by omega) (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ ((max K M : ℕ) : ℝ)⁻¹ := by positivity
    calc ∑ i ∈ range M, 1 / (i : ℝ) ^ 2 ≤ ∑ i ∈ insert 0 (Ioc 0 (max K M)), 1 / (i : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg h1 fun _ _ _ => by positivity
      _ = ∑ i ∈ Ioc 0 (max K M), 1 / (i : ℝ) ^ 2 := by rw [Finset.sum_insert (by simp)]; simp
      _ = ∑ i ∈ Ioc 0 K, 1 / (i : ℝ) ^ 2 + ∑ i ∈ Ioc K (max K M), 1 / (i : ℝ) ^ 2 :=
          (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (le_max_left _ _)).symm
      _ ≤ _ := by
          simp only [one_div] at h2 ⊢
          linarith
  linarith

/-- The sum over 1 ≤ k ≤ K of the lower bounds for the sums over v. -/
private theorem sum_k_ge {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) {K : ℕ} (hK : 1 ≤ K) :
    1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) - K / 4 - 486 * γ / α ^ 4 * (Real.pi ^ 2 / 6)
      ≤ ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by
  have e : ∀ k ∈ Ioc 0 K, 1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4
      = 1 / α ^ 2 * (1 / (k : ℝ) ^ 2) - 1 / 4 - 486 * γ / α ^ 4 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.1 hk).1
    field_simp
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Ioc, nsmul_eq_mul]
  have h1 := le_sum_inv_sq hK
  have h2 := sum_inv_sq_le K
  have h3 : 1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) ≤ 1 / α ^ 2 * ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 := by gcongr
  have h4 : 486 * γ / α ^ 4 * ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 ≤ 486 * γ / α ^ 4 * (Real.pi ^ 2 / 6) := by gcongr
  have h5 : ((K - 0 : ℕ) : ℝ) * (1 / 4) = K / 4 := by simp; ring
  linarith

/-! ### The arithmetic of the induction step -/

/-- With s = √n, α = c/(2s) − B/s², γ = c/(2s³), c² = 4Z and 1/α ≤ K ≤ 1/α + 1, the lower bound for
the double sum is at least n, if B ≥ 3890 and s ≥ 4B/c + c. -/
private theorem step_arith {c s B α γ Z : ℝ} {K : ℕ} (hc : 0 < c) (hB : 3890 ≤ B) (hs : 4 * B / c + c ≤ s) (hα : α = c / (2 * s) - B / s ^ 2)
    (hγ : γ = c / (2 * s ^ 3)) (hZ : Z = c ^ 2 / 4) (hK1 : 1 / α ≤ K) (hK2 : (K : ℝ) ≤ 1 / α + 1) :
    s ^ 2 ≤ 1 / α ^ 2 * (Z - 1 / K) - K / 4 - 486 * γ / α ^ 4 * Z := by
  have hBc : 0 < 4 * B / c := by positivity
  have hs0 : 0 < s := by linarith
  have hsc : c ≤ s := by linarith
  have hcs : 4 * B ≤ c * s := by
    have : 4 * B / c ≤ s := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  obtain ⟨q, hq⟩ : ∃ q, q = c * s - 2 * B := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = 2 * s ^ 2 / q := ⟨_, rfl⟩
  have hαw : α = 1 / w := by
    rw [hα, hw, hq]
    have : c * s - 2 * B ≠ 0 := by linarith
    field_simp
  have hw0 : 0 < w := by rw [hw]; positivity
  have e1 : 1 / α = w := by rw [hαw]; field_simp
  have e2 : 1 / α ^ 2 = w ^ 2 := by rw [hαw]; field_simp
  have e4 : 486 * γ / α ^ 4 = 486 * γ * w ^ 4 := by rw [hαw]; field_simp
  rw [e1] at hK1 hK2
  rw [e2, e4]
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le hw0 hK1
  -- the gain
  have g1 : s ^ 2 + 4 * B * s / c ≤ w ^ 2 * Z := by
    rw [hw, hZ]
    have e5 : (2 * s ^ 2 / q) ^ 2 * (c ^ 2 / 4) = c ^ 2 * s ^ 4 / q ^ 2 := by field_simp; ring
    rw [e5, le_div_iff₀ (by positivity)]
    have e6 : (s ^ 2 + 4 * B * s / c) * q ^ 2 = s * ((c * s + 4 * B) * q ^ 2) / c := by field_simp
    rw [e6, div_le_iff₀ hc, hq]
    have h7 : (c * s + 4 * B) * (c * s - 2 * B) ^ 2 ≤ (c * s) ^ 3 := by nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ B) (by linarith : (0:ℝ) ≤ B)) (by linarith : (0:ℝ) ≤ 12 * (c * s) - 16 * B)]
    calc s * ((c * s + 4 * B) * (c * s - 2 * B) ^ 2) ≤ s * (c * s) ^ 3 := by gcongr
      _ = c ^ 2 * s ^ 4 * c := by ring
  -- the losses
  have l1 : w ≤ 4 * s / c := by
    rw [hw, div_le_div_iff₀ hq0 hc, hq]
    nlinarith
  have l2 : w ^ 2 * (1 / K) ≤ w := by
    have : 1 / (K : ℝ) ≤ 1 / w := one_div_le_one_div_of_le hw0 hK1
    calc w ^ 2 * (1 / K) ≤ w ^ 2 * (1 / w) := by gcongr
      _ = w := by field_simp
  have l3 : 486 * γ * w ^ 4 * Z ≤ 15552 * s / c := by
    have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    calc 486 * γ * w ^ 4 * Z ≤ 486 * γ * (4 * s / c) ^ 4 * Z := by gcongr
      _ = 15552 * s / c := by rw [hγ, hZ]; field_simp; norm_num
  have l4 : 1 ≤ s / c := by rwa [le_div_iff₀ hc, one_mul]
  have l5 : 4 * B * s / c = 4 * B * (s / c) := by ring
  have l6 : 4 * s / c = 4 * (s / c) := by ring
  have l7 : 15552 * s / c = 15552 * (s / c) := by ring
  have l8 : 15560 * (s / c) ≤ 4 * B * (s / c) := by
    have : (0 : ℝ) ≤ s / c := by positivity
    nlinarith
  nlinarith

/-! ### The induction step -/

/-- c² = 4·ζ(2), with c = π·√(2/3) and ζ(2) = π²/6. -/
private theorem cHR_sq : Real.pi ^ 2 / 6 = cHR ^ 2 / 4 := by
  unfold cHR
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  ring

private theorem cHR_pos : 0 < cHR := by
  unfold cHR
  positivity

/-- If the bound holds below n, and √n ≥ 4B/c + c with B ≥ 3890, it holds at n. -/
private theorem step {H : ℝ} {B : ℕ} (hH : 0 ≤ H) (hB : (3890 : ℝ) ≤ B) {n : ℕ} (hn : 4 * (B : ℝ) / cHR + cHR ≤ Real.sqrt n)
    (ih : ∀ m, 1 ≤ m → m < n → H * Real.exp (cHR * Real.sqrt m) / (m : ℝ) ^ B ≤ p m) :
    H * Real.exp (cHR * Real.sqrt n) / (n : ℝ) ^ B ≤ p n := by
  have hZ := cHR_sq
  have hc : 0 < cHR := cHR_pos
  generalize cHR = c at *
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  rw [← hsdef] at hn ⊢
  have hs2 : s ^ 2 = n := by rw [hsdef, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hBc : 0 < 4 * (B : ℝ) / c := by positivity
  have hs0 : 0 < s := by linarith
  have hsc : c ≤ s := by linarith
  have hcs : 4 * (B : ℝ) ≤ c * s := by
    have : 4 * (B : ℝ) / c ≤ s := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by rw [← hs2]; positivity
    exact_mod_cast this
  obtain ⟨α, hα⟩ : ∃ α, α = c / (2 * s) - B / s ^ 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = c / (2 * s ^ 3) := ⟨_, rfl⟩
  have hα0 : 0 < α := by
    have e : c / (2 * s) - B / s ^ 2 = (c * s - 2 * B) / (2 * s ^ 2) := by field_simp
    rw [hα, e]
    have hden : (0 : ℝ) < 2 * s ^ 2 := by positivity
    exact _root_.div_pos (by linarith) hden
  have hα1 : α ≤ 1 := by
    have h1 : c / (2 * s) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h2 : 0 ≤ (B : ℝ) / s ^ 2 := by positivity
    linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hγn : 1 ≤ γ * (s ^ 2) ^ 2 := by
    have e : γ * (s ^ 2) ^ 2 = c * s / 2 := by rw [hγ]; field_simp
    rw [e]
    linarith
  obtain ⟨K, hK⟩ : ∃ K, K = ⌈1 / α⌉₊ := ⟨_, rfl⟩
  have hw0 : 0 < 1 / α := by positivity
  have hK0 : 1 ≤ K := by rw [hK]; exact Nat.ceil_pos.2 hw0
  have hK1 : 1 / α ≤ K := by rw [hK]; exact Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ 1 / α + 1 := by rw [hK]; exact (Nat.ceil_lt_add_one hw0.le).le
  obtain ⟨F, hF⟩ : ∃ F, F = Real.exp (c * s) / (s ^ 2) ^ B := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  -- one term
  have term : ∀ k v : ℕ, 1 ≤ k → 1 ≤ v →
      H * F * ((v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2)) ≤ if k * v < n then (v : ℝ) * p (n - k * v) else 0 := by
    intro k v hk hv
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = k * v := ⟨_, rfl⟩
    have e1 : α * k * v = α * x := by rw [hx]; ring
    have e2 : γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2 = γ * x ^ 2 := by rw [hx]; ring
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    rw [e1, e2]
    split_ifs with h
    · have hxs : x < s ^ 2 := by rw [hs2, hx]; exact_mod_cast h
      have hr := ratio_ge B hc.le hs0 hx0 hxs
      rw [← hα, ← hγ, ← hF] at hr
      have hm : ((n - k * v : ℕ) : ℝ) = s ^ 2 - x := by rw [Nat.cast_sub h.le, hs2, hx]; push_cast; ring
      have hi := ih (n - k * v) (by omega) (Nat.sub_lt hn0 (Nat.mul_pos hk hv))
      rw [hm] at hi
      calc H * F * ((v : ℝ) * Real.exp (-(α * x)) * (1 - γ * x ^ 2)) = v * (H * (F * (Real.exp (-(α * x)) * (1 - γ * x ^ 2)))) := by ring
        _ ≤ v * (H * (Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B)) := by gcongr
        _ = v * (H * Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B) := by ring
        _ ≤ v * p (n - k * v) := by gcongr
    · have hxs : s ^ 2 ≤ x := by rw [hs2, hx]; exact_mod_cast not_lt.1 h
      have h1 : γ * (s ^ 2) ^ 2 ≤ γ * x ^ 2 := by gcongr
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  -- the sum over v for one k
  have sumv : ∀ k ∈ Ioc 0 K, 1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4
      ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
    intro k hk
    obtain ⟨hk0, hkK⟩ := Finset.mem_Ioc.1 hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkK' : (k : ℝ) ≤ K := by exact_mod_cast hkK
    refine sum_v_ge (by positivity) ?_ (by positivity) n ?_
    · calc α * k ≤ α * (1 / α + 1) := by gcongr; exact hkK'.trans hK2
        _ = 1 + α := by field_simp
        _ ≤ 2 := by linarith
    · rw [← hs2]
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
      calc 1 ≤ γ * (s ^ 2) ^ 2 := hγn
        _ = γ * 1 * (s ^ 2) ^ 2 := by ring
        _ ≤ γ * (k : ℝ) ^ 2 * (s ^ 2) ^ 2 := by gcongr
  -- the recurrence
  have hrec : ((n : ℝ) * p n) = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * p (n - k * v) := by exact_mod_cast mul_p_eq n
  have hmain : H * F * s ^ 2 ≤ (n : ℝ) * p n := by
    calc H * F * s ^ 2 ≤ H * F * ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by
          gcongr
          exact (step_arith hc hB hn hα hγ hZ hK1 hK2).trans (sum_k_ge hα0 hγ0 hK0)
      _ ≤ H * F * ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
          gcongr with k hk
          exact sumv k hk
      _ = ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, H * F * ((v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, if k * v < n then (v : ℝ) * p (n - k * v) else 0 :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun v hv => term k v (Finset.mem_Ioc.1 hk).1 (Finset.mem_Icc.1 hv).1
      _ = ∑ v ∈ Icc 1 n, ∑ k ∈ Ioc 0 K, if k * v < n then (v : ℝ) * p (n - k * v) else 0 := Finset.sum_comm
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * p (n - k * v) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => by positivity
          obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
          exact Finset.mem_Icc.2 ⟨(Finset.mem_Ioc.1 hk1).1, (Nat.le_div_iff_mul_le (Finset.mem_Icc.1 hv).1).2 hk2.le⟩
      _ = (n : ℝ) * p n := hrec.symm
  rw [← hs2, mul_div_assoc, ← hF]
  rw [← hs2, mul_comm (s ^ 2)] at hmain
  exact le_of_mul_le_mul_right hmain (by positivity)

end ExponentialLowerBound

open ExponentialLowerBound

/-- The number of partitions of `n` is at least
`H * exp (pi * sqrt (2 / 3) * sqrt n) / n ^ B` for some `H > 0` and natural `B`, when `n ≥ 1`. -/
theorem exists_exp_div_pow_le_card :
    ∃ (H : ℝ) (B : ℕ), 0 < H ∧ ∀ n : ℕ, 1 ≤ n →
      H * Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) / (n : ℝ) ^ B ≤
        (Fintype.card (Partition n) : ℝ) := by
  change ∃ (H : ℝ) (B : ℕ), 0 < H ∧ ∀ E : ℕ, 1 ≤ E →
    H * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ B ≤ p E
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((4 * ((3890 : ℕ) : ℝ) / cHR + cHR) ^ 2)
  refine ⟨Real.exp (-(cHR * Real.sqrt n₀)), 3890, Real.exp_pos _, fun E => ?_⟩
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE
    rcases lt_or_ge E n₀ with h | h
    · have h1 : (1 : ℝ) ≤ p E := by exact_mod_cast p_pos E
      have h2 : (1 : ℝ) ≤ (E : ℝ) ^ 3890 := one_le_pow₀ (by exact_mod_cast hE)
      have h3 : Real.sqrt E ≤ Real.sqrt n₀ := Real.sqrt_le_sqrt (by exact_mod_cast h.le)
      have h4 : Real.exp (-(cHR * Real.sqrt n₀)) * Real.exp (cHR * Real.sqrt E) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]
        have := mul_le_mul_of_nonneg_left h3 cHR_pos.le
        linarith
      refine le_trans ?_ h1
      rw [div_le_one (by positivity)]
      exact h4.trans h2
    · refine step (Real.exp_pos _).le (by norm_num) ?_ fun m hm1 hm => ih m hm hm1
      have h5 : ((4 * ((3890 : ℕ) : ℝ) / cHR + cHR) ^ 2) ≤ (E : ℝ) := hn₀.trans (by exact_mod_cast h)
      exact (le_abs_self _).trans (Real.abs_le_sqrt h5)

end Nat.Partition
