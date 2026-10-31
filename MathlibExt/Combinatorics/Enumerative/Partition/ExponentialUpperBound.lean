/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical partition cardinalities, keep proof helpers private, narrow imports, and add
importing-client tests.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.NumberTheory.ZetaValues
public import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-!
# An exponential upper bound for integer partitions

The number of integer partitions of `n` is at most
`exp (π * sqrt (2 / 3) * sqrt n)`. The proof is Erdős's induction through the exact
partition-count recurrence. It is adapted from `eth/proof/rates/ClauseBound/Part/Upper.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace Nat.Partition

open Finset

private theorem sqrt_sub_le {n x : ℝ} (hn : 0 < n) (hx : x ≤ n) :
    Real.sqrt (n - x) ≤ Real.sqrt n - x / (2 * Real.sqrt n) := by
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hhalf : x / (2 * Real.sqrt n) ≤ Real.sqrt n / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
  have hsq : (Real.sqrt n - x / (2 * Real.sqrt n)) ^ 2 =
      n - x + (x / (2 * Real.sqrt n)) ^ 2 := by
    rw [sub_sq, hss]
    field_simp
  rw [hsq]
  nlinarith [sq_nonneg (x / (2 * Real.sqrt n))]

private theorem exp_div_le {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 ≤ 1 / y ^ 2 := by
  have hq : 0 < Real.exp (-(y / 2)) := Real.exp_pos _
  have hr : Real.exp (-y) = Real.exp (-(y / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hone : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsinh : y / 2 ≤ (Real.exp (y / 2) - Real.exp (-(y / 2))) / 2 := by
    rw [← Real.sinh_eq]
    exact Real.self_le_sinh_iff.2 (by positivity)
  have hbound : y * Real.exp (-(y / 2)) ≤ 1 - Real.exp (-(y / 2)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsinh hq.le
    nlinarith
  have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hden : 0 < (1 - Real.exp (-y)) ^ 2 := by positivity
  have hy2 : 0 < y ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hy2, one_mul, hr]
  calc
    Real.exp (-(y / 2)) ^ 2 * y ^ 2 = (y * Real.exp (-(y / 2))) ^ 2 := by ring
    _ ≤ (1 - Real.exp (-(y / 2)) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbound 2

private theorem sum_mul_exp_le {y : ℝ} (hy : 0 < y) (s : Finset ℕ) :
    ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) ≤ 1 / y ^ 2 := by
  have hr0 : 0 < Real.exp (-y) := Real.exp_pos _
  have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (r := Real.exp (-y)) (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have heq : ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) =
      ∑ v ∈ s, (v : ℝ) * Real.exp (-y) ^ v := by
    refine sum_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [heq]
  exact (sum_le_hasSum s (fun _ _ => by positivity) hsum).trans (exp_div_le hy)

private theorem sum_inv_sq_le (s : Finset ℕ) :
    ∑ k ∈ s, 1 / (k : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum s (fun _ _ => by positivity) hasSum_zeta_two

/-- The number of integer partitions of `n` is at most
`exp (π * sqrt (2 / 3) * sqrt n)`. -/
theorem card_le_exp (n : ℕ) :
    (Fintype.card (Partition n) : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) := by
  let c : ℝ := Real.pi * Real.sqrt ((2 : ℝ) / 3)
  change (Fintype.card (Partition n) : ℝ) ≤ Real.exp (c * Real.sqrt n)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hn'
  have hss : s ^ 2 = n := hs ▸ Real.sq_sqrt hn'.le
  let a : ℝ := c / (2 * s)
  have ha0 : 0 < a := by
    dsimp [a]
    positivity
  rw [← hs]
  have hterm : ∀ v ∈ Icc 1 n, ∀ k ∈ Icc 1 (n / v),
      (v : ℝ) * (Fintype.card (Partition (n - k * v)) : ℝ) ≤
        Real.exp (c * s) * ((v : ℝ) * Real.exp (-(a * k * v))) := by
    intro v hv k hk
    have hv1 : 1 ≤ v := (mem_Icc.mp hv).1
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hkv : k * v ≤ n := (Nat.le_div_iff_mul_le hv1).mp (mem_Icc.mp hk).2
    have hpos : 0 < k * v := Nat.mul_pos hk1 hv1
    have hind := ih (n - k * v) (by omega)
    have hsqrt : Real.sqrt ((n - k * v : ℕ) : ℝ) ≤
        s - (k * v : ℝ) / (2 * s) := by
      rw [Nat.cast_sub hkv, hs]
      push_cast
      exact sqrt_sub_le hn' (by exact_mod_cast hkv)
    have hexp : Real.exp (c * Real.sqrt ((n - k * v : ℕ) : ℝ)) ≤
        Real.exp (c * s) * Real.exp (-(a * k * v)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      calc
        c * Real.sqrt ((n - k * v : ℕ) : ℝ) ≤
            c * (s - (k * v : ℝ) / (2 * s)) := by gcongr
        _ = c * s + -(a * k * v) := by
          dsimp [a]
          ring
    calc
      (v : ℝ) * (Fintype.card (Partition (n - k * v)) : ℝ) ≤
          v * (Real.exp (c * s) * Real.exp (-(a * k * v))) := by
        gcongr
        exact hind.trans hexp
      _ = Real.exp (c * s) * ((v : ℝ) * Real.exp (-(a * k * v))) := by ring
  have hsum : (n : ℝ) * (Fintype.card (Partition n) : ℝ) ≤
      n * Real.exp (c * s) := by
    calc
      (n : ℝ) * (Fintype.card (Partition n) : ℝ) =
          ((n * Fintype.card (Partition n) : ℕ) : ℝ) := by push_cast; ring
      _ = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v),
          (v : ℝ) * (Fintype.card (Partition (n - k * v)) : ℝ) := by
        rw [mul_card_eq_sum]
        push_cast
        rfl
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v),
          Real.exp (c * s) * ((v : ℝ) * Real.exp (-(a * k * v))) :=
        sum_le_sum fun v hv => sum_le_sum (hterm v hv)
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
          Real.exp (c * s) * ((v : ℝ) * Real.exp (-(a * k * v))) :=
        sum_le_sum fun v _ =>
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self _ _))
            fun _ _ _ => by positivity
      _ = Real.exp (c * s) * ∑ k ∈ Icc 1 n, ∑ v ∈ Icc 1 n,
          (v : ℝ) * Real.exp (-(a * k * v)) := by
        rw [sum_comm]
        simp only [mul_sum]
      _ ≤ Real.exp (c * s) * ∑ k ∈ Icc 1 n, 1 / (a * k) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (Real.exp_pos _).le
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
        exact sum_mul_exp_le (by positivity) _
      _ = Real.exp (c * s) * (1 / a ^ 2 * ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2) := by
        congr 1
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by rw [mul_pow, one_div_mul_one_div]
      _ ≤ Real.exp (c * s) * (1 / a ^ 2 * (Real.pi ^ 2 / 6)) := by
        gcongr
        exact sum_inv_sq_le _
      _ = n * Real.exp (c * s) := by
        have hpi := Real.pi_pos
        rw [show a = c / (2 * s) from rfl, div_pow, mul_pow,
          Real.sq_sqrt (by norm_num), show (2 * s) ^ 2 = 4 * s ^ 2 by ring, hss]
        field_simp
        ring
  exact le_of_mul_le_mul_left hsum hn'

end Nat.Partition
