/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedSylvester
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Uniqueness of the Sylvester sequence

A geometric bound for each reciprocal tail forces the next denominator whenever the
remaining sum is a unit fraction. The Sylvester recurrence then propagates this property.
-/

namespace MetaMathlibExt

private theorem reciprocal_tail_le {x : ℕ → ℝ} (hpos : ∀ n, 0 < x n)
    (hmono : Monotone x) (hgrowth : ∀ n, x n ^ 2 ≤ (4 / 3) * x (n + 1))
    (n : ℕ) (hn : 2 ≤ x n) (hs : Summable fun j => 1 / x (n + j)) :
    (∑' j, 1 / x (n + j)) ≤ 1 / (x n - 4 / 3) := by
  let q : ℝ := (4 / 3) / x n
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q < 1 := (div_lt_one (hpos n)).2 (by linarith)
  have hstep (j : ℕ) : 1 / x (n + j + 1) ≤ (1 / x (n + j)) * q := by
    have hj : x n ≤ x (n + j) := hmono (Nat.le_add_right _ _)
    have hp : x (n + j) * x n ≤ (4 / 3) * x (n + j + 1) := by
      calc
        x (n + j) * x n ≤ x (n + j) ^ 2 := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hj (hpos _).le
        _ ≤ _ := hgrowth _
    dsimp [q]
    rw [div_mul_div_comm, div_le_div_iff₀ (hpos _) (mul_pos (hpos _) (hpos _))]
    simpa only [one_mul] using hp
  have hterm (j : ℕ) : 1 / x (n + j) ≤ (1 / x n) * q ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc]
      exact (hstep j).trans (mul_le_mul_of_nonneg_right ih hq₀)
  calc
    (∑' j, 1 / x (n + j)) ≤ ∑' j, (1 / x n) * q ^ j :=
      hs.tsum_le_tsum hterm ((summable_geometric_of_lt_one hq₀ hq₁).mul_left _)
    _ = 1 / (x n - 4 / 3) := by
      have hden : 1 - q = (x n - 4 / 3) / x n := by
        rw [sub_div, div_self (hpos n).ne']
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁, hden, inv_div,
        ← mul_div_assoc, one_div_mul_cancel (hpos n).ne']

/-- **Characterization of the Sylvester sequence.** Let $(a_n)_{n \ge 0}$ be a sequence of
positive integers with $2/3 \le a_n^2 / a_{n+1} \le 4/3$ for all $n$ and $\sum_n 1 / a_n = 1$.
Then $a_n = s_n(1)$ for all $n \ge 0$, where $(s_n(1))_{n \ge 0}$ is the generalized Sylvester
sequence with parameter $1$, that is, the Sylvester sequence $2, 3, 7, 43, \ldots$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 1 (`integers-2026-A28-cor-1`). -/
public theorem eq_sylvester_of_ratio_mem_of_hasSum_one {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, 2 / 3 ≤ (a n : ℝ) ^ 2 / a (n + 1) ∧ (a n : ℝ) ^ 2 / a (n + 1) ≤ 4 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) 1) :
    ∀ n, a n = Nat.generalizedSylvester 1 n := by
  let tail (n : ℕ) : ℝ := ∑' j, 1 / (a (n + j) : ℝ)
  have ha_pos (n : ℕ) : (0 : ℝ) < a n := by exact_mod_cast hpos n
  have htail_summable (n : ℕ) : Summable fun j => 1 / (a (n + j) : ℝ) := by
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).2 hsum.summable
  have htail₀ : tail 0 = 1 := by simpa only [tail, Nat.zero_add] using hsum.tsum_eq
  have hsplit (n : ℕ) : tail n = 1 / (a n : ℝ) + tail (n + 1) := by
    simpa only [tail, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
      (htail_summable n).tsum_eq_zero_add
  have htail_pos (n : ℕ) : 0 < tail n :=
    (htail_summable n).tsum_pos (fun _ => by positivity) 0
      (by simpa only [Nat.add_zero] using one_div_pos.mpr (ha_pos n))
  have hrecip_lt (n : ℕ) : 1 / (a n : ℝ) < tail n := by
    rw [hsplit n]
    linarith [htail_pos (n + 1)]
  have ha₀ : 2 ≤ a 0 := by
    have h := hrecip_lt 0
    rw [htail₀] at h
    have h' := (div_lt_one (ha_pos 0)).1 h
    exact Nat.succ_le_of_lt (by exact_mod_cast h')
  have hgrowth (n : ℕ) : (a n : ℝ) ^ 2 ≤ (4 / 3) * (a (n + 1) : ℝ) :=
    (div_le_iff₀ (ha_pos _)).1 (hratio n).2
  have hstep (n : ℕ) (hn : 2 ≤ a n) : a n ≤ a (n + 1) := by
    have hn' : (2 : ℝ) ≤ a n := by exact_mod_cast hn
    have h : (4 / 3 : ℝ) * a n ≤ (a n : ℝ) * a n :=
      mul_le_mul_of_nonneg_right (by linarith) (ha_pos n).le
    have h' := (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 4 / 3)).1
      (h.trans (by simpa only [pow_two] using hgrowth n))
    exact_mod_cast h'
  have ha_two (n : ℕ) : 2 ≤ a n := by
    induction n with
    | zero => exact ha₀
    | succ n ih => exact ih.trans (hstep n ih)
  have hmono : Monotone a := monotone_nat_of_le_succ fun n => hstep n (ha_two n)
  -- If the tail is `1 / d`, positivity and the geometric bound give `d < a n ≤ d + 4 / 3`.
  have hidentify (n d : ℕ) (hd : 0 < d) (hr : tail n = 1 / (d : ℝ)) : a n = d + 1 := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hlo := hrecip_lt n
    rw [hr, div_lt_div_iff₀ (ha_pos n) hd', one_mul, one_mul] at hlo
    have hlo' : d < a n := by exact_mod_cast hlo
    have hn : (2 : ℝ) ≤ a n := by exact_mod_cast ha_two n
    have hden : (0 : ℝ) < (a n : ℝ) - 4 / 3 := by linarith
    have hle : tail n ≤ 1 / ((a n : ℝ) - 4 / 3) :=
      reciprocal_tail_le ha_pos (fun _ _ hij => Nat.cast_le.mpr (hmono hij)) hgrowth n hn
        (htail_summable n)
    rw [hr, div_le_div_iff₀ hd' hden, one_mul, one_mul] at hle
    have hhi : a n < d + 2 := by
      exact_mod_cast (show (a n : ℝ) < (d : ℝ) + 2 by linarith)
    omega
  -- Track the denominator of the tail, which is one less than the corresponding Sylvester term.
  have hresult (n : ℕ) :
      ∃ d : ℕ, 0 < d ∧ Nat.generalizedSylvester 1 n = d + 1 ∧ tail n = 1 / (d : ℝ) := by
    induction n with
    | zero => exact ⟨1, by decide, rfl, by simpa only [Nat.cast_one, div_one] using htail₀⟩
    | succ n ih =>
      obtain ⟨d, hd, hs, hr⟩ := ih
      have ha := hidentify n d hd hr
      refine ⟨d * (d + 1), Nat.mul_pos hd (Nat.succ_pos _), ?_, ?_⟩
      · rw [Nat.generalizedSylvester_succ, hs, pow_two, Nat.add_mul, one_mul, Nat.add_sub_cancel]
      · have heq := hsplit n
        rw [hr, ha, Nat.cast_add, Nat.cast_one] at heq
        have hd' : (0 : ℝ) < d := by exact_mod_cast hd
        have hd₁ : (0 : ℝ) < (d : ℝ) + 1 := by positivity
        calc
          tail (n + 1) = 1 / (d : ℝ) - 1 / ((d : ℝ) + 1) := by linarith
          _ = 1 / ((d * (d + 1) : ℕ) : ℝ) := by
            push_cast
            field_simp
            ring
  intro n
  obtain ⟨d, hd, hs, hr⟩ := hresult n
  exact (hidentify n d hd hr).trans hs.symm

end MetaMathlibExt
