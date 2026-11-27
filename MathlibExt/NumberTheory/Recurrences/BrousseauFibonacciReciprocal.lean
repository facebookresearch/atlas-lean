/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

private theorem cassini_int (n : ℕ) (hn : 0 < n) :
    ((Nat.fib (n - 1) : ℤ) * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) ^ 2) = (-1 : ℤ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ n hn ih =>
    have h1 : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have h2 : Nat.fib (n + 1 + 1 + 1) = Nat.fib (n + 1) + Nat.fib (n + 1 + 1) := Nat.fib_add_two
    have hn1 : (n + 1) - 1 = n := by omega
    rw [hn1]
    push_cast [h1, h2]
    have hfib : (Nat.fib (n - 1) : ℤ) = (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) := by
      have h := Nat.fib_add_one (n := n) (by omega : n ≠ 0)
      have : (Nat.fib (n + 1) : ℤ) = (Nat.fib (n - 1) : ℤ) + (Nat.fib n : ℤ) := by
        exact_mod_cast h
      omega
    have ih' : (Nat.fib (n - 1) : ℤ) * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) ^ 2 = (-1 : ℤ) ^ n := ih
    rw [hfib] at ih'
    ring_nf at ih' ⊢
    linear_combination -ih'

private theorem key_identity (K q : ℕ) (hK : 0 < K) (hq : 0 < q) :
    ((Nat.fib (K + q) : ℤ) ^ 2 - (Nat.fib q : ℤ) * (Nat.fib (2 * K + q) : ℤ))
      = (-1 : ℤ) ^ q * (Nat.fib K : ℤ) ^ 2 := by
  have hqm : q - 1 + 1 = q := by omega
  have e1 : Nat.fib (K + q) = Nat.fib K * Nat.fib (q - 1) + Nat.fib (K + 1) * Nat.fib q := by
    have h := Nat.fib_add (m := K) (n := q - 1)
    have hqq : K + (q - 1) + 1 = K + q := by omega
    rw [hqq, hqm] at h
    exact h
  have e2 : Nat.fib (K + q + 1) = Nat.fib K * Nat.fib q + Nat.fib (K + 1) * Nat.fib (q + 1) := by
    have h := Nat.fib_add (m := K) (n := q)
    exact h
  have e3 : Nat.fib (2 * K + q) = Nat.fib (K - 1) * Nat.fib (K + q) + Nat.fib K * Nat.fib (K + q + 1) := by
    have h := Nat.fib_add (m := K - 1) (n := K + q)
    have hKK : (K - 1) + (K + q) + 1 = 2 * K + q := by omega
    have hKm : K - 1 + 1 = K := by omega
    rw [hKK, hKm] at h
    exact h
  have e4 : Nat.fib (K + 1) = Nat.fib (K - 1) + Nat.fib K := Nat.fib_add_one (by omega : K ≠ 0)
  have e5 : Nat.fib (q + 1) = Nat.fib (q - 1) + Nat.fib q := Nat.fib_add_one (by omega : q ≠ 0)
  have hc := cassini_int q hq
  have e1z : (Nat.fib (K + q) : ℤ) = (Nat.fib K : ℤ) * (Nat.fib (q - 1) : ℤ) + (Nat.fib (K + 1) : ℤ) * (Nat.fib q : ℤ) := by exact_mod_cast e1
  have e2z : (Nat.fib (K + q + 1) : ℤ) = (Nat.fib K : ℤ) * (Nat.fib q : ℤ) + (Nat.fib (K + 1) : ℤ) * (Nat.fib (q + 1) : ℤ) := by exact_mod_cast e2
  have e3z : (Nat.fib (2 * K + q) : ℤ) = (Nat.fib (K - 1) : ℤ) * (Nat.fib (K + q) : ℤ) + (Nat.fib K : ℤ) * (Nat.fib (K + q + 1) : ℤ) := by exact_mod_cast e3
  have e4z : (Nat.fib (K + 1) : ℤ) = (Nat.fib (K - 1) : ℤ) + (Nat.fib K : ℤ) := by exact_mod_cast e4
  have e5z : (Nat.fib (q + 1) : ℤ) = (Nat.fib (q - 1) : ℤ) + (Nat.fib q : ℤ) := by exact_mod_cast e5
  have hgf : (Nat.fib (K + q) : ℤ) - (Nat.fib q : ℤ) * (Nat.fib (K - 1) : ℤ)
      = (Nat.fib K : ℤ) * (Nat.fib (q + 1) : ℤ) := by
    linear_combination e1z + (Nat.fib q : ℤ) * e4z - (Nat.fib K : ℤ) * e5z
  have hmain1 : (Nat.fib (K + q) : ℤ) ^ 2 - (Nat.fib q : ℤ) * (Nat.fib (2 * K + q) : ℤ)
      = (Nat.fib K : ℤ) * ((Nat.fib (K + q) : ℤ) * (Nat.fib (q + 1) : ℤ) - (Nat.fib q : ℤ) * (Nat.fib (K + q + 1) : ℤ)) := by
    linear_combination (Nat.fib (K + q) : ℤ) * hgf - (Nat.fib q : ℤ) * e3z
  have hmain2 : (Nat.fib (K + q) : ℤ) * (Nat.fib (q + 1) : ℤ) - (Nat.fib q : ℤ) * (Nat.fib (K + q + 1) : ℤ)
      = (Nat.fib K : ℤ) * ((Nat.fib (q - 1) : ℤ) * (Nat.fib (q + 1) : ℤ) - (Nat.fib q : ℤ) ^ 2) := by
    linear_combination (Nat.fib (q + 1) : ℤ) * e1z - (Nat.fib q : ℤ) * e2z
  linear_combination hmain1 + (Nat.fib K : ℤ) * hmain2 + (Nat.fib K : ℤ) ^ 2 * hc

private theorem pow_le_fib_pair (m : ℕ) : 2 ^ m ≤ Nat.fib (2 * m + 1) ∧ 2 ^ m ≤ Nat.fib (2 * m + 2) := by
  induction m with
  | zero => constructor <;> simp
  | succ m ih =>
    obtain ⟨hodd, heven⟩ := ih
    have h1 : Nat.fib (2 * m + 1 + 2) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 1 + 1) :=
      Nat.fib_add_two
    have h1a : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by omega
    have h1b : 2 * m + 1 + 1 = 2 * m + 2 := by omega
    have h2 : Nat.fib (2 * m + 2 + 2) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 2 + 1) :=
      Nat.fib_add_two
    have h2a : 2 * (m + 1) + 2 = 2 * m + 2 + 2 := by omega
    have h2b : 2 * m + 2 + 1 = 2 * (m + 1) + 1 := by omega
    have h3 : 2 ^ (m + 1) ≤ Nat.fib (2 * (m + 1) + 1) := by
      rw [h1a, h1, h1b, pow_succ]
      omega
    constructor
    · rw [h1a, h1, h1b, pow_succ]
      omega
    · rw [h2a, h2, h2b]
      omega

private theorem inv_fib_sq_le (k : ℕ) :
    (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2 ≤ 2 * (1 / 2) ^ k := by
  have hpos : (0 : ℝ) < (Nat.fib (k + 1) : ℝ) := by
    have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast this
  rcases Nat.even_or_odd k with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hm2 : k = 2 * m := by omega
    have hle : (2 : ℝ) ^ m ≤ (Nat.fib (k + 1) : ℝ) := by
      have hnat : 2 ^ m ≤ Nat.fib (2 * m + 1) := (pow_le_fib_pair m).1
      have heq : 2 * m + 1 = k + 1 := by omega
      rw [heq] at hnat
      exact_mod_cast hnat
    have hsq : ((2 : ℝ) ^ m) ^ 2 ≤ (Nat.fib (k + 1) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    have h1 : (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2 ≤ 1 / ((2 : ℝ) ^ m) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity) hsq
    have h2 : (1 : ℝ) / ((2 : ℝ) ^ m) ^ 2 = (1 / 2) ^ (2 * m) := by
      rw [div_pow, one_pow, ← pow_mul]
      congr 1
      ring
    have h3 : (1 / 2 : ℝ) ^ (2 * m) ≤ 2 * (1 / 2) ^ k := by
      rw [hm2]
      have : (0 : ℝ) ≤ (1 / 2) ^ (2 * m) := by positivity
      linarith
    calc (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2
        ≤ 1 / ((2 : ℝ) ^ m) ^ 2 := h1
      _ = (1 / 2) ^ (2 * m) := h2
      _ ≤ 2 * (1 / 2) ^ k := h3
  · obtain ⟨m, hm⟩ := hodd
    have hm2 : k = 2 * m + 1 := by omega
    have hle : (2 : ℝ) ^ m ≤ (Nat.fib (k + 1) : ℝ) := by
      have hnat : 2 ^ m ≤ Nat.fib (2 * m + 2) := (pow_le_fib_pair m).2
      have heq : 2 * m + 2 = k + 1 := by omega
      rw [heq] at hnat
      exact_mod_cast hnat
    have hsq : ((2 : ℝ) ^ m) ^ 2 ≤ (Nat.fib (k + 1) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    have h1 : (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2 ≤ 1 / ((2 : ℝ) ^ m) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity) hsq
    have heven : (1 : ℝ) / ((2 : ℝ) ^ m) ^ 2 = (1 / 2) ^ (2 * m) := by
      rw [div_pow, one_pow, ← pow_mul]
      congr 1
      ring
    have h2 : (1 : ℝ) / ((2 : ℝ) ^ m) ^ 2 = 2 * (1 / 2) ^ k := by
      rw [heven, hm2, pow_succ (1 / 2 : ℝ) (2 * m)]
      ring
    calc (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2
        ≤ 1 / ((2 : ℝ) ^ m) ^ 2 := h1
      _ = 2 * (1 / 2) ^ k := h2

private theorem term_eq (q k : ℕ) (hq : 0 < q) :
    ((-1 : ℝ) ^ k * Nat.fib (2 * (k + 1) + q)) /
      ((Nat.fib (k + 1) : ℝ) ^ 2 * (Nat.fib (k + 1 + q) : ℝ) ^ 2)
    = (Nat.fib q : ℝ)⁻¹ *
      (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2) -
       ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + 1 + q) : ℝ) ^ 2)) := by
  have hK : 0 < k + 1 := by omega
  have hF1 : (Nat.fib (k + 1) : ℝ) ≠ 0 := by
    have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast ne_of_gt this
  have hF2 : (Nat.fib (k + 1 + q) : ℝ) ≠ 0 := by
    have : 0 < Nat.fib (k + 1 + q) := Nat.fib_pos.mpr (by omega)
    exact_mod_cast ne_of_gt this
  have hFq : (Nat.fib q : ℝ) ≠ 0 := by
    have : 0 < Nat.fib q := Nat.fib_pos.mpr hq
    exact_mod_cast ne_of_gt this
  have hkey := key_identity (k + 1) q hK hq
  have hkeyR : (Nat.fib (k + 1 + q) : ℝ) ^ 2 - (Nat.fib q : ℝ) * (Nat.fib (2 * (k + 1) + q) : ℝ)
      = (-1 : ℝ) ^ q * (Nat.fib (k + 1) : ℝ) ^ 2 := by
    have h1 : (k + 1) + q = k + 1 + q := rfl
    rw [h1] at hkey
    exact_mod_cast hkey
  have hpow : (-1 : ℝ) ^ (k + q) = (-1 : ℝ) ^ k * (-1 : ℝ) ^ q := pow_add _ _ _
  field_simp
  rw [hpow]
  linear_combination -(-1 : ℝ) ^ k * hkeyR

private theorem summable_inv_fib_sq :
    Summable (fun k : ℕ => (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2) := by
  apply Summable.of_nonneg_of_le (f := fun k : ℕ => 2 * (1 / 2) ^ k)
  · intro b
    positivity
  · intro b
    exact inv_fib_sq_le b
  · exact summable_geometric_two.mul_left 2

private theorem summable_d : Summable (fun k : ℕ => (-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2) := by
  apply Summable.of_norm
  have hcongr : (fun k : ℕ => ‖(-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2‖)
      = (fun k : ℕ => (1 : ℝ) / (Nat.fib (k + 1) : ℝ) ^ 2) := by
    funext k
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
    rw [norm_pow]
    have hpos : (0 : ℝ) ≤ (Nat.fib (k + 1) : ℝ) := by
      have : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
      exact_mod_cast le_of_lt this
    rw [Real.norm_of_nonneg hpos]
    rw [inv_eq_one_div]
  rw [hcongr]
  exact summable_inv_fib_sq

private theorem tendsto_d_zero : Filter.Tendsto (fun k : ℕ => (-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun k : ℕ => 2 * (1 / 2) ^ k)
  · intro n
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    have hpos : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by
      have : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
      exact_mod_cast this
    rw [Real.norm_of_nonneg (le_of_lt (pow_pos hpos 2))]
    have h := inv_fib_sq_le n
    rwa [one_div] at h ⊢
  · have hlim : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have : Filter.Tendsto (fun k : ℕ => 2 * (1 / 2 : ℝ) ^ k) Filter.atTop (nhds (2 * 0)) :=
      hlim.const_mul 2
    rwa [mul_zero] at this

private theorem partial_telescope (d : ℕ → ℝ) (q N : ℕ) :
    ∑ k ∈ Finset.range N, (d k - d (k + q))
    = ∑ k ∈ Finset.range q, d k - ∑ k ∈ Finset.range q, d (N + k) := by
  have h1 : ∑ k ∈ Finset.range N, (d k - d (k + q))
      = ∑ k ∈ Finset.range N, d k - ∑ k ∈ Finset.range N, d (k + q) := Finset.sum_sub_distrib _ _
  have hshift : ∑ k ∈ Finset.range N, d (k + q) = ∑ k ∈ Finset.range N, d (q + k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [add_comm k q]
  have h := Finset.sum_range_add d q N
  have h3 := Finset.sum_range_add d N q
  have h4 : q + N = N + q := by omega
  rw [h1, hshift]
  rw [h4] at h
  linear_combination h - h3

private theorem hasSum_telescope (q : ℕ) :
    HasSum (fun k : ℕ => ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
      - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2))
    (∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)) := by
  have hshift : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2) := by
    have h2 : (fun k : ℕ => (-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2)
        = (fun k : ℕ => (fun j : ℕ => (-1 : ℝ) ^ j / (Nat.fib (j + 1) : ℝ) ^ 2) (k + q)) :=
      rfl
    rw [h2]
    exact (summable_nat_add_iff q).mpr summable_d
  have hsum : Summable (fun k : ℕ => ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
      - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2)) :=
    summable_d.sub hshift
  rw [Summable.hasSum_iff_tendsto_nat hsum]
  have htail : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range q, ((-1 : ℝ) ^ (N + k) / (Nat.fib (N + k + 1) : ℝ) ^ 2)) Filter.atTop (nhds 0) := by
    have h0 : (∑ k ∈ Finset.range q, (0 : ℝ)) = 0 := by simp
    rw [← h0]
    apply tendsto_finsetSum
    intro j _
    have hcomp : (fun N : ℕ => (-1 : ℝ) ^ (N + j) / (Nat.fib (N + j + 1) : ℝ) ^ 2)
        = (fun k : ℕ => (-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2) ∘ (fun N : ℕ => N + j) := rfl
    rw [hcomp]
    exact tendsto_d_zero.comp (Filter.tendsto_add_atTop_nat j)
  have hlim : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
      - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2))) Filter.atTop
      (nhds (∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2))) := by
    have htel : (fun N : ℕ => ∑ k ∈ Finset.range N, (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
        - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2)))
        = (fun N : ℕ => ∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
          - ∑ k ∈ Finset.range q, ((-1 : ℝ) ^ (N + k) / (Nat.fib (N + k + 1) : ℝ) ^ 2)) := by
      funext N
      have hpt := partial_telescope (fun k : ℕ => (-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2) q N
      have heq : (∑ k ∈ Finset.range N, (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
          - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2)))
          = ∑ k ∈ Finset.range N, ((fun j : ℕ => (-1 : ℝ) ^ j / (Nat.fib (j + 1) : ℝ) ^ 2) k
            - (fun j : ℕ => (-1 : ℝ) ^ j / (Nat.fib (j + 1) : ℝ) ^ 2) (k + q)) :=
        rfl
      rw [heq, hpt]
    rw [htel]
    have hconst : Filter.Tendsto (fun _ : ℕ => ∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)) Filter.atTop
        (nhds (∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2))) :=
      tendsto_const_nhds
    have hsub := hconst.sub htail
    simp only [sub_zero] at hsub
    exact hsub
  exact hlim

private theorem icc_eq_range (q : ℕ) :
    ∑ k ∈ Finset.Icc 1 q, ((-1 : ℝ) ^ (k - 1)) / (Nat.fib k : ℝ) ^ 2
    = ∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1), ih, Finset.sum_range_succ]
    have h1 : q + 1 - 1 = q := by omega
    rw [h1]

/-- **Brousseau's alternating series of reciprocal Fibonacci squares.** Let $F_n$ denote the
Fibonacci numbers, with $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. For every positive
integer $q$, the real series
$\sum_{k \ge 1} (-1)^{k-1} \frac{F_{2k+q}}{F_k^2 \, F_{k+q}^2}$ is unconditionally summable,
with sum $\frac{1}{F_q} \sum_{k=1}^{q} \frac{(-1)^{k-1}}{F_k^2}$.

Adegoke's generalization has a further integer parameter $n$ and assumes that $q$ is even or
$nq$ is odd; this is its case $n = 1$, in which that assumption holds for every positive $q$.

Proves `Wanted` entry `brousseau_fibonacci_reciprocal_sum`.

Source: Kunle Adegoke, "Generalizations of the Reciprocal Fibonacci-Lucas Sums of
Brousseau," Journal of Integer Sequences 21 (2018),
`https://cs.uwaterloo.ca/journals/JIS/VOL21/Adegoke/ade3.tex`, live and bundled
source-file SHA-256 `8feb3648f4ab8f2da4d383821f763b4b57316a8f46343082a2c0d7682912f5d7`;
controlling theorem, equation, and specialization at lines 1135–1148 with exact-span
SHA-256 under LF joining without a terminal LF
`360a38704aab45f8e89f64fb8ffc5f865c5da5316796e5ec28c650318b343dd1`; original reference:
Brother Alfred Brousseau, "Fibonacci-Lucas Infinite Series — Research Topic,"
Fibonacci Quarterly 7 (1969), 211–217, Formula (6), cited at source line 1414; task id:
`jis_grounded_50e651872ff01364d67794b1__brousseau_fibonacci_reciprocal_sum`.
-/
theorem brousseau_fibonacci_reciprocal_sum (q : ℕ) (hq : 0 < q) :
    HasSum
      (fun k : ℕ =>
        ((-1 : ℝ) ^ k * Nat.fib (2 * (k + 1) + q)) /
          ((Nat.fib (k + 1) : ℝ) ^ 2 * (Nat.fib (k + 1 + q) : ℝ) ^ 2))
      ((Nat.fib q : ℝ)⁻¹ *
        ∑ k ∈ Finset.Icc 1 q, ((-1 : ℝ) ^ (k - 1)) / (Nat.fib k : ℝ) ^ 2) := by
  have htel := hasSum_telescope q
  have htel2 : HasSum (fun k : ℕ => ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
      - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + 1 + q) : ℝ) ^ 2))
      (∑ k ∈ Finset.range q, ((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)) := by
    apply htel.congr_fun
    intro k
    have heq : k + q + 1 = k + 1 + q := by omega
    rw [heq]
  have hmul := htel2.mul_left (Nat.fib q : ℝ)⁻¹
  have hcongr : (fun k : ℕ =>
      ((-1 : ℝ) ^ k * Nat.fib (2 * (k + 1) + q)) /
        ((Nat.fib (k + 1) : ℝ) ^ 2 * (Nat.fib (k + 1 + q) : ℝ) ^ 2))
      = (fun k : ℕ => (Nat.fib q : ℝ)⁻¹ *
        (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
          - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + 1 + q) : ℝ) ^ 2))) := by
    funext k
    exact term_eq q k hq
  rw [hcongr]
  have hcongr2 : (fun k : ℕ => (Nat.fib q : ℝ)⁻¹ *
      (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
        - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2)))
      = (fun k : ℕ => (Nat.fib q : ℝ)⁻¹ *
        (((-1 : ℝ) ^ k / (Nat.fib (k + 1) : ℝ) ^ 2)
          - ((-1 : ℝ) ^ (k + q) / (Nat.fib (k + q + 1) : ℝ) ^ 2))) := rfl
  -- transform hmul to match, then rewrite Icc sum
  have hfinal := hmul.congr_fun (fun k => rfl)
  rw [icc_eq_range] at *
  -- hmul : HasSum (scaled diff) ((Fq)⁻¹ * ∑_{range} ...)
  -- goal after rw hcongr : HasSum (scaled diff) ((Fq)⁻¹ * ∑_{range} ...)
  exact hfinal

end

end MetaMathlibExt
