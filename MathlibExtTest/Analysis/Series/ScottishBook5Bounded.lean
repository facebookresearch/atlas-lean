/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.ScottishBook5Bounded
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field

/-! # Tests for the bounded Scottish Book Problem 5

The same witness sums a sequence with arbitrarily late unit spikes to zero, but not to one.
The strictly increasing sequence `n + Nat.sqrt n` indexes its zero terms and has density one.
-/

namespace MathlibExtTest.Analysis.Series.ScottishBook5Bounded

open Filter
open MathlibExt.Analysis.Series.ScottishBook5BoundedWanted
open scoped Topology

private def s (n : ℕ) : ℕ := n + n.sqrt

private lemma s_strictMono : StrictMono s := fun _ _ h ↦
  Nat.add_lt_add_of_lt_of_le h (Nat.sqrt_le_sqrt h.le)

private lemma s_hasDensityOne : HasDensityOne s := by
  refine ⟨s_strictMono, ?_⟩
  have hsqrt : Tendsto (fun n : ℕ ↦ ((n.sqrt : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop.2 fun a ↦
      (eventually_ge_atTop (a * a)).mono fun _ hn ↦ Nat.le_sqrt.2 hn
  have hr : Tendsto (fun n : ℕ ↦ (n.sqrt : ℝ) / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hsqrt.const_div_atTop 1)
      (Eventually.of_forall fun _ ↦ by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < n.sqrt := by exact_mod_cast Nat.le_sqrt.2 hn
    have hpos' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : (n.sqrt : ℝ) * n.sqrt ≤ n := by exact_mod_cast Nat.sqrt_le n
    exact (div_le_div_iff₀ hpos' hpos).2 (by simpa only [one_mul] using hsq)
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).add (hr.comp (tendsto_add_atTop_nat 1))
  refine (by simpa only [add_zero, Function.comp_apply] using hlim : Tendsto (fun n : ℕ ↦
    1 + (((n + 1).sqrt : ℕ) : ℝ) / (↑(n + 1) : ℝ)) atTop (𝓝 1)).congr ?_
  intro n
  simp only [s, Nat.cast_add, Nat.cast_one]
  rw [add_div, div_self (by positivity : (n : ℝ) + 1 ≠ 0)]

private noncomputable def spikes (k : ℕ) : ℝ := by
  classical
  exact if k ∈ Set.range s then 0 else 1

private lemma arbitrarilyLateSpikes (N : ℕ) : ∃ k ≥ N, spikes k = 1 := by
  let m := N + 1
  let k := m * m + N
  have hm : N ≤ m * m := by dsimp [m]; nlinarith
  have hk : k ∉ Set.range s := by
    rintro ⟨j, hj⟩
    by_cases h : j < m * m
    · have hroot : j.sqrt < m := Nat.sqrt_lt.2 h
      unfold s at hj
      omega
    · have hroot : m ≤ j.sqrt := Nat.le_sqrt.2 (Nat.le_of_not_gt h)
      unfold s at hj
      omega
  exact ⟨k, by omega, by simp [spikes, hk]⟩

example : ¬ Tendsto spikes atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually_lt_const (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨k, hk, hspike⟩ := arbitrarilyLateSpikes N
  exact (lt_irrefl (1 : ℝ)) (hspike ▸ hN k hk)

example : ∃ a, IsPermanent a ∧ MatrixSums a spikes 0 ∧ ¬ MatrixSums a spikes 1 := by
  have hB : IsBounded spikes := by
    refine ⟨1, fun k ↦ ?_⟩
    by_cases hk : k ∈ Set.range s <;> simp [spikes, hk]
  have hsub : AsymptoticallyConvergent spikes 0 := by
    refine ⟨s, s_hasDensityOne, tendsto_const_nhds.congr fun n ↦ ?_⟩
    simp [spikes]
  obtain ⟨a, hperm, hiff⟩ := scottishBookProblem5Claim
  have hzero := (hiff spikes hB 0).2 hsub
  exact ⟨a, hperm, hzero, fun hone ↦ zero_ne_one (tendsto_nhds_unique hzero.2 hone.2)⟩

/--
info: 'MathlibExt.Analysis.Series.ScottishBook5BoundedWanted.scottishBookProblem5Claim'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scottishBookProblem5Claim

end MathlibExtTest.Analysis.Series.ScottishBook5Bounded
