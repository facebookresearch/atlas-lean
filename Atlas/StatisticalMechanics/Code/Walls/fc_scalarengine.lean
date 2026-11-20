/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib

open Set Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace StatMech.Walls






















theorem fc_almostMono_converges (a δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hsum : Summable δ)
    (hmono : ∀ n, a n - δ n ≤ a (n + 1)) (hbdd : BddAbove (range a)) :
    ∃ L, Tendsto a atTop (𝓝 L) := by
  
  set S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, δ k with hS
  set c : ℕ → ℝ := fun n => a n + S n with hc
  have hcmono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [hc, hS, Finset.sum_range_succ]
    have := hmono n; linarith
  have hStot : ∀ n, S n ≤ ∑' k, δ k := fun n =>
    Summable.sum_le_tsum (Finset.range n) (fun k _ => hδ k) hsum
  obtain ⟨M, hM⟩ := hbdd
  have hcbdd : BddAbove (range c) := by
    refine ⟨M + ∑' k, δ k, ?_⟩
    rintro x ⟨n, rfl⟩
    have h1 : a n ≤ M := hM ⟨n, rfl⟩
    have h2 := hStot n
    simp only [hc]; linarith
  
  have hctends : Tendsto c atTop (𝓝 (⨆ i, c i)) := tendsto_atTop_ciSup hcmono hcbdd
  have hStends : Tendsto S atTop (𝓝 (∑' k, δ k)) := hsum.hasSum.tendsto_sum_nat
  have heq : a = fun n => c n - S n := by funext n; simp [hc]
  refine ⟨(⨆ i, c i) - ∑' k, δ k, ?_⟩
  rw [heq]; exact hctends.sub hStends




theorem fc_almostMono_converges_subadditive (a : ℕ → ℝ)
    (hmono : ∀ n, a n ≤ a (n + 1)) (hbdd : BddAbove (range a)) :
    ∃ L, Tendsto a atTop (𝓝 L) :=
  fc_almostMono_converges a (fun _ => 0) (fun _ => le_refl 0) summable_zero
    (fun n => by simpa using hmono n) hbdd








theorem fc_natLog_tendsto_atTop : Tendsto (fun n => Nat.log 2 n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨2 ^ k, fun n hn => ?_⟩
  calc k = Nat.log 2 (2 ^ k) := (Nat.log_pow (by norm_num) k).symm
    _ ≤ Nat.log 2 n := Nat.log_mono_right hn

















theorem fc_full_from_dyadic (a : ℕ → ℝ) (L : ℝ)
    (hdy : Tendsto (fun j => a (2 ^ j)) atTop (𝓝 L))
    (osc : ℕ → ℝ) (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, 1 ≤ n → |a n - a (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) :
    Tendsto a atTop (𝓝 L) := by
  have hcomp : Tendsto (fun n => a (2 ^ (Nat.log 2 n))) atTop (𝓝 L) :=
    hdy.comp fc_natLog_tendsto_atTop
  have hosc' : Tendsto (fun n => osc (Nat.log 2 n)) atTop (𝓝 0) :=
    hosc.comp fc_natLog_tendsto_atTop
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hcomp) (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hosc') (ε / 2) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hd1 : dist (a (2 ^ (Nat.log 2 n))) L < ε / 2 := hN1 n hnN1
  have hd2 : dist (osc (Nat.log 2 n)) 0 < ε / 2 := hN2 n hnN2
  have hsd : |a n - a (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n) := hsand n hn1
  have hoscnn : 0 ≤ osc (Nat.log 2 n) := le_trans (abs_nonneg _) hsd
  rw [Real.dist_eq] at hd1 hd2 ⊢
  rw [sub_zero, abs_of_nonneg hoscnn] at hd2
  calc |a n - L| = |(a n - a (2 ^ (Nat.log 2 n))) + (a (2 ^ (Nat.log 2 n)) - L)| := by ring_nf
    _ ≤ |a n - a (2 ^ (Nat.log 2 n))| + |a (2 ^ (Nat.log 2 n)) - L| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · exact le_trans hsd (le_of_lt hd2)
        · exact hd1
    _ = ε := by ring

















theorem fc_scalar_converges (g δ osc : ℕ → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hdymono : ∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1)))
    (hbdd : BddAbove (range (fun j => g (2 ^ j))))
    (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) :
    ∃ L, Tendsto g atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := fc_almostMono_converges (fun j => g (2 ^ j)) δ hδ hsum
    (fun j => by simpa using hdymono j) hbdd
  exact ⟨L, fc_full_from_dyadic g L hL osc hosc hsand⟩












theorem fc_scalar_converges_satisfiable :
    ∃ (g δ osc : ℕ → ℝ),
      (∀ j, 0 ≤ δ j)
      ∧ Summable δ
      ∧ (∀ j, g (2 ^ j) - δ j ≤ g (2 ^ (j + 1)))
      ∧ BddAbove (range (fun j => g (2 ^ j)))
      ∧ Tendsto osc atTop (𝓝 0)
      ∧ (∀ n, 1 ≤ n → |g n - g (2 ^ (Nat.log 2 n))| ≤ osc (Nat.log 2 n)) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => le_refl 0, summable_zero, ?_, ?_,
    tendsto_const_nhds, ?_⟩
  · intro j; simp
  · exact ⟨0, by rintro x ⟨n, rfl⟩; simp⟩
  · intro n _; simp

end StatMech.Walls
