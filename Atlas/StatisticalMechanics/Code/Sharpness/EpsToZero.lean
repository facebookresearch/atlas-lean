/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Sharpness.GHSUnconditional
import Code.Sharpness.Simon

open scoped BigOperators
open Filter Topology Finset SimpleGraph

namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]











theorem set_susceptibility_sum_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x)
          - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) := by
  refine Finset.sum_nonneg (fun x _ => ?_)
  by_cases hxo : x = o
  · subst hxo
    have hsq : (fun s => spin s x * spin s x) = (fun _ : ConfigSpace V => (1 : ℝ)) := by
      funext s; exact spin_sq s x
    rw [hsq]
    have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
      unfold isingExpectation
      simp [isingProb_sum_eq_one G β h]
    rw [hone]
    have hb := expectation_spin_bounds G β h hβ hh x
    nlinarith [hb.1, hb.2]
  · have := cov_nonneg G β h hβ hh o x (Ne.symm hxo)
    linarith








theorem ghs_susceptibility_sum_bound (β h : ℝ) (hβ : 0 < β) (hh : 0 < h) (o : V)
    :
    ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x)
          - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x))
        ≤ 1 / (β * h) := by
  
  have hderiv := deriv_magnetization_eq_sum_cov G β h o
  have hghs := (ghs_susceptibility_unconditional G β h hβ.le hh o).2
  rw [hderiv] at hghs
  
  set S := ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x)
        - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) with hS
  have hSle : S ≤ (1 / h) / β := by
    rw [le_div_iff₀ hβ, mul_comm]; exact hghs
  have heq : (1 / h) / β = 1 / (β * h) := by
    rw [div_div, mul_comm]
  rw [heq] at hSle
  exact hSle











theorem eps_annular_bound_of_mono {M : ℕ → ℝ} (hMono : Monotone M) {h : ℝ} (hh : 0 < h)
    (n k : ℕ) (_hk : k ≤ n) :
    0 ≤ (1 / h) * (M n - M (n - k)) := by
  have hle : M (n - k) ≤ M n := hMono (Nat.sub_le n k)
  have : 0 ≤ M n - M (n - k) := by linarith
  positivity


















theorem set_annularDiff_tendsto_zero (M : ℕ → ℝ) {L : ℝ} (hM : Tendsto M atTop (𝓝 L))
    (k : ℕ) :
    Tendsto (fun n : ℕ => M n - M (n - k)) atTop (𝓝 0) := by
  have hsub : Tendsto (fun n : ℕ => n - k) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + k, fun n hn => by omega⟩)
  have hMk : Tendsto (fun n : ℕ => M (n - k)) atTop (𝓝 L) := hM.comp hsub
  have hdiff : Tendsto (fun n : ℕ => M n - M (n - k)) atTop (𝓝 (L - L)) := hM.sub hMk
  rwa [sub_self] at hdiff


















theorem set_eps_to_zero (ε tail M : ℕ → ℝ) {L h : ℝ} (_hh : 0 < h)
    (hpos : ∀ n, 0 ≤ ε n)
    (hsplit : ∀ k n, k ≤ n → ε n ≤ tail k + (1 / h) * (M n - M (n - k)))
    (htail : Tendsto tail atTop (𝓝 0))
    (hM : Tendsto M atTop (𝓝 L)) :
    Tendsto ε atTop (𝓝 0) := by
  
  rw [Metric.tendsto_atTop]
  intro δ hδ
  
  have hhalf : 0 < δ / 2 := by linarith
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨K, hK⟩ := htail (δ / 2) hhalf
  have htailK : tail K < δ / 2 := by
    have := hK K le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact (abs_lt.mp this).2
  
  have hann : Tendsto (fun n : ℕ => (1 / h) * (M n - M (n - K))) atTop (𝓝 0) := by
    have := (set_annularDiff_tendsto_zero M hM K).const_mul (1 / h)
    simpa using this
  rw [Metric.tendsto_atTop] at hann
  obtain ⟨N₀, hN₀⟩ := hann (δ / 2) hhalf
  
  refine ⟨max K N₀, fun n hn => ?_⟩
  have hnK : K ≤ n := le_trans (le_max_left K N₀) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_right K N₀) hn
  have hannlt : (1 / h) * (M n - M (n - K)) < δ / 2 := by
    have := hN₀ n hnN₀
    rw [Real.dist_eq, sub_zero] at this
    exact (abs_lt.mp this).2
  have hub : ε n ≤ tail K + (1 / h) * (M n - M (n - K)) := hsplit K n hnK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos n)]
  calc ε n ≤ tail K + (1 / h) * (M n - M (n - K)) := hub
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end Sharpness

end StatMech
