/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.Percolation.Sharpness
import Code.Percolation.TildePc

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace StatMech

namespace TwoDim

open StatMech.Percolation StatMech.Lattice















theorem theta_half_eq_zero (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
    theta 2 (1 / 2) h12 = 0 := by
  by_contra hne
  have hpos : 0 < theta 2 (1 / 2) h12 :=
    lt_of_le_of_ne (theta_nonneg 2 (1 / 2) h12) (Ne.symm hne)
  have hto1 : Tendsto (cross (1 / 2)) atTop (𝓝 1) := hpercToOne hpos
  
  have hconst : Tendsto (cross (1 / 2)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have : cross (1 / 2) = fun _ : ℕ => (1 / 2 : ℝ) := funext hdualHalf
    rw [this]; exact tendsto_const_nhds
  have : (1 / 2 : ℝ) = 1 := tendsto_nhds_unique hconst hto1
  norm_num at this



theorem half_mem_subcriticalSet (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
    (1 / 2 : ℝ≥0) ∈ subcriticalSet 2 :=
  ⟨h12, theta_half_eq_zero h12 cross hdualHalf hpercToOne⟩





theorem half_le_pc (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
    (1 / 2 : ℝ≥0) ≤ pc 2 :=
  le_pc_of_mem_subcriticalSet (half_mem_subcriticalSet h12 cross hdualHalf hpercToOne)

























theorem pc_le_half
    (hsharp : tildePc 2 = pc 2)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 ≤ (1 / 2 : ℝ≥0) := by
  
  rw [← hsharp]
  
  refine csSup_le_iff' ?_ |>.mpr ?_
  · 
    exact ⟨1, fun _ hp => (mem_tildePcSet.mp hp).1⟩
  · intro p hp
    by_contra hlt
    rw [not_le] at hlt
    
    obtain ⟨hp1, -⟩ := mem_tildePcSet.mp hp
    
    have hto0 : Tendsto (cross p) atTop (𝓝 0) := hdecayToZero p hp1 (hsub p hp hp1)
    
    have hge : ∀ n, (1 / 2 : ℝ) ≤ cross p n := fun n => by
      have := hmono n (1 / 2) p (le_of_lt hlt)
      rwa [hdualHalf n] at this
    
    have hlimge : (1 / 2 : ℝ) ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hto0
        (Filter.Eventually.of_forall hge)
    norm_num at hlimge


















theorem pc_eq_half (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (hsharp : tildePc 2 = pc 2)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1))
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 = (1 / 2 : ℝ≥0) :=
  le_antisymm
    (pc_le_half hsharp cross hsub hmono hdualHalf hdecayToZero)
    (half_le_pc h12 cross hdualHalf hpercToOne)

end TwoDim

end StatMech
