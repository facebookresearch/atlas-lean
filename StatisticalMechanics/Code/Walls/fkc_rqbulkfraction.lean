/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.FK.QuadrantPartition
import Code.FK.InfiniteVolume

open Filter Topology

open StatMech.FK

namespace StatMech.Walls

variable {d : ℕ}





def fkc_T (m n : ℕ) : ℕ := (2 * n + 1) / (2 * m + 1)


theorem fkc_T_mul_le (m n : ℕ) : fkc_T m n * (2 * m + 1) ≤ 2 * n + 1 :=
  Nat.div_mul_le_self _ _


theorem fkc_lt_T_succ_mul (m n : ℕ) : 2 * n + 1 < (fkc_T m n + 1) * (2 * m + 1) := by
  have hdm := Nat.div_add_mod (2 * n + 1) (2 * m + 1)
  have hmod := Nat.mod_lt (2 * n + 1) (show 0 < 2 * m + 1 by omega)
  rw [fkc_T]; nlinarith [hdm, hmod]




theorem fkc_denom_tendsto_atTop :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
  apply Filter.tendsto_atTop_add_const_right
  exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop




theorem fkc_packing_ratio_tendsto (m : ℕ) :
    Tendsto (fun n => ((fkc_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) atTop (𝓝 1) := by
  have hupper : ∀ n, ((fkc_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1) ≤ 1 := by
    intro n
    have hden : (0 : ℝ) < 2 * n + 1 := by positivity
    rw [div_le_one hden]
    have : (fkc_T m n * (2 * m + 1) : ℕ) ≤ 2 * n + 1 := fkc_T_mul_le m n
    exact_mod_cast this
  have h0 : Tendsto (fun n : ℕ => (2 * (m : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (2 * (m : ℝ) + 1))).div_atTop fkc_denom_tendsto_atTop
  have hlowfun : Tendsto (fun n : ℕ => 1 - (2 * (m : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 1) := by
    have := h0.const_sub (1 : ℝ); simpa using this
  have hlower : ∀ n : ℕ, 1 - (2 * (m : ℝ) + 1) / (2 * n + 1)
      ≤ ((fkc_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1) := by
    intro n
    have hden : (0 : ℝ) < 2 * n + 1 := by positivity
    have hT1 : 2 * n + 1 < (fkc_T m n + 1) * (2 * m + 1) := fkc_lt_T_succ_mul m n
    have hT1R : (2 * (n : ℝ) + 1) < ((fkc_T m n : ℝ) + 1) * (2 * m + 1) := by
      have : ((2 * n + 1 : ℕ) : ℝ) < (((fkc_T m n + 1) * (2 * m + 1) : ℕ) : ℝ) := by
        exact_mod_cast hT1
      push_cast at this ⊢; linarith
    rw [le_div_iff₀ hden, sub_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
    nlinarith [hT1R]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowfun tendsto_const_nhds hlower hupper


theorem fkc_oddEven_ratio_tendsto :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
  have heq : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℝ) + 1) / (2 * n) = 1 + 1 / (2 * n) := by
    intro n hn
    have hden0 : (0 : ℝ) < 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    field_simp
  have hlim : Tendsto (fun n : ℕ => 1 + 1 / (2 * (n : ℝ))) atTop (𝓝 1) := by
    have := h0.const_add (1 : ℝ); simpa using this
  refine (Filter.tendsto_congr' ?_).mpr hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn using (heq n hn)













theorem fkc_bulkFraction_arith_tendsto (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => ((fkc_T m n) ^ d : ℝ)
        * ((d : ℝ) * (2 * m) * (2 * (m : ℝ) + 1) ^ (d - 1))
        / ((d : ℝ) * (2 * n) * (2 * (n : ℝ) + 1) ^ (d - 1))) atTop
      (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
  
  have hprod : Tendsto (fun n => (((fkc_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) ^ d
        * (2 * (m : ℝ) / (2 * m + 1)) * ((2 * (n : ℝ) + 1) / (2 * n))) atTop
      (𝓝 ((1 : ℝ) ^ d * (2 * (m : ℝ) / (2 * m + 1)) * 1)) :=
    (((fkc_packing_ratio_tendsto m).pow d).mul tendsto_const_nhds).mul fkc_oddEven_ratio_tendsto
  rw [one_pow, one_mul, mul_one] at hprod
  refine (Filter.tendsto_congr' ?_).mp hprod
  
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have h2n1 : (0 : ℝ) < 2 * n + 1 := by positivity
  
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [div_pow, mul_pow, pow_succ (2 * (m : ℝ) + 1) e, pow_succ (2 * (n : ℝ) + 1) e]
  have hpowMp : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ e := by positivity
  have hpowNp : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ e := by positivity
  have hepos : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  push_cast
  field_simp











theorem fkc_bulkFraction_tendsto (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n => ((fkc_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
        / ((boxGraph d n).edgeFinset.card : ℝ)) atTop
      (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
  have harith := fkc_bulkFraction_arith_tendsto (d := d) hd m hm
  refine (Filter.tendsto_congr' ?_).mp harith
  
  filter_upwards [Filter.eventually_ge_atTop 0] with n _
  
  have hEm : ((boxGraph d m).edgeFinset.card : ℝ)
      = (d : ℝ) * (2 * m) * (2 * (m : ℝ) + 1) ^ (d - 1) := by
    rw [EdgeCount.boxGraph_edgeCard d m hd]; push_cast; ring
  have hEn : ((boxGraph d n).edgeFinset.card : ℝ)
      = (d : ℝ) * (2 * n) * (2 * (n : ℝ) + 1) ^ (d - 1) := by
    rw [EdgeCount.boxGraph_edgeCard d n hd]; push_cast; ring
  rw [hEm, hEn]

end StatMech.Walls
