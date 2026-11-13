/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.SolowSteadyState
import Mathlib.Tactic.NormNum
import Mathlib.Logic.Function.Iterate

open MathlibExt.Economics.Macro.SolowSteadyState
/-!
# Tests for the Cobb-Douglas Solow steady state

Concrete instance `a = 1/2`, `b = 1/4`, `alpha = 1/2`: the steady state is
`k* = ((1/2) / (3/4)) ^ 2 = 4/9`. The first iterate from `k0 = 1/9` is
`(1/2) * (1/3) + (1/4) * (1/9) = 7/36`, and the second iterate lies strictly
between `7/36` and `4/9`; the iterated path from `1/9` converges to `4/9`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.SolowSteadyState

open MathlibExt.Economics.Macro.SolowSteadyState

theorem rpow_sqrt_49 : (4/9 : ℝ) ^ ((1/2 : ℝ)) = 2/3 := by
  have h49 : (4/9 : ℝ) = (2/3 : ℝ) ^ (2 : ℕ) := by norm_num
  have hexp1 : (((2:ℕ)):ℝ) * (1/2) = 1 := by norm_num
  rw [h49, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (show (0:ℝ) ≤ 2/3 by norm_num), hexp1, Real.rpow_one]

theorem rpow_sqrt_19 : (1/9 : ℝ) ^ ((1/2 : ℝ)) = 1/3 := by
  have h19 : (1/9 : ℝ) = (1/3 : ℝ) ^ (2 : ℕ) := by norm_num
  have hexp1 : (((2:ℕ)):ℝ) * (1/2) = 1 := by norm_num
  rw [h19, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (show (0:ℝ) ≤ 1/3 by norm_num), hexp1, Real.rpow_one]

theorem steady_concrete : solowSteadyState (1/2) (1/4) (1/2) = 4/9 := by
  unfold solowSteadyState
  have hbase : (1/2 : ℝ) / (1 - 1/4) = 2/3 := by norm_num
  have hexp : (1:ℝ) / (1 - 1/2) = (((2:ℕ)):ℝ) := by
    have h : (1:ℝ) / (1 - 1/2) = 2 := by norm_num
    rw [h]
    norm_num
  rw [hbase, hexp, Real.rpow_natCast]
  norm_num

theorem map_fixed_concrete : solowMap (1/2) (1/4) (1/2) (4/9) = 4/9 := by
  unfold solowMap
  rw [rpow_sqrt_49]
  norm_num

theorem map_iter1_concrete : solowMap (1/2) (1/4) (1/2) (1/9) = 7/36 := by
  unfold solowMap
  rw [rpow_sqrt_19]
  norm_num

theorem map_iter2_between :
    7/36 < solowMap (1/2) (1/4) (1/2) (7/36)
      ∧ solowMap (1/2) (1/4) (1/2) (7/36) < 4/9 := by
  have hstar : solowSteadyState (1/2) (1/4) (1/2) = 4/9 := steady_concrete
  have hpos736 : (0:ℝ) < 7/36 := by norm_num
  have hlt : (7/36 : ℝ) < solowSteadyState (1/2) (1/4) (1/2) := by
    rw [hstar]; norm_num
  have hfix : 0 < solowSteadyState (1/2) (1/4) (1/2)
      ∧ solowMap (1/2) (1/4) (1/2) (solowSteadyState (1/2) (1/4) (1/2))
        = solowSteadyState (1/2) (1/4) (1/2) :=
    solow_fixedPoint (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsign : (7/36 : ℝ) < solowMap (1/2) (1/4) (1/2) (7/36)
      ↔ (7/36 : ℝ) < solowSteadyState (1/2) (1/4) (1/2) :=
    solow_self_lt_map_iff (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hpos736
  have hmono : StrictMonoOn (solowMap (1/2) (1/4) (1/2)) (Set.Ici 0) :=
    solow_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  have hup : solowMap (1/2) (1/4) (1/2) (7/36)
      < solowMap (1/2) (1/4) (1/2) (solowSteadyState (1/2) (1/4) (1/2)) :=
    hmono (Set.mem_Ici.mpr (le_of_lt hpos736))
      (Set.mem_Ici.mpr hfix.1.le) hlt
  rw [hfix.2, hstar] at hup
  exact ⟨hsign.mpr hlt, hup⟩

theorem tendsto_concrete : Filter.Tendsto
    (fun t => (solowMap (1/2) (1/4) (1/2))^[t] (1/9 : ℝ))
    Filter.atTop (nhds (4/9 : ℝ)) := by
  have h0 : (solowMap (1/2) (1/4) (1/2))^[0] (1/9 : ℝ) = 1/9 := rfl
  have hrec : ∀ t, (solowMap (1/2) (1/4) (1/2))^[t + 1] (1/9 : ℝ)
      = solowMap (1/2) (1/4) (1/2)
        ((solowMap (1/2) (1/4) (1/2))^[t] (1/9)) :=
    fun t => Function.iterate_succ_apply' _ _ _
  have hlim : Filter.Tendsto
      (fun t => (solowMap (1/2) (1/4) (1/2))^[t] (1/9 : ℝ))
      Filter.atTop (nhds (solowSteadyState (1/2) (1/4) (1/2))) :=
    solow_tendsto (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 hrec
  rw [steady_concrete] at hlim
  exact hlim
end MathlibExtTest.Economics.Macro.SolowSteadyState
