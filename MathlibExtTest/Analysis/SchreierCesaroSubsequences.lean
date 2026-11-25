/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SchreierCesaroSubsequences

open Filter MeasureTheory Topology
open MathlibExt.Analysis.ScottishBook4Wanted
open scoped ENNReal

example (b : Bool) : fairCoinMeasure {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> simp [fairCoinMeasure]

example :
    ∀ᵐ _ω ∂(Measure.infinitePi fun _ : ℕ => fairCoinMeasure),
      Tendsto (fun N : ℕ =>
        (∑ _k ∈ Finset.range N, (-3 : ℝ)) / (N : ℝ)) atTop (𝓝 (-3)) := by
  have hlim : Tendsto (fun n : ℕ =>
      (∑ _i ∈ Finset.range n, (-3 : ℝ)) / (n : ℝ)) atTop (𝓝 (-3)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel_left₀ (-3 : ℝ) (Nat.cast_ne_zero.mpr hn)]
  exact schreierCesaroSubsequences (fun _ => -3) (-3)
    ⟨3, fun _ => by norm_num⟩ hlim
