/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ScottishBook17
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open MathlibExt.Probability.ScottishBook17Wanted

-- Constant-one draws are pairwise independent. The averages are one after the empty first sum.
example (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ _i ∈ Finset.range n, (fun _ : Ω => (1 : ℝ)) ω) / (n : ℝ))
      atTop (𝓝 1) := by
  have hc : Tendsto (fun n : ℕ => (∑ _i ∈ Finset.range n, (1 : ℝ)) / (n : ℝ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [hn']
  have h := urnConversePoisson Ω μ (fun _ => 1) (fun _ _ => 1) 1
    (fun _ => by norm_num) (fun _ => measurable_const) (fun _ => by simp)
    (fun _ => by simp) (fun _ _ _ => indepFun_const_left (1 : ℝ) (fun _ : Ω => (1 : ℝ)))
  filter_upwards [h] with ω hω
  exact hω hc
