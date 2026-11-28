/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.EgorovDominatedRealLine

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted
open scoped Topology

-- The zero sequence converges a.e. to a function that is nonzero at 0.
-- Any exceptional set witnessing uniform convergence must exclude 0 from its complement.
example : ∃ E : Set ℝ, MeasurableSet E ∧ volume E < 1 ∧ (0 : ℝ) ∈ E := by
  let f : ℝ → ℝ := ({0} : Set ℝ).indicator (fun _ => 1)
  have hnot : ∀ᵐ x ∂volume, x ∉ ({0} : Set ℝ) := by
    rw [ae_iff]
    simp
  have hae : ∀ᵐ x ∂volume, Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (f x)) := by
    filter_upwards [hnot] with x hx
    rw [show f x = 0 from indicator_of_notMem hx _]
    exact tendsto_const_nhds
  obtain ⟨E, hE, hm, hu⟩ := exists_measure_lt_tendstoUniformlyOn_compl_of_ae_tendsto_of_abs_le
    f (fun _ _ => 0) (fun _ => 0) (fun _ => measurable_const) hae
    (integrable_zero ℝ ℝ volume) (by simp) 1 (by norm_num)
  refine ⟨E, hE, by simpa using hm, ?_⟩
  by_contra hn
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (f 0)) := hu.tendsto_at hn
  have heq := tendsto_nhds_unique h0
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  norm_num [f] at heq
