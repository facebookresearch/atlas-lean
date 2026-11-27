/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Fourier.DirichletJordan

open Set Filter Topology Complex
open scoped Real BigOperators

namespace MathlibExt.Analysis.Fourier.DirichletTheoremWanted

private noncomputable def step (x : ℝ) : ℝ := if Real.cos x ≤ 0 then 1 else 0

private lemma step_bv : BoundedVariationOn step (Icc (-π) π) := by
  have hm : MonotoneOn step (Icc 0 π) := by
    intro x hx y hy hxy
    have hcos := Real.antitoneOn_cos hx hy hxy
    simp only [step]
    split_ifs <;> grind
  have hr := hm.boundedVariationOn (C := 1) (by intro x _; unfold step; split <;> norm_num)
  have hl : BoundedVariationOn step (Icc (-π) 0) := by
    have h := eVariationOn.comp_le_of_antitoneOn step Neg.neg (s := Icc 0 π) (t := Icc (-π) 0)
      (fun _ _ _ _ h ↦ neg_le_neg h) (fun x hx ↦ ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    have heven : step ∘ Neg.neg = step := by ext x; simp [step]
    rw [heven] at h
    exact ne_top_of_le_ne_top hr h
  have h := eVariationOn.Icc_add_Icc step (s := univ) (neg_nonpos.mpr Real.pi_pos.le)
    Real.pi_pos.le (mem_univ 0)
  rw [BoundedVariationOn, ← univ_inter (Icc (-π) π), ← h]
  simpa using ENNReal.add_ne_top.mpr ⟨hl, hr⟩

-- At π/2 this square wave takes the value I, with one-sided limits I and 0.
private noncomputable def squareWave (x : ℝ) : ℂ := step x • I

example :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fourierCoeffOn Real.two_pi_pos squareWave n *
        exp (I * (n : ℂ) * ((π / 2 : ℝ) : ℂ))) atTop (𝓝 (I / 2)) := by
  have hp : Function.Periodic squareWave (2 * π) := by
    intro x
    simp [squareWave, step, Real.cos_add_two_pi]
  have hb : BoundedVariationOn squareWave (Icc (-π) π) :=
    (ContinuousLinearMap.toSpanSingleton ℝ I).lipschitzWith.comp_boundedVariationOn step_bv
  obtain ⟨p, m, hpr, hml, hs⟩ := dirichlet_pointwise_convergence squareWave hp hb (π / 2)
  have hr : Tendsto squareWave (𝓝[>] (π / 2)) (𝓝 I) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(nhdsGT_basis (π / 2)).mem_of_mem
      (show π / 2 < π + π / 2 by linarith [Real.pi_pos])] with t ht
    simp [squareWave, step, (Real.cos_neg_of_pi_div_two_lt_of_lt ht.1 ht.2).le]
  have hl : Tendsto squareWave (𝓝[<] (π / 2)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(nhdsLT_basis (π / 2)).mem_of_mem
      (show -(π / 2) < π / 2 by linarith [Real.pi_pos])] with t ht
    simp [squareWave, step, (Real.cos_pos_of_mem_Ioo ht).not_ge]
  simpa [tendsto_nhds_unique hpr hr, tendsto_nhds_unique hml hl] using hs

end MathlibExt.Analysis.Fourier.DirichletTheoremWanted
