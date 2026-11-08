/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.FDeriv.WithLp

public import MathlibExt.Analysis.Complex.HartogsExtension

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

namespace MathlibExtTest.Analysis.Complex.HartogsExtension

open MathlibExt.Analysis.Complex.HartogsWanted Metric

-- A two-coordinate polynomial has continuous derivative and extends across the origin.
example :
    ContinuousOn
        (fderiv ℂ (fun x : EuclideanSpace ℂ (Fin 2) ↦
          WithLp.ofLp x 0 * WithLp.ofLp x 1)) (ball 0 2) ∧
      ∃ F : EuclideanSpace ℂ (Fin 2) → ℂ,
        DifferentiableOn ℂ F Set.univ ∧
          Set.EqOn F
            (fun x : EuclideanSpace ℂ (Fin 2) ↦
              WithLp.ofLp x 0 * WithLp.ofLp x 1)
            (Set.univ \ {0}) := by
  have hpoly : Differentiable ℂ
      (fun x : EuclideanSpace ℂ (Fin 2) ↦
        WithLp.ofLp x 0 * WithLp.ofLp x 1) := by
    exact ((differentiable_piLp 2).mp differentiable_id 0).mul
      ((differentiable_piLp 2).mp differentiable_id 1)
  constructor
  · exact continuousOn_fderiv_of_differentiableOn isOpen_ball hpoly.differentiableOn
  · apply hartogs_extension (n := 2) (by norm_num) isOpen_univ isConnected_univ
      isCompact_singleton (by simp)
    · rw [← Set.compl_eq_univ_sdiff]
      exact isConnected_compl_singleton_of_one_lt_rank
        (E := EuclideanSpace ℂ (Fin 2))
        (by norm_num [← Module.finrank_eq_rank, finrank_real_of_complex]) 0
    · exact hpoly.differentiableOn

-- The Cauchy–Green solver handles a concrete nonzero smooth bump.
example : ∃ g u : ℂ → ℂ, g 0 = 1 ∧ HasCompactSupport g ∧
    Differentiable ℝ u ∧ ∀ z, barDeriv u z = g z := by
  let β : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : ℂ → ℂ := Complex.ofRealCLM ∘ β
  have hg : ContDiff ℝ 1 g := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hgc : HasCompactSupport g := β.hasCompactSupport.comp_left (by simp)
  obtain ⟨u, hu, hbar⟩ := exists_differentiable_barDeriv_eq_of_hasCompactSupport
    (hg.differentiable (by norm_num)) (hg.continuous_fderiv (by norm_num)) hgc
  refine ⟨g, u, ?_, hgc, hu, hbar⟩
  have hβ : β 0 = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  simp [g, hβ]

-- The forward Wirtinger criterion applies to a concrete entire function.
example (w : ℂ) : barDeriv (fun z : ℂ ↦ z ^ 2 + Complex.exp z) w = 0 := by
  apply barDeriv_eq_zero_of_differentiableAt
  fun_prop

-- The converse criterion proves complex differentiability of z * conj z at the origin.
example : DifferentiableAt ℂ (id * (Complex.conjCAE : ℂ → ℂ)) 0 := by
  have hprod :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).mul
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  apply differentiableAt_of_barDeriv_eq_zero hprod.differentiableAt
  rw [barDeriv, hprod.fderiv]
  simp

end MathlibExtTest.Analysis.Complex.HartogsExtension
