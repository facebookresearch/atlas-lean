/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Normed.Lp.FinsuppL1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Finite-support L¹ norms and scalar multiplication

A single coordinate has its coefficient norm for arbitrary normed additive
groups. On complex coefficients, the single value `3 + 4i` has L¹ norm five,
and multiplication by `i` preserves that norm. The metric is the advertised
L¹ metric, and an empty index set has only the zero vector.
-/

noncomputable section

open scoped NNReal

namespace MathlibExtTest.FinsuppL1

universe u v

local instance : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩

example {ι : Type u} {E : Type v} [NormedAddCommGroup E] (i : ι) (x : E) :
    ‖WithLp.toLp (1 : ℝ≥0) (Finsupp.single i x)‖ = ‖x‖ := by
  rw [Finsupp.l1_norm_eq_sum]
  simp

private abbrev Vector := WithLp (1 : ℝ≥0) (Fin 2 →₀ ℂ)

private def singleVector : Vector :=
  WithLp.toLp (1 : ℝ≥0) (Finsupp.single 0 (3 + 4 * Complex.I))

private theorem singleVector_norm : ‖singleVector‖ = 5 := by
  rw [Finsupp.l1_norm_eq_sum]
  simp only [singleVector, WithLp.ofLp_toLp, Finsupp.sum_single_index, norm_zero]
  have hs : ‖(3 + 4 * Complex.I : ℂ)‖ ^ 2 = 25 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [norm_nonneg (3 + 4 * Complex.I : ℂ)]

example : ‖singleVector‖ = 5 ∧ singleVector ≠ 0 := by
  refine ⟨singleVector_norm, ?_⟩
  intro h
  have hn := singleVector_norm
  rw [h, norm_zero] at hn
  norm_num at hn

example : ‖Complex.I • singleVector‖ = 5 := by
  rw [Finsupp.l1_norm_smul, Complex.norm_I, one_mul, singleVector_norm]

example : dist (Complex.I • singleVector) 0 = 5 := by
  rw [dist_zero_right, norm_smul, Complex.norm_I, one_mul, singleVector_norm]

example :
    (Finsupp.instL1NormedAddCommGroup (ι := Fin 2) (E := ℂ)).toMetricSpace =
      Finsupp.l1Metric (ι := Fin 2) (E := ℂ) :=
  Finsupp.l1NormedAddCommGroup_metric_eq

example (x : WithLp (1 : ℝ≥0) (Fin 0 →₀ ℂ)) : x = 0 ∧ ‖x‖ = 0 := by
  have hx : x = 0 := by
    apply (WithLp.ofLp_injective (1 : ℝ≥0))
    ext i
    exact Fin.elim0 i
  exact ⟨hx, by rw [hx, norm_zero]⟩

end MathlibExtTest.FinsuppL1
