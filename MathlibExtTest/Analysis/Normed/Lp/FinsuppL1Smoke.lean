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

private def tailVector : Vector :=
  WithLp.toLp (1 : ℝ≥0) (Finsupp.single 1 ((2 : ℝ) • Complex.I))

private def multiVector : Vector := singleVector + tailVector

private theorem tailVector_norm : ‖tailVector‖ = 2 := by
  rw [Finsupp.l1_norm_eq_sum]
  simp only [tailVector, WithLp.ofLp_toLp, Finsupp.sum_single_index, norm_zero]
  simp

private theorem multiVector_norm : ‖multiVector‖ = 7 := by
  rw [Finsupp.l1_norm_eq_sum]
  change (Finsupp.single (0 : Fin 2) (3 + 4 * Complex.I) +
      Finsupp.single 1 ((2 : ℝ) • Complex.I)).sum (fun _ x => ‖x‖) = 7
  rw [Finsupp.sum_single_add_single 0 1 _ _ _ (by decide)
    (fun _ => norm_zero)]
  have ha : ‖(3 + 4 * Complex.I : ℂ)‖ = 5 := by
    have h := singleVector_norm
    rw [Finsupp.l1_norm_eq_sum] at h
    simpa only [singleVector, WithLp.ofLp_toLp, Finsupp.sum_single_index, norm_zero] using h
  have hb : ‖(2 : ℝ) • Complex.I‖ = 2 := by simp
  rw [ha, hb]
  norm_num

example : ‖multiVector‖ = 7 ∧ ‖singleVector‖ < ‖multiVector‖ := by
  rw [multiVector_norm, singleVector_norm]
  norm_num

example : ‖Complex.I • multiVector‖ = 7 ∧ dist (Complex.I • multiVector) 0 = 7 := by
  rw [Finsupp.l1_norm_smul, Complex.norm_I, one_mul, multiVector_norm, dist_zero_right,
    norm_smul, Complex.norm_I, one_mul, multiVector_norm]
  exact ⟨rfl, rfl⟩

example : dist multiVector singleVector = 2 := by
  rw [dist_eq_norm]
  have hdiff : multiVector - singleVector = tailVector := by
    change singleVector + tailVector - singleVector = tailVector
    abel
  rw [hdiff, tailVector_norm]

example :
    multiVector.ofLp (0 : Fin 2) = 3 + 4 * Complex.I ∧
      multiVector.ofLp (1 : Fin 2) = (2 : ℝ) • Complex.I := by
  simp [multiVector, singleVector, tailVector, WithLp.ofLp_add]

end MathlibExtTest.FinsuppL1
