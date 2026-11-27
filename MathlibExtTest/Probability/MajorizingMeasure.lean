/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.MajorizingMeasure

/-!
# Tests for the majorizing measure theorem

The family has one constant coordinate and two copies of a standard Gaussian coordinate. Its
canonical distance vanishes between the two copies, so it is only a pseudo-distance, and its
maximum is the positive part of the Gaussian variable.
-/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.GenericChaining
open MathlibExt.Probability.MajorizingMeasureWanted

private noncomputable def process : Fin 3 → ℝ → ℝ :=
  fun i x => if i = 0 then 0 else x

example :
    let P := gaussianReal 0 1
    let g := gammaFunctional 2 (canonicalDist P process)
    let m := ENNReal.ofReal (∫ x, max 0 x ∂P)
    ∃ L : ℝ, 0 < L ∧ g ≤ ENNReal.ofReal L * m ∧ m ≤ ENNReal.ofReal L * g := by
  let P := gaussianReal 0 1
  let A : ℝ →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi fun i =>
    if i = 0 then 0 else ContinuousLinearMap.id ℝ ℝ
  have hA (x : ℝ) (i : Fin 3) : A x i = process i x := by
    by_cases h : i = 0 <;> simp [A, process, h]
  have hX (i : Fin 3) : Measurable (process i) := by
    simpa only [Function.comp_def, hA] using
      (measurable_pi_apply i).comp A.continuous.measurable
  have hG : IsGaussian (P.map fun x i => process i x) := by
    have he : A = (fun x i => process i x) := funext fun x => funext (hA x)
    rw [← he]
    exact isGaussian_map A
  have hcen (i : Fin 3) : ∫ x, process i x ∂P = 0 := by
    by_cases h : i = 0 <;> simp [process, h, P, integral_id_gaussianReal]
  have hmax (x : ℝ) : (⨆ i, process i x) = max 0 x := by
    apply le_antisymm
    · refine ciSup_le fun i => ?_
      by_cases h : i = 0 <;> simp [process, h]
    · have h := Set.Finite.bddAbove (Set.finite_range (process · x))
      refine max_le ?_ ?_
      · simpa [process] using le_ciSup h (0 : Fin 3)
      · simpa [process] using le_ciSup h (1 : Fin 3)
  obtain ⟨L, hL, h⟩ := majorizing_measure
  exact ⟨L, hL, by simpa only [hmax] using h ℝ P (Fin 3) process hX hG hcen⟩
