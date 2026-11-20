/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.CriticalState
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Modified Cam-Clay yield-domain checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.CriticalState`: the
ellipse center, intercepts and apex, sign controls on `M`
and `pc`, the deviatoric invariant normalizations (triaxial,
pure shear, hydrostatic), the mean-stress sign test, and
the critical-state line shape.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Ellipse focused checks and controls
- B. Invariant normalizations

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.CriticalState`
-/

open EarthScience
open Elasticity
open scoped Matrix

namespace PhyslibExtTest.EarthScience.Geotechnical.CriticalState

/-! ## A. Ellipse focused checks and controls -/

/-- The center `(pc / 2, 0)` is interior for `M, pc > 0`. -/
example {M pc : ℝ} (hM : 0 < M) (hpc : 0 < pc) :
    modifiedCamClayYield M pc (pc / 2) 0 < 0 := by
  rw [modifiedCamClayYield_eq_translated_ellipse]
  have h : (0 : ℝ) < (M * pc / 2) ^ 2 := by positivity
  simp
  linarith

/-- The intercepts `p = 0` and `p = pc` and the apex
`(pc / 2, M pc / 2)` lie on `F = 0`. -/
example (M pc : ℝ) : modifiedCamClayYield M pc 0 0 = 0 := by
  simp [modifiedCamClayYield]

example (M pc : ℝ) : modifiedCamClayYield M pc pc 0 = 0 := by
  simp [modifiedCamClayYield]

example (M pc : ℝ) :
    modifiedCamClayYield M pc (pc / 2) (M * pc / 2) = 0 := by
  rw [modifiedCamClayYield_eq_translated_ellipse]
  ring

/-- Negative control: `M = -1` breaks the `q` bound (the
point `(1, 1)` is in the domain at `pc = 2`). -/
example : ((1 : ℝ), (1 : ℝ)) ∈ modifiedCamClayElasticDomain (-1) 2 ∧
    ¬ |(1 : ℝ)| ≤ (-1) * 2 / 2 := by
  refine ⟨?_, by norm_num⟩
  change modifiedCamClayYield (-1) 2 1 1 ≤ 0
  norm_num [modifiedCamClayYield]

/-- Negative control: at `M = 0` the domain contains
negative `p`. -/
example : ((-1 : ℝ), (0 : ℝ)) ∈ modifiedCamClayElasticDomain 0 1 ∧
    ¬ (0 ≤ (-1 : ℝ)) := by
  refine ⟨?_, by norm_num⟩
  change modifiedCamClayYield 0 1 (-1) 0 ≤ 0
  norm_num [modifiedCamClayYield]

/-- Negative control: `pc < 0` puts the domain on
negative `p`. -/
example : ((-1 : ℝ), (0 : ℝ)) ∈ modifiedCamClayElasticDomain 1 (-2) ∧
    ¬ (0 ≤ (-1 : ℝ)) := by
  refine ⟨?_, by norm_num⟩
  change modifiedCamClayYield 1 (-2) (-1) 0 ≤ 0
  norm_num [modifiedCamClayYield]

/-- Convexity also holds at the degenerate `M = 0`,
`pc < 0`. -/
example : Convex ℝ (modifiedCamClayElasticDomain 0 (-3)) :=
  convex_modifiedCamClayElasticDomain 0 (-3)

/-- Degenerate joint-zero case: at `M = pc = 0` the
domain is the line `q = 0`, not a point: `(5, 0)` is in
it and `(0, 1)` is not. -/
example : ((5 : ℝ), (0 : ℝ)) ∈ modifiedCamClayElasticDomain 0 0 ∧
    ((0 : ℝ), (1 : ℝ)) ∉ modifiedCamClayElasticDomain 0 0 := by
  constructor
  · change modifiedCamClayYield 0 0 5 0 ≤ 0
    norm_num [modifiedCamClayYield]
  · change ¬ modifiedCamClayYield 0 0 0 1 ≤ 0
    norm_num [modifiedCamClayYield]

/-- At `M = 0` with `pc ≠ 0` the domain is still the
whole line `q = 0`: `p` is unbounded, with no finite
`p` semi-axis `|pc| / 2`. -/
example : ((100 : ℝ), (0 : ℝ)) ∈ modifiedCamClayElasticDomain 0 2 := by
  change modifiedCamClayYield 0 2 100 0 ≤ 0
  norm_num [modifiedCamClayYield]

/-- Critical-state line shape: on `q = M p`,
`F = M² p (2p - pc)`. -/
example (M pc p : ℝ) :
    modifiedCamClayYield M pc p (M * p) = M ^ 2 * p * (2 * p - pc) :=
  modifiedCamClayYield_on_critical_line M pc p


/-- Nonzero critical point: at `M = pc = 2`, the point
`(1, 2)` is the nonzero intersection. -/
example : (1 : ℝ) = 2 / 2 ∧ (2 : ℝ) = 2 * 2 / 2 :=
  modifiedCamClayYield_eq_zero_on_critical_line_of_ne_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [modifiedCamClayYield]) (by norm_num)

/-- Origin control: the origin is the excluded second
intersection, not the critical point. -/
example : ¬ ((0 : ℝ) = 2 / 2 ∧ (0 : ℝ) = 2 * 2 / 2) := by norm_num

/-- Physical off-yield points on the line at
`M = 1`, `pc = 2` (interior value and the named
off-yield control). -/
example : modifiedCamClayYield 1 2 (1 / 2) (1 / 2) = -1 / 2 := by
  norm_num [modifiedCamClayYield]

example : modifiedCamClayYield 1 2 (1 / 2) (1 * (1 / 2)) ≠ 0 :=
  modifiedCamClayYield_on_critical_line_ne_zero
    (by norm_num) (by norm_num) (by norm_num)

/-- `M = 0` counterexamples: without `0 < M` the whole
line `q = 0` lies on the locus. -/
example : modifiedCamClayYield 0 2 3 (0 * 3) = 0 := by
  norm_num [modifiedCamClayYield]

example : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) = 0 * 3 ∧
    modifiedCamClayYield 0 2 3 0 = 0 ∧
    ¬ ((3 : ℝ) = 0 ∨ (3 : ℝ) = 2 / 2) := by
  norm_num [modifiedCamClayYield]

/-- Lower-apex branch control: `(1, -1)` is on the locus
but on `q = -M p`, not the signed physical branch. -/
example : modifiedCamClayYield 1 2 1 (-1) = 0 ∧
    ¬ ((0 : ℝ) ≤ -1 ∧ (-1 : ℝ) = 1 * 1) := by
  norm_num [modifiedCamClayYield]

/-! ## B. Invariant normalizations -/

/-- Triaxial normalization `q = |σa - σr|`. -/
example (a b : ℝ) :
    deviatoricInvariant !![a, 0, 0; 0, b, 0; 0, 0, b] = |a - b| := by
  rw [← Real.sqrt_sq_eq_abs, deviatoricInvariant]
  congr 1
  simp [deviatoricStress, meanStress, Matrix.trace_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.one_apply]
  ring

/-- Pure shear `τ` gives `q = √3 |τ|`. -/
example (τ : ℝ) :
    deviatoricInvariant !![0, τ, 0; τ, 0, 0; 0, 0, 0]
      = Real.sqrt 3 * |τ| := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by norm_num), deviatoricInvariant]
  congr 1
  simp [deviatoricStress, meanStress, Matrix.trace_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring

/-- Hydrostatic stress has `q = 0`. -/
example (p : ℝ) :
    deviatoricInvariant (p • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by
  have hs : deviatoricStress (p • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by
    simp [deviatoricStress, meanStress, Matrix.trace_smul, Matrix.trace_one]
  simp [deviatoricInvariant, hs]

/-- Mean-stress sign test: the compression-positive mean
stress is `-σₘ`. -/
example (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    meanStress (compressionPositiveStress σ) = -meanStress σ := by
  simp [meanStress, compressionPositiveStress, Matrix.trace_neg, neg_div]

/-- Symmetric (Cauchy) stress: the invariant is `√(3 J₂)`
of the deviatoric part, here at a triaxial stress. -/
example (a b : ℝ) :
    deviatoricInvariant !![a, 0, 0; 0, b, 0; 0, 0, b]
      = Real.sqrt (3 * (-stressInvariant2
        (deviatoricStress !![a, 0, 0; 0, b, 0; 0, 0, b]))) :=
  deviatoricInvariant_eq_sqrt_neg_stressInvariant2_deviatoric
    (by
      unfold IsSymmetricStress
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply])

/-- Nonsymmetric control: for the single-entry matrix
`σ 0 1 = 1` the Frobenius-form invariant is `√(3/2)`,
while `J₂` of its deviatoric part is `0`; the two notions
agree only under symmetry. -/
example : deviatoricInvariant !![0, 1, 0; 0, 0, 0; 0, 0, 0]
      = Real.sqrt (3 / 2) ∧
    stressInvariant2
      (deviatoricStress !![0, 1, 0; 0, 0, 0; 0, 0, 0]) = 0 := by
  constructor
  · simp [deviatoricInvariant, deviatoricStress, meanStress,
      Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [stressInvariant2, deviatoricStress, meanStress,
      Matrix.trace_fin_three]

#print axioms EarthScience.modifiedCamClayYield_eq_translated_ellipse
#print axioms EarthScience.convex_modifiedCamClayElasticDomain
#print axioms EarthScience.modifiedCamClayElasticDomain_bounds
#print axioms EarthScience.modifiedCamClayYield_on_critical_line
#print axioms EarthScience.modifiedCamClayYield_eq_zero_on_critical_line_iff
#print axioms
  EarthScience.modifiedCamClayYield_eq_zero_on_critical_line_of_ne_zero
#print axioms EarthScience.modifiedCamClayYield_on_critical_line_ne_zero
#print axioms EarthScience.meanStress_effectiveStressCompressionPositive
#print axioms EarthScience.deviatoricInvariant_effectiveStressCompressionPositive
#print axioms EarthScience.deviatoricInvariant_compressionPositiveStress
#print axioms
  EarthScience.deviatoricInvariant_eq_sqrt_neg_stressInvariant2_deviatoric

end PhyslibExtTest.EarthScience.Geotechnical.CriticalState
