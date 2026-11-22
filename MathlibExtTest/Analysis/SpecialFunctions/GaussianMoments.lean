/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.GaussianMoments
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.NormNum

open MeasureTheory Set Real
open scoped ContDiff
open MathlibExt.Analysis.GaussianMoments

-- Nonintegrable constant data are valid inputs, including high moment orders.
example : ¬ Integrable (fun _ : ℝ => (1 : ℝ)) := by
  simp [integrable_const_iff, isFiniteMeasure_iff]

example : Integrable (fun y : ℝ => y ^ 7 * exp (-2 * y ^ 2 + 3 * y)) := by
  simpa using integrable_gaussianMoment (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    ⟨1, fun _ => by norm_num⟩ 7 (p := (2, 3)) (by norm_num)

-- An independent normalization check against Mathlib's Gaussian integral.
example : gaussianMoment (fun _ => 1) 0 (1, 0) = sqrt π := by
  simpa [gaussianMoment] using integral_gaussian (1 : ℝ)

example : ContDiffOn ℝ ∞ (gaussianMoment (fun _ => (-2 : ℝ)) 7) (Ioi 0 ×ˢ univ) :=
  gaussianMoment_contDiffOn aestronglyMeasurable_const ⟨2, fun _ => by norm_num⟩ 7

-- Both parameter directions: the signs and shifts are checked explicitly.
example (f : ℝ → ℝ) (hf : AEStronglyMeasurable f) (hb : ∃ M, ∀ y, |f y| ≤ M)
    (n : ℕ) (a b : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s => gaussianMoment f n (s, b)) (-gaussianMoment f (n + 2) (a, b)) a := by
  simpa using! (gaussianMoment_hasFDerivAt hf hb n (p := (a, b)) ha).comp_hasDerivAt a
    ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))

example (f : ℝ → ℝ) (hf : AEStronglyMeasurable f) (hb : ∃ M, ∀ y, |f y| ≤ M)
    (n : ℕ) (a b : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s => gaussianMoment f n (a, s)) (gaussianMoment f (n + 1) (a, b)) b := by
  simpa using! (gaussianMoment_hasFDerivAt hf hb n (p := (a, b)) ha).comp_hasDerivAt b
    ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))

-- A genuinely joint direction combines both moment shifts.
example (f : ℝ → ℝ) (hf : AEStronglyMeasurable f) (hb : ∃ M, ∀ y, |f y| ≤ M)
    (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    fderiv ℝ (gaussianMoment f n) p (1, 1) =
      -gaussianMoment f (n + 2) p + gaussianMoment f (n + 1) p := by
  rw [(gaussianMoment_hasFDerivAt hf hb n hp).fderiv]
  simp

-- Smoothness is uniform in the requested finite order, beyond the C3 use case.
example (f : ℝ → ℝ) (hf : AEStronglyMeasurable f) (hb : ∃ M, ∀ y, |f y| ≤ M) :
    ContDiffOn ℝ 12 (gaussianMoment f 5) (Ioi 0 ×ˢ univ) :=
  (gaussianMoment_contDiffOn hf hb 5).of_le (by simp)

#print axioms MathlibExt.Analysis.GaussianMoments.gaussianMoment_contDiffOn
