/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetryDensityCfValueEqOfAppendSymmetric
import Mathlib.Tactic.NormNum

/-!
# Tests for the density at a convergent from symmetric extensions

These tests specialize the density formula to the string `[2]` and derive vanishing at a
convergent when the density vanishes at zero.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 3.1.
-/

namespace MathlibExtTest.NumberTheory.GaussKuzminSymmetryDensityCfValueEqOfAppendSymmetric

open MetaMathlibExt MeasureTheory

example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0 : ℝ)..1, f x = 1)
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder [2, t], f x = ∫ x in cfCylinder [t, 2], f x) :
    f (1 / 2) = (2 / 3) * f 0 := by
  have h := density_cfValue_eq_of_append_symmetric f hf hf0 hf1 [2] (by decide) hsym
  norm_num [convergentMatrix, div_eq_mul_inv] at h
  simpa [div_eq_mul_inv, mul_comm, mul_assoc] using h

example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0 : ℝ)..1, f x = 1)
    (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) (hzero : f 0 = 0)
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder (a ++ [t]), f x = ∫ x in cfCylinder (t :: a.reverse), f x) :
    f ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) = 0 := by
  simpa [hzero] using density_cfValue_eq_of_append_symmetric f hf hf0 hf1 a ha hsym

end MathlibExtTest.NumberTheory.GaussKuzminSymmetryDensityCfValueEqOfAppendSymmetric
