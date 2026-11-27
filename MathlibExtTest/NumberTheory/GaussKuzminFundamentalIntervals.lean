/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals

/-! # Tests for fundamental intervals of reversed and extended strings -/

open MetaMathlibExt MeasureTheory

-- The reversed string of `[2]` is itself; its interval is `(1/3, 1/2]`.
example : cfCylinder [2] =ᵐ[volume] fundInterval (1 / 2 : ℝ) (1 / 3 : ℝ) := by
  have h := (cfCylinder_reverse_append_cons_ae_eq [2] (by decide) 1 (by decide)).1
  have hC : convergentMatrix [2] = !![0, 1; 1, 2] := by decide
  rw [show ([2] : List ℕ).reverse = [2] from rfl, hC] at h
  norm_num at h
  exact h

-- Appending `1` to the empty string gives the string `[1]`, with interval `(1/2, 1]`.
example : cfCylinder [1] =ᵐ[volume] fundInterval (1 : ℝ) (1 / 2 : ℝ) := by
  have h := (cfCylinder_reverse_append_cons_ae_eq [] (by decide) 1 (by decide)).2.1
  have hC : convergentMatrix ([] : List ℕ) = 1 := convergentMatrix_nil
  norm_num [hC, convergentMatrix] at h
  exact h

-- Prepending `2` to `[1]` gives `[2, 1]`, with interval `(1/3, 2/5)`.
example : cfCylinder [2, 1] =ᵐ[volume] fundInterval (1 / 3 : ℝ) (2 / 5 : ℝ) := by
  have h := (cfCylinder_reverse_append_cons_ae_eq [1] (by decide) 2 (by decide)).2.2.1
  have hC : convergentMatrix [1] = !![0, 1; 1, 1] := by decide
  rw [hC] at h
  norm_num at h
  exact h

-- Prepending `1` to the reverse of `[2]` gives `[1, 2]`, with interval `(2/3, 3/4)`.
example : cfCylinder [1, 2] =ᵐ[volume] fundInterval (2 / 3 : ℝ) (3 / 4 : ℝ) := by
  have h := (cfCylinder_reverse_append_cons_ae_eq [2] (by decide) 1 (by decide)).2.2.2
  have hC : convergentMatrix [2] = !![0, 1; 1, 2] := by decide
  rw [hC] at h
  norm_num at h
  exact h
