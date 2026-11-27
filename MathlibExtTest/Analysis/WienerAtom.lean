/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.WienerAtom

/-! # Tests for Wiener's atom-detection formula -/

namespace MathlibExtTest.Analysis.WienerAtom

open MeasureTheory Filter Topology MathlibExt.Analysis.WienerAtomWanted.Analysis

local notation "Torus" => AddCircle (2 * Real.pi)

-- A point mass evaluates the character at its location, including at negative frequencies.
example (x : Torus) (k : ℤ) : fourierCoeffMeasure (Measure.dirac x) k = fourier k x := by
  simp [fourierCoeffMeasure]

-- The squared mass of the only atom contributes one.
example (a : Torus) :
    Tendsto (fun N : ℕ ↦ (1 / (N : ℝ)) *
      ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖fourierCoeffMeasure (Measure.dirac a) k‖ ^ 2)
      atTop (𝓝 1) := by
  classical
  have h (x : Torus) : ((Measure.dirac a) {x}).toReal ^ 2 = if x = a then 1 else 0 := by
    by_cases hx : x = a <;> simp [Measure.dirac_apply', hx, Ne.symm]
  simpa only [h, tsum_ite_eq] using wiener_atom_detection (Measure.dirac a)

-- Normalized Haar measure has no point masses.
example [Fact (0 < 2 * Real.pi)] :
    Tendsto (fun N : ℕ ↦ (1 / (N : ℝ)) *
      ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖fourierCoeffMeasure AddCircle.haarAddCircle k‖ ^ 2)
      atTop (𝓝 0) := by
  simpa using wiener_atom_detection AddCircle.haarAddCircle

end MathlibExtTest.Analysis.WienerAtom
