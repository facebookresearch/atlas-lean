/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogramArea
import MathlibExt.NumberTheory.QuadraticForms.RootLattice

open MeasureTheory

namespace PeriodPair

-- The measure of a fundamental parallelogram, for an arbitrary period pair and vertex.
example (L : PeriodPair) (α : ℂ) :
    volume (L.fundamentalParallelogram α) =
      ENNReal.ofReal |(starRingEnd ℂ L.ω₁ * L.ω₂).im| :=
  volume_fundamentalParallelogram L α

-- The square lattice `ℤ + ℤi`: every fundamental parallelogram has measure `1`.
example (α : ℂ) (hI : Complex.I.im ≠ 0) :
    volume ((ofTau Complex.I hI).fundamentalParallelogram α) = 1 := by
  rw [volume_fundamentalParallelogram_of_ω₁_eq_one _ rfl (by rw [ofTau_ω₂]; simp), ofTau_ω₂]
  simp

-- `(1, 2 + 3i)`: measure `Im (2 + 3i) = 3`.
example (α : ℂ) (hτ : (2 + 3 * Complex.I).im ≠ 0) :
    volume ((ofTau (2 + 3 * Complex.I) hτ).fundamentalParallelogram α) = 3 := by
  rw [volume_fundamentalParallelogram_of_ω₁_eq_one _ rfl (by rw [ofTau_ω₂]; simp), ofTau_ω₂]
  simp

-- Periods `(2, 1 + i)`, not of the form `(1, τ)`: `Im(conj 2 · (1 + i)) = 2`.
example (L : PeriodPair) (h₁ : L.ω₁ = 2) (h₂ : L.ω₂ = 1 + Complex.I) (α : ℂ) :
    volume (L.fundamentalParallelogram α) = 2 := by
  rw [volume_fundamentalParallelogram, h₁, h₂]
  simp [Complex.mul_im]

-- Each point lies in exactly one lattice translate of a fundamental parallelogram.
example (L : PeriodPair) (α z : ℂ) :
    ∃! l : ℂ, l ∈ L.lattice ∧ z - l ∈ L.fundamentalParallelogram α :=
  existsUnique_sub_mem_fundamentalParallelogram L α z

end PeriodPair
