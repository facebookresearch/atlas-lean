/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.RankOneSpectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Tests for the spectrum of a rank-one operator

* On `ℝ × ℝ`, the rank-one operator `T = f.smulRight y` with `f` the
  first-coordinate functional and `y = (1, 0)` is the projection onto the
  first coordinate: `T (3, 5) = (3, 0)`, `T * T = T`, its spectrum is
  `{0, 1}`, `1` and `0` are eigenvalues, and `2` is not in the spectrum.
  The same `y` with the zero functional has spectrum `{0}`.
* The Hilbert-space form is tested on `EuclideanSpace ℝ (Fin 2)` with
  `x = y = e₀` and `w = e₁`: the rank-one operator `rankOne ℝ e₀ e₀` has
  spectrum `{0, 1}`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.RankOneSpectrumTests

open MathlibExt.Analysis.FunctionalAnalysis.RankOneSpectrum

/-- The first-coordinate functional on `ℝ × ℝ`. -/
noncomputable def testF : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The vector `(1, 0)` in `ℝ × ℝ`. -/
noncomputable def testY : ℝ × ℝ := (1, 0)

/-- The vector `(0, 1)` in `ℝ × ℝ`. -/
noncomputable def testW : ℝ × ℝ := (0, 1)

/-- The projection onto the first coordinate, as a rank-one operator. -/
noncomputable def testT : ℝ × ℝ →L[ℝ] ℝ × ℝ := testF.smulRight testY

example : testF testY = 1 := by simp [testF, testY]

example : testF testW = 0 := by simp [testF, testW]

example : testY ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)

example : testW ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)

/-- The projection sends `(3, 5)` to `(3, 0)`. -/
example : testT (3, 5) = (3, 0) := by
  simp [testT, testF, testY, ContinuousLinearMap.smulRight_apply]

/-- The projection is idempotent, from `T * T = (f y) • T` with `f y = 1`. -/
example : testT * testT = testT := by
  have h := smulRight_mul_self testF testY
  simpa [testT, testF, testY] using h

/-- `1` is an eigenvalue of the projection, with eigenvector `y`. -/
example : Module.End.HasEigenvalue (testT : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) 1 := by
  have h : Module.End.HasEigenvalue
      (testF.smulRight testY : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) (testF testY) :=
    hasEigenvalue_smulRight (by simp [testY])
  simpa [testT, testF, testY] using h

/-- `0` is an eigenvalue of the projection, with eigenvector `w`. -/
example : Module.End.HasEigenvalue (testT : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) 0 := by
  have h : Module.End.HasEigenvalue
      (testF.smulRight testY : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) 0 :=
    hasEigenvalue_zero_smulRight (w := testW) (by simp [testW]) (by simp [testF, testW])
  simpa [testT] using h

/-- The spectrum of the projection is `{0, 1}`. -/
example : spectrum ℝ testT = {0, 1} := by
  have h := spectrum_smulRight (f := testF) (y := testY) (w := testW)
    (by simp [testY]) (by simp [testW]) (by simp [testF, testW])
  simpa [testT, testF, testY] using h

/-- `2` is not in the spectrum of the projection. -/
example : (2 : ℝ) ∉ spectrum ℝ testT := by
  have h := not_mem_spectrum_smulRight (f := testF) (y := testY) (μ := (2 : ℝ))
    (by norm_num) (by simp [testF, testY])
  simpa [testT] using h

/-- With the zero functional, the rank-one operator has spectrum `{0}`. -/
example : spectrum ℝ ((0 : ℝ × ℝ →L[ℝ] ℝ).smulRight testY) = {0} := by
  exact spectrum_smulRight_of_apply_eq_zero (f := (0 : ℝ × ℝ →L[ℝ] ℝ)) (y := testY)
    (by simp [testY]) (by simp)

/-- The vector `e₀` in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def testE0 : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 (0 : Fin 2) (1 : ℝ)

/-- The vector `e₁` in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def testE1 : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 (1 : Fin 2) (1 : ℝ)

/-- The Hilbert-space form: `rankOne ℝ e₀ e₀` on `EuclideanSpace ℝ (Fin 2)`
has spectrum `{0, 1}`. -/
example : spectrum ℝ (InnerProductSpace.rankOne ℝ testE0 testE0) = {0, 1} := by
  have hx : testE0 ≠ 0 := by
    intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) h
    simp [testE0, PiLp.norm_single] at h2
  have hw : testE1 ≠ 0 := by
    intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) h
    simp [testE1, PiLp.norm_single] at h2
  have hyw : inner ℝ testE0 testE1 = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [testE0, testE1]
  have hyx : inner ℝ testE0 testE0 = 1 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [testE0]
  have h := spectrum_rankOne (x := testE0) (y := testE0) (w := testE1) hx hw hyw
  rw [hyx] at h
  exact h

end MathlibExtTest.Analysis.FunctionalAnalysis.RankOneSpectrumTests
