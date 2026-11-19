/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.InputOutput.GrossOutputMono
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

namespace MathlibExtTest.Economics.InputOutput.GrossOutputMono

open MathlibExt.Economics.InputOutput Matrix

theorem test_rowSum_mono_concrete : ((![3, 2] : Fin 2 → ℝ) ≤ ![5, 2]) := by
  have hA0 : ∀ i j,
      0 ≤ (!![(1 / 2 : ℝ), 1 / 4; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  have hrow : ∀ i,
      ∑ j, (!![(1 / 2 : ℝ), 1 / 4; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) i j < 1 := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  have hx : ((![3, 2] : Fin 2 → ℝ) =
      (!![(1 / 2 : ℝ), 1 / 4; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 2] + ![1, 1]) := by
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  have hx' : ((![5, 2] : Fin 2 → ℝ) =
      (!![(1 / 2 : ℝ), 1 / 4; 0, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![5, 2] + ![2, 1]) := by
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  have hd : ((![1, 1] : Fin 2 → ℝ) ≤ ![2, 1]) := by
    intro i
    fin_cases i <;> simp <;> norm_num
  exact grossOutput_mono_of_rowSum_lt_one hA0 hrow hx hx' hd

theorem test_rowSum_mono_zero (d d' : Fin 2 → ℝ) (hd : d ≤ d') : d ≤ d' :=
  grossOutput_mono_of_rowSum_lt_one (A := (0 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun i j => by simp) (fun i => by simp)
    (by simp : d = (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ d + d)
    (by simp : d' = (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ d' + d') hd

theorem test_spectral_mono_zero (d d' : Fin 2 → ℝ) (hd : d ≤ d') : d ≤ d' :=
  grossOutput_mono (A := (0 : Matrix (Fin 2) (Fin 2) ℝ)) (fun i j => by simp)
    (by
      have h0 : ((0 : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)) = 0 := by
        ext i j <;> simp
      rw [h0, spectrum.spectralRadius_zero]
      exact zero_lt_one)
    (by simp : d = (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ d + d)
    (by simp : d' = (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ d' + d') hd

end MathlibExtTest.Economics.InputOutput.GrossOutputMono
