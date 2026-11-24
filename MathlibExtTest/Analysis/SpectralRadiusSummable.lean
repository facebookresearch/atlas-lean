/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.SpectralRadiusSummable

@[expose] public section

open Filter

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem spectralRadius_zero_matrix_fin_two_lt_one :
    spectralRadius ℂ (0 : Matrix (Fin 2) (Fin 2) ℂ) < 1 := by simp

example : Summable (fun k => (0 : Matrix (Fin 2) (Fin 2) ℂ) ^ k) :=
  summable_of_spectralRadius_lt_one _ spectralRadius_zero_matrix_fin_two_lt_one

example : Tendsto (fun k => (0 : Matrix (Fin 2) (Fin 2) ℂ) ^ k) atTop (nhds 0) := by
  have h := (summable_of_spectralRadius_lt_one _
    spectralRadius_zero_matrix_fin_two_lt_one).tendsto_cofinite_zero
  rwa [Nat.cofinite_eq_atTop] at h

example : ¬ spectralRadius ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ) < 1 := by
  rw [spectrum.spectralRadius_one]
  simp

end
end
public section
