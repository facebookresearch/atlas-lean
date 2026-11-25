/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.GeometricMajorant

open MvPowerSeries

private def unitMajorant : GeometricMajorant (Fin 1) :=
  ⟨1, fun _ => 1, by norm_num, fun _ => by norm_num⟩

private def onesSeries : MvPowerSeries (Fin 1) ℚ := fun _ => 1

private theorem ones_majorized : IsMajorized onesSeries unitMajorant := by
  intro n
  change |(1 : ℚ)| ≤ 1 * ∏ i : Fin 1, (1 ^ n i)⁻¹
  norm_num

-- Infinite geometric coefficients give a nontrivial Cauchy product bound.
example : IsMajorized (onesSeries * onesSeries)
    ⟨1, fun _ => 1 / 2, by norm_num, fun _ => by norm_num⟩ := by
  simpa [unitMajorant] using IsMajorized.mul (fun _ => 1) ones_majorized ones_majorized
    (fun _ => rfl) (fun _ => rfl)

-- Empty-variable products retain the constant coefficient.
example : IsMajorized (C 3 : MvPowerSeries (Fin 0) ℚ)
    ⟨3, Fin.elim0, by norm_num, fun i => Fin.elim0 i⟩ := by
  intro n
  have hn : n = 0 := Subsingleton.elim _ _
  subst n
  norm_num

-- The total inverse of a zero constant series is covered by the API.
example : IsMajorized (0 : MvPowerSeries (Fin 1) ℚ)⁻¹
    ⟨0, fun _ => 1 / 2, by norm_num, fun _ => by norm_num⟩ := by
  simpa using isMajorized_inv (0 : MvPowerSeries (Fin 1) ℚ)
    (c := 0) (M := 0) (R := fun _ => 1) (r := fun _ => 1 / 2)
    (by simp) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp) (by norm_num)

-- The inverse smallness condition allows equality at its threshold.
example : IsMajorized (1 - X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)⁻¹
    ⟨1, fun _ => 1 / 2, by norm_num, fun _ => by norm_num⟩ := by
  have rest : ∀ n : Fin 1 →₀ ℕ, n ≠ 0 →
      |coeff n (1 - X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)| ≤
        1 * radiiWeight (fun _ => 1) n := by
    intro n hn
    by_cases hx : n = Finsupp.single 0 1
    · subst n
      norm_num [radiiWeight, coeff_X, coeff_one]
    · simp [map_sub, coeff_one, coeff_X, hn, hx, radiiWeight]
  convert isMajorized_inv (1 - X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)
    (c := 1) (M := 1) (R := fun _ => 1) (r := fun _ => 1 / 2)
    (by simp) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) rest (by norm_num) using 1
  norm_num

-- A negative constant with absolute value different from one checks inverse scaling.
example : IsMajorized (C (-2) + X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)⁻¹
    ⟨1 / 2, fun _ => 1 / 2, by norm_num, fun _ => by norm_num⟩ := by
  have rest : ∀ n : Fin 1 →₀ ℕ, n ≠ 0 →
      |coeff n (C (-2) + X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)| ≤
        1 * radiiWeight (fun _ => 1) n := by
    intro n hn
    by_cases hx : n = Finsupp.single 0 1 <;>
      norm_num [map_add, coeff_C, coeff_X, hn, hx, radiiWeight]
  convert isMajorized_inv (C (-2) + X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)
    (c := -2) (M := 1) (R := fun _ => 1) (r := fun _ => 1 / 2)
    (by simp) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) rest (by norm_num) using 1
  norm_num

#print axioms MvPowerSeries.IsMajorized.mul
#print axioms MvPowerSeries.isMajorized_inv
