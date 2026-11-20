/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.GeometricTail

open MvPowerSeries

private def unitMajorant : GeometricMajorant (Fin 1) :=
  ⟨1, fun _ => 1, by norm_num, fun _ => by norm_num⟩

-- A uniform numerical bound for an arbitrary infinite coefficient family.
example (a : MvPowerSeries (Fin 1) ℚ) (ha : IsMajorized a unitMajorant)
    (x : Fin 1 → ℝ) (hx : ∀ i, |x i| ≤ 1 / 2) :
    |geometricSum a x - rectangularSum (fun _ => 3) a x| ≤ 1 / 4 := by
  have h := abs_geometricSum_sub_rectangularSum_le (b := fun _ => (1 / 2 : ℚ≥0))
    ha (by norm_num [unitMajorant]) (fun _ => 3) (x := x) (by simpa using hx)
  norm_num [geometricTailBound, ratio, unitMajorant] at h
  exact h

-- A zero evaluation radius leaves no tail after a positive cutoff.
example (a : MvPowerSeries (Fin 1) ℚ) (ha : IsMajorized a unitMajorant) :
    geometricSum a (fun _ => 0) = rectangularSum (fun _ => 1) a (fun _ => 0) := by
  have h := abs_geometricSum_sub_rectangularSum_le (b := fun _ => (0 : ℚ≥0))
    ha (by norm_num [unitMajorant]) (fun _ => 1) (x := fun _ => 0) (by simp)
  norm_num [geometricTailBound, ratio, unitMajorant] at h
  exact sub_eq_zero.mp h

-- A zero cutoff omits every coefficient.
example : rectangularWindow (fun _ : Fin 1 => 0) = ∅ := by
  ext n
  simp [mem_rectangularWindow]

-- With no axes the single constant term is retained, and the tail bound is zero.
example (m : GeometricMajorant (Fin 0)) (b : Fin 0 → ℚ≥0) (N : Fin 0 → ℕ) :
    geometricTailBound m b N = 0 := by
  simp [geometricTailBound]

example (N : Fin 0 → ℕ) : rectangularWindow N = {0} := by
  ext n
  simp [mem_rectangularWindow, Subsingleton.elim n 0]

#print axioms MvPowerSeries.summable_norm_seriesTerm
#print axioms MvPowerSeries.abs_geometricSum_sub_rectangularSum_le
