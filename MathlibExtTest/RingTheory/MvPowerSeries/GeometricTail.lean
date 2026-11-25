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

private def unitMajorantTwo : GeometricMajorant (Fin 2) :=
  ⟨1, fun _ => 1, by norm_num, fun _ => by norm_num⟩

private def onesSeriesTwo : MvPowerSeries (Fin 2) ℚ := fun _ => 1

private theorem onesTwo_majorized : IsMajorized onesSeriesTwo unitMajorantTwo := by
  intro n
  change |(1 : ℚ)| ≤ 1 * ∏ i : Fin 2, (1 ^ n i)⁻¹
  norm_num

-- Two infinite axes, unequal evaluation radii and cutoffs exercise overlapping tails.
example : |geometricSum onesSeriesTwo ![1 / 2, 1 / 3] -
    rectangularSum ![2, 3] onesSeriesTwo ![1 / 2, 1 / 3]| ≤ 31 / 36 := by
  have h := abs_geometricSum_sub_rectangularSum_le
    (b := ![(1 / 2 : ℚ≥0), (1 / 3 : ℚ≥0)]) onesTwo_majorized
    (by intro i; fin_cases i <;> norm_num [unitMajorantTwo]) ![2, 3]
    (x := ![1 / 2, 1 / 3]) (by intro i; fin_cases i <;> norm_num)
  norm_num [geometricTailBound, ratio, unitMajorantTwo, Fin.sum_univ_two,
    Fin.prod_univ_two] at h
  exact h

-- An explicit omitted monomial gives an actual nonzero truncation error.
example : |geometricSum (X (0 : Fin 1)) (fun _ => 1 / 2) -
    rectangularSum (fun _ => 1) (X (0 : Fin 1)) (fun _ => 1 / 2)| = 1 / 2 := by
  have hs : geometricSum (X (0 : Fin 1)) (fun _ => (1 / 2 : ℝ)) = 1 / 2 := by
    have h := hasSum_single
      (f := seriesTerm (X (0 : Fin 1)) (fun _ => (1 / 2 : ℝ))) (Finsupp.single 0 1)
      (fun n hn => by simp [seriesTerm, coeff_X, hn])
    simpa [geometricSum, seriesTerm, coeff_X] using h.tsum_eq
  have hr : rectangularSum (fun _ => 1) (X (0 : Fin 1)) (fun _ => (1 / 2 : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn0 : n ≠ Finsupp.single 0 1 := by
      intro he
      have hlt := (mem_rectangularWindow _ n).mp hn 0
      simp [he] at hlt
    simp [seriesTerm, coeff_X, hn0]
  rw [hs, hr]
  norm_num

#print axioms MvPowerSeries.summable_norm_seriesTerm
#print axioms MvPowerSeries.abs_geometricSum_sub_rectangularSum_le
