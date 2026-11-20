/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity
import Code.Universality.IsingFermionicSquareCaratheodory





namespace StatMech.Universality

open Filter Metric Set Topology

noncomputable section


def meshScaleLinearField (k : Nat) (z : Complex) : Complex :=
  (Real.sqrt (k + 1 : Real) : Complex) * z




theorem meshScaleLinearField_local_norm_sub_sq_le
    (k : Nat) (z w : Complex)
    (hzw : dist z w ≤ 1 / (k + 1 : Real)) :
    ‖meshScaleLinearField k z - meshScaleLinearField k w‖ ^ 2 ≤
      dist z w := by
  have hk : 0 < (k + 1 : Real) := by positivity
  have hsqrt : Real.sqrt (k + 1 : Real) ^ 2 = (k + 1 : Real) :=
    Real.sq_sqrt hk.le
  have hdist : 0 ≤ dist z w := dist_nonneg
  have hmul : (k + 1 : Real) * dist z w ≤ 1 := by
    rw [le_div_iff₀ hk] at hzw
    nlinarith
  rw [show meshScaleLinearField k z - meshScaleLinearField k w =
      (Real.sqrt (k + 1 : Real) : Complex) * (z - w) by
        simp [meshScaleLinearField]; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ← dist_eq_norm]
  calc
    (Real.sqrt (k + 1 : Real) * dist z w) ^ 2 =
        (k + 1 : Real) * dist z w ^ 2 := by rw [mul_pow, hsqrt]
    _ ≤ dist z w := by nlinarith




theorem meshScaleLinearField_not_meshUniformCompactHolder :
    ¬ Nonempty
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
        meshScaleLinearField) := by
  rintro ⟨H⟩
  let K : Set Complex := {0, 1}
  have hK : IsCompact K := by
    exact (isCompact_singleton : IsCompact ({1} : Set Complex)).insert 0
  have hKU : K ⊆ fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
    simp [fkIsingExpandingBoundarySquareCaratheodoryApproximation]
  obtain ⟨C, alpha, _halpha, hholder⟩ := H.holder K hK hKU
  obtain ⟨n, hn⟩ := exists_nat_gt ((C : Real) ^ 2)
  have hsqrtGt : (C : Real) < Real.sqrt (n + 1 : Real) := by
    rw [Real.lt_sqrt (by positivity)]
    exact lt_of_lt_of_le hn (by exact_mod_cast Nat.le_add_right n 1)
  have hbound := (hholder n).dist_le (show (0 : Complex) ∈ K by simp [K])
    (show (1 : Complex) ∈ K by simp [K])
  have hle : Real.sqrt (n + 1 : Real) ≤ (C : Real) := by
    simpa [meshScaleLinearField, dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hbound
  exact (not_lt_of_ge hle) hsqrtGt

end

end StatMech.Universality
