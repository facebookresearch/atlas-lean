/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientDoubleCount

/-! Finite tools for counting actual signed-short axes orthogonal to a given vector.

The count splits along the three actual short-label families, and orthogonality to an
actual signed-short axis becomes an exact integer equation once the matrix and short
coordinates of the vector are given by integer numerators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Contraction of a diagonal matrix against a vector. -/
theorem generatedFeasibleAmbient_diagonal_contraction (v d : Fin 24 → ℝ) :
    axisMatrixContraction v (Matrix.diagonal d) = ∑ i, d i * v i ^ 2 := by
  unfold axisMatrixContraction
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.diagonal_apply_eq]
    ring
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

/-- The squared actual physical coordinate is the squared integral coordinate over eight. -/
theorem generatedFeasibleAmbient_shortVector_sq (r : GriessShortIndex) (i : Fin 24) :
    griessShortVector r i ^ 2 = (griessShortIntegral r i : ℝ) ^ 2 / 8 := by
  have hs : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  rw [griessShortVector, div_pow, hs]

/-- The product of two actual physical coordinates is the integral product over eight. -/
theorem generatedFeasibleAmbient_shortVector_mul (r s : GriessShortIndex) (i j : Fin 24) :
    griessShortVector r i * griessShortVector s j =
      (griessShortIntegral r i : ℝ) * griessShortIntegral s j / 8 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  rw [griessShortVector, griessShortVector, div_mul_div_comm, hs]

/-- The orthogonal axis count as the cardinality of an explicit finite filter. -/
theorem generatedFeasibleAmbientAxisZeroCount_eq_card (x : GriessSpace) :
    generatedFeasibleAmbientAxisZeroCount x =
      (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
        griessForm (conwayShortAxis p.1 p.2) x = 0).card := by
  classical
  unfold generatedFeasibleAmbientAxisZeroCount
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq, Finset.coe_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- A filter over the actual signed-short addresses splits along the three label families. -/
theorem generatedFeasibleAmbient_short_filter_card (P : GriessShortIndex → ZMod 2 → Prop)
    [∀ r c, Decidable (P r c)] :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 => P p.1 p.2).card =
      (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 => P (Sum.inl q.1) q.2).card +
      (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
        P (Sum.inr (Sum.inl q.1)) q.2).card +
      (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
        P (Sum.inr (Sum.inr q.1)) q.2).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_sum_type]
  ring

/-- Exact integer criterion for orthogonality to an actual signed-short axis. If the
matrix coordinates are `N / DM` and the short coordinate at `r` is `n / DS`, then
orthogonality is `DS · uᵀNu = 32 · DM · (±1) · n` for the integral short vector `u`. -/
theorem generatedFeasibleAmbient_axis_form_eq_zero_iff_int (r : GriessShortIndex)
    (c : ZMod 2) (x : GriessSpace) (N : Fin 24 → Fin 24 → ℤ) (n : ℤ) (DM DS : ℕ)
    (hDM : 0 < DM) (hDS : 0 < DS)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = (N i j : ℝ) / DM)
    (hS : (griessConwayEncode x).2.1 r = (n : ℝ) / DS) :
    griessForm (conwayShortAxis r c) x = 0 ↔
      (DS : ℤ) * (∑ i, ∑ j, griessShortIntegral r i * N i j * griessShortIntegral r j) =
        32 * DM * (if c = 0 then 1 else -1) * n := by
  rw [generatedFeasibleAmbient_axis_form, hS]
  have hc : axisMatrixContraction (griessShortVector r) (griessConwayEncode x).1 =
      ((∑ i, ∑ j, griessShortIntegral r i * N i j * griessShortIntegral r j : ℤ) : ℝ) /
        (8 * DM) := by
    unfold axisMatrixContraction
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    calc griessShortVector r i * (griessConwayEncode x).1 i j * griessShortVector r j
        = (N i j : ℝ) / DM * (griessShortVector r i * griessShortVector r j) := by
          rw [hM]
          ring
      _ = (N i j : ℝ) / DM *
          ((griessShortIntegral r i : ℝ) * griessShortIntegral r j / 8) := by
          rw [generatedFeasibleAmbient_shortVector_mul]
      _ = (griessShortIntegral r i : ℝ) * N i j * griessShortIntegral r j / (8 * DM) := by
          ring
  have hq : qSign c = ((if c = 0 then 1 else -1 : ℤ) : ℝ) := by
    unfold qSign
    split_ifs <;> simp
  rw [hc, hq]
  generalize (∑ i, ∑ j, griessShortIntegral r i * N i j * griessShortIntegral r j) = Q
  generalize (if c = 0 then 1 else -1 : ℤ) = σ
  have hDM' : (DM : ℝ) ≠ 0 := by exact_mod_cast hDM.ne'
  have hDS' : (DS : ℝ) ≠ 0 := by exact_mod_cast hDS.ne'
  have key : 2 * ((Q : ℝ) / (8 * DM)) - 8 * (σ : ℝ) * ((n : ℝ) / DS) =
      ((DS : ℝ) * Q - 32 * DM * σ * n) / (4 * DM * DS) := by
    field_simp
    ring
  have hden : (4 * (DM : ℝ) * DS) ≠ 0 := by positivity
  rw [key, div_eq_zero_iff, sub_eq_zero]
  simp only [hden, or_false]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
