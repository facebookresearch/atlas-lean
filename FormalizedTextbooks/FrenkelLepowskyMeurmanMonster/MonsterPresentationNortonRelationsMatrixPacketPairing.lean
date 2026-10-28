/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact raw matrix pairings for the finite sparse Norton half-word calculation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsDyadicPairing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_product_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ i, (0 : ℝ) * x i) = 0 := by
  simp only [zero_mul, Finset.sum_const_zero]

private theorem real_zero_sum {ι : Type*} [Fintype ι] : (∑ _i : ι, (0 : ℝ)) = 0 :=
  Finset.sum_const_zero

/-- A genuine pure-matrix vector pairs only with the full physical matrix constituent. -/
theorem monsterNortonForm_pure_matrix_raw (A B : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ)
    (ha : ∀ i j, A i j = A j i) (hb : ∀ i j, B i j = B j i) :
    griessForm (griessConwayDecode (A, (0, 0))) (griessConwayDecode (B, (X, T))) =
      ∑ i, ∑ j, A i j * B i j := by
  rw [monsterNortonForm_raw_coordinates, griessConwayEncode_decode _ ha,
    griessConwayEncode_decode _ hb]
  simp only [Pi.zero_apply]
  rw [zero_product_sum X]
  simp_rw [zero_product_sum (fun i : Fin 24 => T _ i)]
  rw [real_zero_sum]
  ring

/-- Pairing with a genuine diagonal matrix reads only its original diagonal coordinates. -/
theorem monsterNortonForm_pure_matrix_diagonal (A : Matrix (Fin 24) (Fin 24) ℝ)
    (b : Fin 24 → ℝ) (X : GriessShortIndex → ℝ)
    (ha : ∀ i j, A i j = A j i) :
    griessForm (griessConwayDecode (A, (0, 0)))
      (griessConwayDecode (Matrix.diagonal b, (X, 0))) = ∑ i, A i i * b i := by
  rw [monsterNortonForm_pure_matrix_raw A _ X 0 ha]
  · simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  · intro i j
    simp only [Matrix.diagonal_apply]
    by_cases h : i = j <;> simp [h, Ne.symm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
