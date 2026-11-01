/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sparse integer transport under the genuine inverse Norton compact numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactInverseIntegerBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse numerator preserves finite integer linear combinations. -/
theorem monsterNortonUCompactInverseNumerator_sum {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (v : ι → NortonUIntegerVector) :
    monsterNortonUCompactInverseNumerator (∑ a : ι, c a • v a) =
      ∑ a : ι, c a • monsterNortonUCompactInverseNumerator (v a) := by
  funext n
  simp only [monsterNortonUCompactInverseNumerator, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerG, nortonUIntegerQ,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro g _
  ring

/-- Sparse vectors transport by their input labels and the sixty-four genuine shifts. -/
theorem monsterNortonUCompactInverseNumerator_sparse {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (u : ι → Fin 4096) :
    monsterNortonUCompactInverseNumerator
      (∑ a : ι, c a • (Pi.single (u a) 1 : NortonUIntegerVector)) =
      -(∑ a : ι, ∑ g : XiGrayIndex,
        (c a * monsterNortonUCompactInverseBasisSign (golayLabelCoefficients (u a)) g) •
          (Pi.single (nortonUIntegerLabel
            (monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients (u a)) g)) 1 :
              NortonUIntegerVector)) := by
  rw [monsterNortonUCompactInverseNumerator_sum]
  simp only [monsterNortonUCompactInverseNumerator_basis, smul_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun v : NortonUIntegerVector => -v)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [smul_smul]

/-- Outside the actual sparse transition labels every inverse numerator coordinate is zero. -/
theorem monsterNortonUCompactInverseNumerator_sparse_zero {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (u : ι → Fin 4096) (n : Fin 4096)
    (hn : ∀ a : ι, ∀ g : XiGrayIndex, n ≠ nortonUIntegerLabel
      (monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients (u a)) g)) :
    monsterNortonUCompactInverseNumerator
      (∑ a : ι, c a • (Pi.single (u a) 1 : NortonUIntegerVector)) n = 0 := by
  rw [monsterNortonUCompactInverseNumerator_sparse]
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
