/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.HendersonInverseInvEqSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Henderson's rules for the inverse numerator relationship matrix

On the pedigree with two unrelated founders and their child, the numerator relationship matrix
satisfies the tabular method, hence is invertible with the Henderson local-addition inverse;
the inverse entry at the child is `2`.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted
open WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted.Pedigree

namespace DomainsTest.Biology.StatisticalGenetics.HendersonInverseInvEqSum

/-- The sire function of the two-founder pedigree. -/
private def testSire : Fin 3 → Option (Fin 3) := ![none, none, some 0]

/-- The dam function of the two-founder pedigree. -/
private def testDam : Fin 3 → Option (Fin 3) := ![none, none, some 1]

/-- The two-founder pedigree: founders `0` and `1`, and their child `2`. -/
private def testPed : Pedigree 3 where
  sire := testSire
  dam := testDam
  sire_lt := by decide
  dam_lt := by decide
  sire_ne_dam := by decide

/-- The numerator relationship matrix of the two-founder pedigree. -/
private noncomputable def testA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 1/2; 0, 1, 1/2; 1/2, 1/2, 1]

/-- Entry `(0, 0)` of the test matrix. -/
private theorem testA00 : testA 0 0 = 1 := rfl

/-- Entry `(0, 1)` of the test matrix. -/
private theorem testA01 : testA 0 1 = 0 := rfl

/-- Entry `(0, 2)` of the test matrix. -/
private theorem testA02 : testA 0 2 = 1 / 2 := rfl

/-- Entry `(1, 0)` of the test matrix. -/
private theorem testA10 : testA 1 0 = 0 := rfl

/-- Entry `(1, 1)` of the test matrix. -/
private theorem testA11 : testA 1 1 = 1 := rfl

/-- Entry `(1, 2)` of the test matrix. -/
private theorem testA12 : testA 1 2 = 1 / 2 := rfl

/-- Entry `(2, 2)` of the test matrix. -/
private theorem testA22 : testA 2 2 = 1 := rfl

/-- Animal `0` has no known sire. -/
private theorem testSire0 : testPed.sire 0 = none := rfl

/-- Animal `1` has no known sire. -/
private theorem testSire1 : testPed.sire 1 = none := rfl

/-- The sire of animal `2` is animal `0`. -/
private theorem testSire2 : testPed.sire 2 = some 0 := rfl

/-- Animal `0` has no known dam. -/
private theorem testDam0 : testPed.dam 0 = none := rfl

/-- Animal `1` has no known dam. -/
private theorem testDam1 : testPed.dam 1 = none := rfl

/-- The dam of animal `2` is animal `1`. -/
private theorem testDam2 : testPed.dam 2 = some 1 := rfl

/-- The inbreeding coefficient of founder `0` is `0`. -/
private theorem testF0 : testPed.inbreeding testA 0 = 0 := rfl

/-- The inbreeding coefficient of founder `1` is `0`. -/
private theorem testF1 : testPed.inbreeding testA 1 = 0 := rfl

/-- The inbreeding coefficient of the child. -/
private theorem testF2 : testPed.inbreeding testA 2 = testA 0 1 / 2 := rfl

/-- The test matrix is the numerator relationship matrix of the test pedigree. -/
private theorem testA_tabular : testPed.IsTabular testA := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro j
    fin_cases j
    · change testA 0 0 = 1 + testPed.inbreeding testA 0
      rw [testA00, testF0]
      norm_num
    · change testA 1 1 = 1 + testPed.inbreeding testA 1
      rw [testA11, testF1]
      norm_num
    · change testA 2 2 = 1 + testPed.inbreeding testA 2
      rw [testA22, testF2, testA01]
      norm_num
  · intro i j h
    fin_cases i
    · fin_cases j
      · exact absurd h (by decide)
      · change testA 0 1 = (0 + 0) / 2
        rw [testA01]
        norm_num
      · change testA 0 2 = (testA 0 0 + testA 0 1) / 2
        rw [testA02, testA00, testA01]
        norm_num
    · fin_cases j
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · change testA 1 2 = (testA 1 0 + testA 1 1) / 2
        rw [testA12, testA10, testA11]
        norm_num
    · fin_cases j
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)

/-- The Mendelian variance of founder `0` is `1`. -/
private theorem testD0 : testPed.mendelianVar testA 0 = 1 := rfl

/-- The Mendelian variance of founder `1` is `1`. -/
private theorem testD1 : testPed.mendelianVar testA 1 = 1 := rfl

/-- The Mendelian variance of the child is `1/2`. -/
private theorem testD2 : testPed.mendelianVar testA 2 = 1 / 2 := by
  have e : testPed.mendelianVar testA 2 =
      1 / 2 - (testPed.inbreeding testA 0 + testPed.inbreeding testA 1) / 4 := rfl
  rw [e, testF0, testF1]
  norm_num

/-- Row `0` of `I - P` at column `2` is `0`. -/
private theorem testC02 : testPed.hendersonVec 0 2 = 0 := by
  unfold hendersonVec
  rw [Matrix.sub_apply, Matrix.one_apply]
  have eP : testPed.parentMatrix 0 2 =
      (if testPed.sire 0 = some 2 then (1/2:ℝ) else 0) +
        (if testPed.dam 0 = some 2 then 1/2 else 0) := rfl
  rw [eP, testSire0, testDam0, ite_eq_right (by decide : (0:Fin 3) ≠ 2)]
  simp

/-- Row `1` of `I - P` at column `2` is `0`. -/
private theorem testC12 : testPed.hendersonVec 1 2 = 0 := by
  unfold hendersonVec
  rw [Matrix.sub_apply, Matrix.one_apply]
  have eP : testPed.parentMatrix 1 2 =
      (if testPed.sire 1 = some 2 then (1/2:ℝ) else 0) +
        (if testPed.dam 1 = some 2 then 1/2 else 0) := rfl
  rw [eP, testSire1, testDam1, ite_eq_right (by decide : (1:Fin 3) ≠ 2)]
  simp

/-- Row `2` of `I - P` at column `2` is `1`. -/
private theorem testC22 : testPed.hendersonVec 2 2 = 1 := by
  unfold hendersonVec
  rw [Matrix.sub_apply, Matrix.one_apply]
  have eP : testPed.parentMatrix 2 2 =
      (if testPed.sire 2 = some 2 then (1/2:ℝ) else 0) +
        (if testPed.dam 2 = some 2 then 1/2 else 0) := rfl
  rw [eP, testSire2, testDam2, ite_eq_left rfl]
  simp

/-- The test matrix has nonzero determinant. -/
example : testA.det ≠ 0 :=
  isUnit_iff_ne_zero.mp (inv_eq_sum testPed testA testA_tabular).1

/-- On the two-founder pedigree, the inverse entry at the child is `2`. -/
example : (testA⁻¹) 2 2 = 2 := by
  have hInv := (inv_eq_sum testPed testA testA_tabular).2
  rw [hInv]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Fin.sum_univ_three]
  rw [testD0, testD1, testD2, testC02, testC12, testC22]
  norm_num

end DomainsTest.Biology.StatisticalGenetics.HendersonInverseInvEqSum
