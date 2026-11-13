/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib










namespace StatMech.FrontierA

open scoped BigOperators

noncomputable section

def gramVarianceCounterDiagonal (i : Fin 3) : Real :=
  if i.val = 0 then 1 / 4 else if i.val = 1 then 29 / 4 else 5 / 4


def gramVarianceCounterKernel (i j : Fin 3) : Real :=
  (if i.val = j.val then gramVarianceCounterDiagonal i else 0) + 1 / 4

def gramVarianceCounterMass (i : Fin 3) : Real :=
  ∑ j, gramVarianceCounterKernel j i

def gramVarianceCounterReflect (i : Fin 3) : Fin 3 :=
  ⟨2 - i.val, by omega⟩

def gramVarianceCounterValue (i : Fin 3) : Real :=
  if i.val = 0 then -2 else if i.val = 1 then 0 else 2

def gramVarianceCounterPlusWeight (i : Fin 3) : Real :=
  gramVarianceCounterMass i *
    (if i.val = 0 then 2 / 3 else if i.val = 1 then 1 else 3 / 2)

def gramVarianceCounterMinusWeight (i : Fin 3) : Real :=
  gramVarianceCounterMass i *
    (if i.val = 0 then 3 / 2 else if i.val = 1 then 1 else 2 / 3)

def finiteWeightedVariance {E : Type*} [Fintype E]
    (w X : E -> Real) : Real :=
  (∑ i, w i * X i ^ 2) / (∑ i, w i) -
    ((∑ i, w i * X i) / (∑ i, w i)) ^ 2

theorem gramVarianceCounterKernel_pos (i j : Fin 3) :
    0 < gramVarianceCounterKernel i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gramVarianceCounterKernel, gramVarianceCounterDiagonal]

theorem gramVarianceCounterKernel_symm (i j : Fin 3) :
    gramVarianceCounterKernel i j = gramVarianceCounterKernel j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gramVarianceCounterKernel, gramVarianceCounterDiagonal]



theorem gramVarianceCounterKernel_quadratic_nonneg (f : Fin 3 -> Real) :
    0 <= ∑ i, ∑ j,
      f i * gramVarianceCounterKernel i j * f j := by
  have h0 : 0 <= (f 0 + f 1 + f 2) ^ 2 := sq_nonneg _
  have h1 : 0 <= f 0 ^ 2 := sq_nonneg _
  have h2 : 0 <= f 1 ^ 2 := sq_nonneg _
  have h3 : 0 <= f 2 ^ 2 := sq_nonneg _
  simp only [Fin.sum_univ_succ]
  norm_num [gramVarianceCounterKernel, gramVarianceCounterDiagonal]
  nlinarith

@[simp] theorem gramVarianceCounterMass_zero :
    gramVarianceCounterMass 0 = 1 := by
  norm_num [gramVarianceCounterMass, gramVarianceCounterKernel,
    gramVarianceCounterDiagonal, Fin.sum_univ_succ]

@[simp] theorem gramVarianceCounterMass_one :
    gramVarianceCounterMass 1 = 8 := by
  norm_num [gramVarianceCounterMass, gramVarianceCounterKernel,
    gramVarianceCounterDiagonal, Fin.sum_univ_succ]

@[simp] theorem gramVarianceCounterMass_two :
    gramVarianceCounterMass 2 = 2 := by
  norm_num [gramVarianceCounterMass, gramVarianceCounterKernel,
    gramVarianceCounterDiagonal, Fin.sum_univ_succ]


theorem gramVarianceCounterMass_compl_ratio_mono
    {i j : Fin 3} (hij : i <= j) :
    gramVarianceCounterMass i *
        gramVarianceCounterMass (gramVarianceCounterReflect j) <=
      gramVarianceCounterMass j *
        gramVarianceCounterMass (gramVarianceCounterReflect i) := by
  fin_cases i <;> fin_cases j
  all_goals simp [gramVarianceCounterReflect, gramVarianceCounterMass,
    gramVarianceCounterKernel, gramVarianceCounterDiagonal,
    Fin.sum_univ_succ] at hij ⊢
  all_goals norm_num

theorem gramVarianceCounterPlusVariance_eq :
    finiteWeightedVariance gramVarianceCounterPlusWeight
      gramVarianceCounterValue = 192 / 175 := by
  norm_num [finiteWeightedVariance, gramVarianceCounterPlusWeight,
    gramVarianceCounterValue, Fin.sum_univ_succ]

theorem gramVarianceCounterMinusVariance_eq :
    finiteWeightedVariance gramVarianceCounterMinusWeight
      gramVarianceCounterValue = 4416 / 4225 := by
  norm_num [finiteWeightedVariance, gramVarianceCounterMinusWeight,
    gramVarianceCounterValue, Fin.sum_univ_succ]



theorem gramVarianceCounterMinusVariance_lt_plus :
    finiteWeightedVariance gramVarianceCounterMinusWeight
        gramVarianceCounterValue <
      finiteWeightedVariance gramVarianceCounterPlusWeight
        gramVarianceCounterValue := by
  rw [gramVarianceCounterPlusVariance_eq,
    gramVarianceCounterMinusVariance_eq]
  norm_num

end

end StatMech.FrontierA
