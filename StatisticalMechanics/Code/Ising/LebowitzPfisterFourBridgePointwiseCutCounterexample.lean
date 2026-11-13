/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample















open Finset

namespace StatMech.Ising

noncomputable section


def fourBridgePointwiseCutCounterexampleWeight
    (P : Finset (Fin 4)) : Nat :=
  if (∑ i ∈ P, 2 ^ i.val) ∈ ({1, 3, 15} : Finset Nat) then 1 else 0


theorem fourBridgePointwiseCutCounterexampleWeight_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgePointwiseCutCounterexampleWeight P) = 3 := by
  decide


theorem fourBridgePointwiseCutCounterexampleWeight_logSupermodular :
    ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset,
        fourBridgePointwiseCutCounterexampleWeight P *
            fourBridgePointwiseCutCounterexampleWeight Q <=
          fourBridgePointwiseCutCounterexampleWeight (P ∩ Q) *
            fourBridgePointwiseCutCounterexampleWeight (P ∪ Q) := by
  decide


theorem fourBridgePointwiseCutCounterexampleWeight_complementRatio :
    ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset,
        P ⊆ Q ->
          fourBridgePointwiseCutCounterexampleWeight P *
              fourBridgePointwiseCutCounterexampleWeight
                ((Finset.univ : Finset (Fin 4)) \ Q) <=
            fourBridgePointwiseCutCounterexampleWeight Q *
              fourBridgePointwiseCutCounterexampleWeight
                ((Finset.univ : Finset (Fin 4)) \ P) := by
  decide


def fourBridgePointwiseCutCounterexampleMass
    (P : Finset (Fin 4)) : Real :=
  fourBridgePointwiseCutCounterexampleWeight P / 3

theorem fourBridgePointwiseCutCounterexampleMass_nonneg
    (P : Finset (Fin 4)) :
    0 <= fourBridgePointwiseCutCounterexampleMass P := by
  unfold fourBridgePointwiseCutCounterexampleMass
  positivity

theorem fourBridgePointwiseCutCounterexampleMass_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgePointwiseCutCounterexampleMass P) = 1 := by
  have hReal :
      (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (fourBridgePointwiseCutCounterexampleWeight P : Real)) = 3 := by
    exact_mod_cast fourBridgePointwiseCutCounterexampleWeight_sum
  unfold fourBridgePointwiseCutCounterexampleMass
  rw [← Finset.sum_div, hReal]
  norm_num


theorem fourBridgePointwiseCutCounterexampleMass_logSupermodular
    {P Q : Finset (Fin 4)}
    (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset) :
    fourBridgePointwiseCutCounterexampleMass P *
        fourBridgePointwiseCutCounterexampleMass Q <=
      fourBridgePointwiseCutCounterexampleMass (P ∩ Q) *
        fourBridgePointwiseCutCounterexampleMass (P ∪ Q) := by
  have hNat := fourBridgePointwiseCutCounterexampleWeight_logSupermodular
    P hP Q hQ
  have hReal :
      (fourBridgePointwiseCutCounterexampleWeight P : Real) *
          fourBridgePointwiseCutCounterexampleWeight Q <=
        (fourBridgePointwiseCutCounterexampleWeight (P ∩ Q) : Real) *
          fourBridgePointwiseCutCounterexampleWeight (P ∪ Q) := by
    exact_mod_cast hNat
  unfold fourBridgePointwiseCutCounterexampleMass
  nlinarith


theorem fourBridgePointwiseCutCounterexampleMass_complementRatio
    {P Q : Finset (Fin 4)}
    (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hPQ : P ⊆ Q) :
    fourBridgePointwiseCutCounterexampleMass P *
        fourBridgePointwiseCutCounterexampleMass
          ((Finset.univ : Finset (Fin 4)) \ Q) <=
      fourBridgePointwiseCutCounterexampleMass Q *
        fourBridgePointwiseCutCounterexampleMass
          ((Finset.univ : Finset (Fin 4)) \ P) := by
  have hNat := fourBridgePointwiseCutCounterexampleWeight_complementRatio
    P hP Q hQ hPQ
  have hReal :
      (fourBridgePointwiseCutCounterexampleWeight P : Real) *
          fourBridgePointwiseCutCounterexampleWeight
            ((Finset.univ : Finset (Fin 4)) \ Q) <=
        (fourBridgePointwiseCutCounterexampleWeight Q : Real) *
          fourBridgePointwiseCutCounterexampleWeight
            ((Finset.univ : Finset (Fin 4)) \ P) := by
    exact_mod_cast hNat
  unfold fourBridgePointwiseCutCounterexampleMass
  nlinarith


theorem fourBridgePointwiseCutCounterexample_rankWeights :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 0 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 0 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 1 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 2 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 3 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 0 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 4 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 := by
  decide

def fourBridgePointwiseCutCounterexampleA : Real := 2 / 3
def fourBridgePointwiseCutCounterexampleB : Real := 4 / 3
def fourBridgePointwiseCutCounterexampleC : Real := 2
def fourBridgePointwiseCutCounterexampleD : Real := 1 / 3



theorem fourBridgePointwiseCutCounterexample_fourierRecovery :
    let p0 : Real := 0
    let p1 : Real := 1 / 3
    let p2 : Real := 1 / 3
    let p3 : Real := 0
    let p4 : Real := 1 / 3
    fourBridgePointwiseCutCounterexampleA = 4 * (p4 - p0) + 2 * (p3 - p1) ∧
      fourBridgePointwiseCutCounterexampleB = 6 * (p0 + p4) - 2 * p2 ∧
      fourBridgePointwiseCutCounterexampleC = 4 * (p4 - p0) + 2 * (p1 - p3) ∧
      fourBridgePointwiseCutCounterexampleD = p0 - p1 + p2 - p3 + p4 := by
  norm_num [fourBridgePointwiseCutCounterexampleA,
    fourBridgePointwiseCutCounterexampleB,
    fourBridgePointwiseCutCounterexampleC,
    fourBridgePointwiseCutCounterexampleD]



theorem fourBridgePointwiseCutCounterexample_numerator_eq :
    fourBridgeSecondMiddleNumerator
      fourBridgePointwiseCutCounterexampleA
      fourBridgePointwiseCutCounterexampleB
      fourBridgePointwiseCutCounterexampleC
      fourBridgePointwiseCutCounterexampleD = -(64 / 9) := by
  norm_num [fourBridgeSecondMiddleNumerator,
    fourBridgePointwiseCutCounterexampleA,
    fourBridgePointwiseCutCounterexampleB,
    fourBridgePointwiseCutCounterexampleC,
    fourBridgePointwiseCutCounterexampleD]

theorem fourBridgePointwiseCutCounterexample_numerator_neg :
    fourBridgeSecondMiddleNumerator
      fourBridgePointwiseCutCounterexampleA
      fourBridgePointwiseCutCounterexampleB
      fourBridgePointwiseCutCounterexampleC
      fourBridgePointwiseCutCounterexampleD < 0 := by
  rw [fourBridgePointwiseCutCounterexample_numerator_eq]
  norm_num


theorem fourBridgePointwiseCutCounterexample_not_strictlyPositive :
    fourBridgePointwiseCutCounterexampleMass (∅ : Finset (Fin 4)) = 0 := by
  norm_num [fourBridgePointwiseCutCounterexampleMass,
    fourBridgePointwiseCutCounterexampleWeight]

end

end StatMech.Ising
