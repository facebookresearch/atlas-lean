/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
import Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
















open Finset

namespace StatMech.Ising

noncomputable section



def fourBridgeSecondMiddleCutCounterexampleWeight
    (P : Finset (Fin 4)) : Nat :=
  match ∑ i ∈ P, 2 ^ i.val with
  | 0 => 16
  | 1 => 32
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 5 => 8
  | 6 => 1
  | 7 => 8
  | 8 => 512
  | 9 => 1024
  | 10 => 64
  | 11 => 256
  | 12 => 64
  | 13 => 256
  | 14 => 64
  | 15 => 512
  | _ => 0


theorem fourBridgeSecondMiddleCutCounterexampleWeight_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgeSecondMiddleCutCounterexampleWeight P) = 2824 := by
  decide


theorem fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular :
    ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset,
        fourBridgeSecondMiddleCutCounterexampleWeight P *
            fourBridgeSecondMiddleCutCounterexampleWeight Q <=
          fourBridgeSecondMiddleCutCounterexampleWeight (P ∩ Q) *
            fourBridgeSecondMiddleCutCounterexampleWeight (P ∪ Q) := by
  decide


def fourBridgeSecondMiddleCutCounterexampleMass
    (P : Finset (Fin 4)) : Real :=
  fourBridgeSecondMiddleCutCounterexampleWeight P / 2824

theorem fourBridgeSecondMiddleCutCounterexampleMass_nonneg
    (P : Finset (Fin 4)) :
    0 <= fourBridgeSecondMiddleCutCounterexampleMass P := by
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  positivity

theorem fourBridgeSecondMiddleCutCounterexampleMass_sum :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
      fourBridgeSecondMiddleCutCounterexampleMass P) = 1 := by
  have hReal :
      (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        (fourBridgeSecondMiddleCutCounterexampleWeight P : Real)) = 2824 := by
    exact_mod_cast fourBridgeSecondMiddleCutCounterexampleWeight_sum
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  rw [← Finset.sum_div, hReal]
  norm_num


theorem fourBridgeSecondMiddleCutCounterexampleMass_logSupermodular
    {P Q : Finset (Fin 4)}
    (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
    (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset) :
    fourBridgeSecondMiddleCutCounterexampleMass P *
        fourBridgeSecondMiddleCutCounterexampleMass Q <=
      fourBridgeSecondMiddleCutCounterexampleMass (P ∩ Q) *
        fourBridgeSecondMiddleCutCounterexampleMass (P ∪ Q) := by
  have hNat := fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular
    P hP Q hQ
  have hReal :
      (fourBridgeSecondMiddleCutCounterexampleWeight P : Real) *
          fourBridgeSecondMiddleCutCounterexampleWeight Q <=
        (fourBridgeSecondMiddleCutCounterexampleWeight (P ∩ Q) : Real) *
          fourBridgeSecondMiddleCutCounterexampleWeight (P ∪ Q) := by
    exact_mod_cast hNat
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  nlinarith


theorem fourBridgeSecondMiddleCutCounterexample_rankWeights :
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 0 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 16 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 1 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 547 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 2 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 1165 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 3 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 584 ∧
    (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset,
        if P.card = 4 then
          fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 512 := by
  decide


def fourBridgeSecondMiddleCutCounterexampleA : Real := 1029 / 1412
def fourBridgeSecondMiddleCutCounterexampleB : Real := 419 / 1412
def fourBridgeSecondMiddleCutCounterexampleC : Real := 955 / 1412
def fourBridgeSecondMiddleCutCounterexampleD : Real := 281 / 1412



theorem fourBridgeSecondMiddleCutCounterexample_fourierRecovery :
    let p0 : Real := 16 / 2824
    let p1 : Real := 547 / 2824
    let p2 : Real := 1165 / 2824
    let p3 : Real := 584 / 2824
    let p4 : Real := 512 / 2824
    fourBridgeSecondMiddleCutCounterexampleA =
        4 * (p4 - p0) + 2 * (p3 - p1) ∧
      fourBridgeSecondMiddleCutCounterexampleB =
        6 * (p0 + p4) - 2 * p2 ∧
      fourBridgeSecondMiddleCutCounterexampleC =
        4 * (p4 - p0) + 2 * (p1 - p3) ∧
      fourBridgeSecondMiddleCutCounterexampleD =
        p0 - p1 + p2 - p3 + p4 := by
  norm_num [fourBridgeSecondMiddleCutCounterexampleA,
    fourBridgeSecondMiddleCutCounterexampleB,
    fourBridgeSecondMiddleCutCounterexampleC,
    fourBridgeSecondMiddleCutCounterexampleD]



theorem fourBridgeSecondMiddleCutCounterexample_scalarBounds :
    let a := fourBridgeSecondMiddleCutCounterexampleA
    let b := fourBridgeSecondMiddleCutCounterexampleB
    let c := fourBridgeSecondMiddleCutCounterexampleC
    let d := fourBridgeSecondMiddleCutCounterexampleD
    0 <= a ∧ a <= 2 ∧ 0 <= b ∧ b <= 6 ∧ 0 <= c ∧ c <= 4 ∧
      0 <= d ∧ d <= 1 ∧ a * d <= c ∧ c * d <= a ∧
      a * c <= 2 * b + 4 * d ∧ a * b <= 3 * (a + c) ∧
      b * c <= 3 * (a + c) ∧ 3 * a <= 6 + b ∧
      3 * c <= 6 + b ∧ b ^ 2 <= 5 + 6 * d := by
  norm_num [fourBridgeSecondMiddleCutCounterexampleA,
    fourBridgeSecondMiddleCutCounterexampleB,
    fourBridgeSecondMiddleCutCounterexampleC,
    fourBridgeSecondMiddleCutCounterexampleD]


theorem fourBridgeSecondMiddleCutCounterexample_rankQuadraticCuts :
    let p0 : Real := 16 / 2824
    let p1 : Real := 547 / 2824
    let p2 : Real := 1165 / 2824
    let p3 : Real := 584 / 2824
    let p4 : Real := 512 / 2824
    p1 ^ 2 <= p1 + 2 * p0 * p2 ∧
      p3 ^ 2 <= p3 + 2 * p2 * p4 ∧
      p0 * p3 <= p1 * p4 := by
  norm_num



theorem fourBridgeSecondMiddleCutCounterexample_nestedSingletonPairCut :
    let M : Finset (Fin 4) := Finset.univ
    let w := fourBridgeSecondMiddleCutCounterexampleWeight
    (w {0} + w {1}) * w (M \ {0, 1}) +
        (w {0} + w {2}) * w (M \ {0, 2}) +
        (w {0} + w {3}) * w (M \ {0, 3}) +
        (w {1} + w {2}) * w (M \ {1, 2}) +
        (w {1} + w {3}) * w (M \ {1, 3}) +
        (w {2} + w {3}) * w (M \ {2, 3}) <=
      w {0, 1} * (w (M \ {0}) + w (M \ {1})) +
        w {0, 2} * (w (M \ {0}) + w (M \ {2})) +
        w {0, 3} * (w (M \ {0}) + w (M \ {3})) +
        w {1, 2} * (w (M \ {1}) + w (M \ {2})) +
        w {1, 3} * (w (M \ {1}) + w (M \ {3})) +
        w {2, 3} * (w (M \ {2}) + w (M \ {3})) := by
  decide


theorem fourBridgeSecondMiddleCutCounterexample_numerator_neg :
    fourBridgeSecondMiddleNumerator
      fourBridgeSecondMiddleCutCounterexampleA
      fourBridgeSecondMiddleCutCounterexampleB
      fourBridgeSecondMiddleCutCounterexampleC
      fourBridgeSecondMiddleCutCounterexampleD < 0 := by
  norm_num [fourBridgeSecondMiddleNumerator,
    fourBridgeSecondMiddleCutCounterexampleA,
    fourBridgeSecondMiddleCutCounterexampleB,
    fourBridgeSecondMiddleCutCounterexampleC,
    fourBridgeSecondMiddleCutCounterexampleD]



theorem fourBridgeSecondMiddleCutCounterexample_productFace_numerator_pos :
    0 < fourBridgeSecondMiddleNumerator
      fourBridgeSecondMiddleCutCounterexampleA
      fourBridgeSecondMiddleCutCounterexampleB
      (fourBridgeSecondMiddleCutCounterexampleA *
        fourBridgeSecondMiddleCutCounterexampleD)
      fourBridgeSecondMiddleCutCounterexampleD := by
  norm_num [fourBridgeSecondMiddleNumerator,
    fourBridgeSecondMiddleCutCounterexampleA,
    fourBridgeSecondMiddleCutCounterexampleB,
    fourBridgeSecondMiddleCutCounterexampleD]




theorem fourBridgeSecondMiddleCutCounterexample_no_nonnegative_upperFace
    {U : Real}
    (hU : fourBridgeSecondMiddleCutCounterexampleC <= U) :
    fourBridgeSecondMiddleNumerator
      fourBridgeSecondMiddleCutCounterexampleA
      fourBridgeSecondMiddleCutCounterexampleB U
      fourBridgeSecondMiddleCutCounterexampleD < 0 := by
  let a := fourBridgeSecondMiddleCutCounterexampleA
  let b := fourBridgeSecondMiddleCutCounterexampleB
  let c := fourBridgeSecondMiddleCutCounterexampleC
  let d := fourBridgeSecondMiddleCutCounterexampleD
  let slope := 3 * a ^ 2 * b - 21 * a ^ 2 + b ^ 2 - b + 9 * d - 15
  have ha : 0 <= a := by
    norm_num [a, fourBridgeSecondMiddleCutCounterexampleA]
  have hslope : slope - 18 * a * c < 0 := by
    norm_num [slope, a, b, c, d,
      fourBridgeSecondMiddleCutCounterexampleA,
      fourBridgeSecondMiddleCutCounterexampleB,
      fourBridgeSecondMiddleCutCounterexampleC,
      fourBridgeSecondMiddleCutCounterexampleD]
  have hUc : c <= U := by simpa only [c] using hU
  have hbracket : slope - 9 * a * (U + c) <= 0 := by
    have hmul := mul_nonneg ha (sub_nonneg.mpr hUc)
    nlinarith
  have hprod : (U - c) * (slope - 9 * a * (U + c)) <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hUc) hbracket
  have hid :
      fourBridgeSecondMiddleNumerator a b U d -
          fourBridgeSecondMiddleNumerator a b c d =
        (U - c) * (slope - 9 * a * (U + c)) := by
    dsimp only [slope]
    unfold fourBridgeSecondMiddleNumerator
    ring
  have hNc : fourBridgeSecondMiddleNumerator a b c d < 0 := by
    simpa only [a, b, c, d] using
      fourBridgeSecondMiddleCutCounterexample_numerator_neg
  simpa only [a, b, d] using (show
    fourBridgeSecondMiddleNumerator a b U d < 0 by nlinarith)




theorem fourBridgeSecondMiddleCutCounterexample_violates_pointwiseComplementRatio :
    let M : Finset (Fin 4) := Finset.univ
    let mu := fourBridgeSecondMiddleCutCounterexampleMass
    mu {1} * mu M < mu ∅ * mu (M \ {1}) := by
  have hsingle :
      fourBridgeSecondMiddleCutCounterexampleWeight {(1 : Fin 4)} = 1 := by
    decide
  have hfull :
      fourBridgeSecondMiddleCutCounterexampleWeight
        (Finset.univ : Finset (Fin 4)) = 512 := by
    decide
  have hempty :
      fourBridgeSecondMiddleCutCounterexampleWeight
        (∅ : Finset (Fin 4)) = 16 := by
    decide
  have hcosingle :
      fourBridgeSecondMiddleCutCounterexampleWeight
        ((Finset.univ : Finset (Fin 4)) \ {1}) = 256 := by
    decide
  dsimp only
  unfold fourBridgeSecondMiddleCutCounterexampleMass
  rw [hsingle, hfull, hempty, hcosingle]
  norm_num

end

end StatMech.Ising
