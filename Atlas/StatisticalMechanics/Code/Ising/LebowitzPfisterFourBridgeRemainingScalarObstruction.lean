/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSecondMiddleLowRank











namespace StatMech.Ising

noncomputable section



def FourBridgeEstablishedAggregateRegion (a b c d : Real) : Prop :=
  0 <= a ∧ a <= 4 ∧ 0 <= b ∧ b <= 6 ∧ 0 <= c ∧ c <= 4 ∧
  0 <= d ∧ d <= 1 ∧
  a ^ 3 - 3 * a * b - a + 3 * c <= 0 ∧
  a * d <= c ∧ c * d <= a ∧ a * c <= 2 * b + 4 * d ∧
  a * b <= 3 * (a + c) ∧ b * c <= 3 * (a + c) ∧
  3 * a <= 6 + b ∧ 3 * c <= 6 + b ∧ b ^ 2 <= 5 * b + 6 * d ∧
  0 <= fourBridgeRankMass a b c d 0 ∧
  0 <= fourBridgeRankMass a b c d 1 ∧
  0 <= fourBridgeRankMass a b c d 2 ∧
  0 <= fourBridgeRankMass a b c d 3 ∧
  0 <= fourBridgeRankMass a b c d 4 ∧
  fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 <=
    fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4 ∧
  fourBridgeRankMass a b c d 1 ^ 2 <=
    fourBridgeRankMass a b c d 1 +
      2 * fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 2 ∧
  fourBridgeRankMass a b c d 3 ^ 2 <=
    fourBridgeRankMass a b c d 3 +
      2 * fourBridgeRankMass a b c d 2 * fourBridgeRankMass a b c d 4

def fourBridgeRemainingCounterexampleA : Real := 8 / 5
def fourBridgeRemainingCounterexampleB : Real := 25 / 8
def fourBridgeRemainingCounterexampleC : Real := 64 / 25
def fourBridgeRemainingCounterexampleD : Real := 1 / 20


theorem fourBridgeRemainingCounterexample_mem_establishedAggregateRegion :
    FourBridgeEstablishedAggregateRegion
      fourBridgeRemainingCounterexampleA
      fourBridgeRemainingCounterexampleB
      fourBridgeRemainingCounterexampleC
      fourBridgeRemainingCounterexampleD := by
  norm_num [FourBridgeEstablishedAggregateRegion,
    fourBridgeRemainingCounterexampleA, fourBridgeRemainingCounterexampleB,
    fourBridgeRemainingCounterexampleC, fourBridgeRemainingCounterexampleD,
    fourBridgeRankMass]


theorem fourBridgeRemainingCounterexample_closed_coefficients_nonpos :
    fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 0 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 1 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 2 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 5 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 6 <= 0 := by
  norm_num [fourBridgeVarianceSkewBernsteinCoeff,
    fourBridgeRemainingCounterexampleA, fourBridgeRemainingCounterexampleB,
    fourBridgeRemainingCounterexampleC, fourBridgeRemainingCounterexampleD]



theorem fourBridgeRemainingCounterexample_middle_three_four_pos :
    0 < fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 3 ∧
      0 < fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 4 := by
  norm_num [fourBridgeVarianceSkewBernsteinCoeff,
    fourBridgeRemainingCounterexampleA, fourBridgeRemainingCounterexampleB,
    fourBridgeRemainingCounterexampleC, fourBridgeRemainingCounterexampleD]

def fourBridgeSkewCounterexampleA : Real := 2
def fourBridgeSkewCounterexampleB : Real := 317 / 100
def fourBridgeSkewCounterexampleC : Real := 9 / 4
def fourBridgeSkewCounterexampleD : Real := 2 / 25


theorem fourBridgeSkewCounterexample_mem_establishedAggregateRegion :
    FourBridgeEstablishedAggregateRegion
      fourBridgeSkewCounterexampleA fourBridgeSkewCounterexampleB
      fourBridgeSkewCounterexampleC fourBridgeSkewCounterexampleD := by
  norm_num [FourBridgeEstablishedAggregateRegion,
    fourBridgeSkewCounterexampleA, fourBridgeSkewCounterexampleB,
    fourBridgeSkewCounterexampleC, fourBridgeSkewCounterexampleD,
    fourBridgeRankMass]




theorem fourBridgeSkewCounterexample_polynomial_pos :
    0 < fourBridgeVarianceSkewPolynomial
      (9 / 10) fourBridgeSkewCounterexampleA fourBridgeSkewCounterexampleB
      fourBridgeSkewCounterexampleC fourBridgeSkewCounterexampleD := by
  norm_num [fourBridgeVarianceSkewPolynomial,
    fourBridgeSkewCounterexampleA, fourBridgeSkewCounterexampleB,
    fourBridgeSkewCounterexampleC, fourBridgeSkewCounterexampleD]

end

end StatMech.Ising
