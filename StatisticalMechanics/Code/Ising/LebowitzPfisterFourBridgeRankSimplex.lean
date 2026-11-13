/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeFirstMiddle









namespace StatMech.Ising

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem fourBridge_rankMass_recover_one (a b c d : Real) :
    a = 4 * (fourBridgeRankMass a b c d 4 -
          fourBridgeRankMass a b c d 0) +
        2 * (fourBridgeRankMass a b c d 3 -
          fourBridgeRankMass a b c d 1) := by
  simp only [fourBridgeRankMass]
  ring


theorem fourBridge_rankMass_recover_two (a b c d : Real) :
    b = 6 * (fourBridgeRankMass a b c d 0 +
          fourBridgeRankMass a b c d 4) -
        2 * fourBridgeRankMass a b c d 2 := by
  simp only [fourBridgeRankMass]
  ring


theorem fourBridge_rankMass_recover_three (a b c d : Real) :
    c = 4 * (fourBridgeRankMass a b c d 4 -
          fourBridgeRankMass a b c d 0) +
        2 * (fourBridgeRankMass a b c d 1 -
          fourBridgeRankMass a b c d 3) := by
  simp only [fourBridgeRankMass]
  ring


theorem fourBridge_rankMass_recover_four (a b c d : Real) :
    d = fourBridgeRankMass a b c d 0 -
        fourBridgeRankMass a b c d 1 +
        fourBridgeRankMass a b c d 2 -
        fourBridgeRankMass a b c d 3 +
        fourBridgeRankMass a b c d 4 := by
  simp only [fourBridgeRankMass]
  ring


theorem fourBridgeRankMass_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V)
    (i : Fin 5) :
    0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) i := by
  fin_cases i
  · change 0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 0
    rw [← fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero]
    exact fourBridgeAgreementSpinMass_nonneg G J hf w x y z (-4)
  · change 0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 1
    rw [← fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one]
    exact fourBridgeAgreementSpinMass_nonneg G J hf w x y z (-2)
  · change 0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 2
    exact fourBridgeRankMass_two_nonneg G J hf w x y z
  · change 0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 3
    rw [← fourBridgeAgreementSpinMass_two_eq_rankMass_three]
    exact fourBridgeAgreementSpinMass_nonneg G J hf w x y z 2
  · change 0 <= fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 4
    rw [← fourBridgeAgreementSpinMass_four_eq_rankMass_four]
    exact fourBridgeAgreementSpinMass_nonneg G J hf w x y z 4


theorem fourBridgeRankMass_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V)
    (i : Fin 5) :
    fourBridgeRankMass
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) i <= 1 := by
  let p := fourBridgeRankMass
    (fourBridgeOneCoeff G J hf w x y z)
    (fourBridgeTwoCoeff G J hf w x y z)
    (fourBridgeThreeCoeff G J hf w x y z)
    (fourBridgeFourCoeff G J hf w x y z)
  have hsum : p 0 + p 1 + p 2 + p 3 + p 4 = 1 := by
    exact fourBridgeRankMass_sum _ _ _ _
  have h0 : 0 <= p 0 := fourBridgeRankMass_nonneg G J hf w x y z 0
  have h1 : 0 <= p 1 := fourBridgeRankMass_nonneg G J hf w x y z 1
  have h2 : 0 <= p 2 := fourBridgeRankMass_nonneg G J hf w x y z 2
  have h3 : 0 <= p 3 := fourBridgeRankMass_nonneg G J hf w x y z 3
  have h4 : 0 <= p 4 := fourBridgeRankMass_nonneg G J hf w x y z 4
  fin_cases i
  · change p 0 <= 1
    linarith
  · change p 1 <= 1
    linarith
  · change p 2 <= 1
    linarith
  · change p 3 <= 1
    linarith
  · change p 4 <= 1
    linarith

end

end StatMech.Ising
