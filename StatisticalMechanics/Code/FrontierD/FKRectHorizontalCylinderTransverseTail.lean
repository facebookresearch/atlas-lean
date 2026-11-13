/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderTransverseDiagonalBound
import Code.FrontierD.FKRectHorizontalCylinderTailLaw













namespace StatMech.FrontierD

noncomputable section



theorem fkRectHorizontalCylinderCrossingTail_le_sqrtExact_pow_pred
    {q : Real} (hq : 4 < q) (R : FKRectTorus)
    (r : Nat) (hr : 0 < r) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) q)
        {rho | r <= fkRectHorizontalCylinderCrossingClusterCount R rho} <=
      Nat.choose R.width r * R.width ^ R.width *
        Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^
            (r - 1) := by
  apply fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred
    R (FK.fkProb (fkRectHorizontalCylinderGraph R)
      (fkRectCriticalP q) q)
    (fun rho => FK.fkProb_nonneg (fkRectHorizontalCylinderGraph R)
      (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
      (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
      (by linarith : (0 : Real) < q) rho)
    r hr _
  intro S _ pair first hfirst
  exact
    fkRectHorizontalCylinderDistinctPairedWitness_mass_le_sqrtExact_pow_erase
      hq R pair S first hfirst


theorem fkRectCriticalHorizontalCut_crossingTail_le_sqrtExact_pow_pred
    {q : Real} (hq : 4 < q) (R : FKRectTorus)
    (r : Nat) (hr : 0 < r) :
    fkRectCriticalHorizontalCutEventMass R q
        {eta | r <= fkRectHorizontalCutPrimalCrossingClusterCount R
          (fkRectForceHorizontalCutClosed R eta)} <=
      Nat.choose R.width r * R.width ^ R.width *
        Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^
            (r - 1) := by
  rw [fkRectCriticalHorizontalCut_crossingTail_eq_finiteEventMass R
    (by linarith : (1 : Real) <= q) r]
  exact fkRectHorizontalCylinderCrossingTail_le_sqrtExact_pow_pred
    hq R r hr




def FKRectWindingTailForcesHorizontalCylinderCrossings
    (R : FKRectTorus) (r : Nat) : Prop :=
  forall omega, r <= fkRectUnorientedVerticalWindingNumber R omega ->
    r <= fkRectHorizontalCutPrimalCrossingClusterCount R
      (fkRectForceHorizontalCutClosed R omega)




theorem fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact
    {q : Real} (hq : 4 < q) (R : FKRectTorus)
    (r : Nat) (hr : 0 < r)
    (hcross : FKRectWindingTailForcesHorizontalCylinderCrossings R r) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalWindingTailMass R q r <=
      Nat.choose R.width r * R.width ^ R.width *
        Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^
            (r - 1) := by
  let Source : Set R.Configuration :=
    {omega | r <= fkRectUnorientedVerticalWindingNumber R omega}
  let Target : Set R.Configuration :=
    {eta | r <= fkRectHorizontalCutPrimalCrossingClusterCount R
      (fkRectForceHorizontalCutClosed R eta)}
  have htransfer :=
    fkRectCritical_eventMass_le_horizontalCutEventMass_of_force R
      (by linarith : (1 : Real) <= q) Source Target (by
        intro omega homega
        change r <= fkRectHorizontalCutPrimalCrossingClusterCount R
          (fkRectForceHorizontalCutClosed R
            (fkRectForceHorizontalCutClosed R omega))
        rw [fkRectHorizontalCutClosedConfiguration_force_eq_self R
          (fkRectForceHorizontalCutClosed R omega)
          (fkRectHorizontalCutClosedConfiguration_force R omega)]
        exact hcross omega homega)
  rw [show fkRectCriticalEventMass R q Source =
      fkRectCriticalWindingTailMass R q r by
        symm
        exact fkRectCriticalWindingTailMass_eq_eventMass R q r] at htransfer
  exact htransfer.trans
    (fkRectCriticalHorizontalCut_crossingTail_le_sqrtExact_pow_pred
      hq R r hr)

end

end StatMech.FrontierD
