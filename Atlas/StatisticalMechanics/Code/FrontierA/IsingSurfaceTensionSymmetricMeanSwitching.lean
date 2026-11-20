/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases
import Code.FrontierA.IsingCriticalOddPrismLayerCoordinates











open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section



def finiteExpVarianceSkewFourSummand
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real)
    (s : E × E × E × E) : Real :=
  w s.1 * w s.2.1 * w s.2.2.1 * w s.2.2.2 *
    (I s.1 - I s.2.1) ^ 2 *
      (Real.exp (r * (I s.1 + I s.2.1 - I s.2.2.1 - I s.2.2.2)) -
        Real.exp (-r *
          (I s.1 + I s.2.1 - I s.2.2.1 - I s.2.2.2)))




structure FiniteExpVarianceSkewSwitchingPairing
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real) where
  switch : (E × E × E × E) ≃ (E × E × E × E)
  pair_nonpos : forall s,
    finiteExpVarianceSkewFourSummand w I r s +
      finiteExpVarianceSkewFourSummand w I r (switch s) <= 0



theorem finiteExpVarianceSkew_nonpos_of_switchingPairing
    {E : Type*} [Fintype E] (w I : E -> Real) (r : Real)
    (hpair : FiniteExpVarianceSkewSwitchingPairing w I r) :
    finiteExpVarianceSkew w I r <= 0 := by
  let S : E × E × E × E -> Real :=
    finiteExpVarianceSkewFourSummand w I r
  have hreindex : (∑ s, S (hpair.switch s)) = ∑ s, S s :=
    Equiv.sum_comp hpair.switch S
  have hpairs : (∑ s, (S s + S (hpair.switch s))) <= 0 := by
    calc
      (∑ s, (S s + S (hpair.switch s))) <= ∑ _s, (0 : Real) :=
        Finset.sum_le_sum fun s _ => hpair.pair_nonpos s
      _ = 0 := by simp
  rw [Finset.sum_add_distrib, hreindex] at hpairs
  have hsum : (∑ s, S s) <= 0 := by linarith
  have hfour :
      (∑ x, ∑ y, ∑ z, ∑ q,
        w x * w y * w z * w q * (I x - I y) ^ 2 *
          (Real.exp (r * (I x + I y - I z - I q)) -
            Real.exp (-r * (I x + I y - I z - I q)))) <= 0 := by
    simpa only [S, finiteExpVarianceSkewFourSummand,
      Fintype.sum_prod_type] using hsum
  have htwice : 2 * finiteExpVarianceSkew w I r <= 0 := by
    rw [two_mul_finiteExpVarianceSkew_eq_fourStateSum]
    exact hfour
  linarith



abbrev OddPrismTransferSkewSwitchingPairing
    (beta : Real) (n : Nat) (r : Real) :=
  FiniteExpVarianceSkewSwitchingPairing
    (oddPrismTransferPairBaseWeight beta n)
    (oddPrismTransferPairInteraction n) r



theorem oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing
    (beta : Real) (n : Nat) (r : Real)
    (hpair : OddPrismTransferSkewSwitchingPairing beta n r) :
    oddPrismTransferBridgeVarianceSkewNumerator beta n r <= 0 := by
  rw [oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp]
  exact finiteExpVarianceSkew_nonpos_of_switchingPairing
    (oddPrismTransferPairBaseWeight beta n)
    (oddPrismTransferPairInteraction n) r hpair



theorem oddPrismTransferBridgeVariance_le_neg_of_switchingPairing
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (hpair : OddPrismTransferSkewSwitchingPairing beta n r) :
    oddPrismTransferBridgeVariance beta n r <=
      oddPrismTransferBridgeVariance beta n (-r) := by
  rw [oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos
    beta n hn r]
  exact
    oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing
      beta n r hpair



theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc
    {beta : Real} (hbeta : 0 <= beta) {n : Nat}
    (hvar : forall t, 0 <= t -> t <= beta ->
      unequalReplicaBridgeVariance
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) beta
          (fun v => beta * oddPrismPlusField n v.1)
          (fun v => beta * oddPrismPlusField n v.1) t <=
        unequalReplicaBridgeVariance
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) beta
          (fun v => beta * oddPrismPlusField n v.1)
          (fun v => beta * oddPrismPlusField n v.1) (-t)) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) t +
      unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) (-t)
  have hdiff : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta _ _ t).differentiableAt
  have hanti : AntitoneOn D (Icc 0 beta) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) beta)
    · exact hdiff.continuous.continuousOn
    · intro t _
      exact hdiff t |>.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta _ _ t).deriv]
      exact sub_nonpos.mpr (hvar t ht.1.le ht.2.le)
  intro t ht htbeta
  have hle := hanti (by exact ⟨le_rfl, hbeta⟩) ⟨ht, htbeta⟩ ht
  dsimp only [D] at hle
  rw [neg_zero] at hle
  linarith



theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings
    {beta : Real} (hbeta : 0 <= beta) {n : Nat} (hn : 0 < n)
    (hpair : forall t, 0 <= t -> t <= beta ->
      OddPrismTransferSkewSwitchingPairing beta n t) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  apply oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc hbeta
  intro t ht htbeta
  rw [oddPrismUnequalBridgeVariance_eq_transfer beta n hn t,
    oddPrismUnequalBridgeVariance_eq_transfer beta n hn (-t)]
  exact oddPrismTransferBridgeVariance_le_neg_of_switchingPairing
    beta n hn t (hpair t ht htbeta)



theorem oddPrismUnequalBridgeSymmetricMeanOrder_all_of_transferSwitchingPairings
    {beta : Real} (hbeta : 0 <= beta)
    (hpair : forall n, 0 < n -> forall t, 0 <= t -> t <= beta ->
      OddPrismTransferSkewSwitchingPairing beta n t) :
    forall n, OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · exact oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism beta
  · exact oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings
      hbeta hn (hpair n hn)



theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_nonpos
    {beta : Real} (hbeta : beta <= 0) (n : Nat) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  intro t ht htbeta
  have ht0 : t <= 0 := htbeta.trans hbeta
  have htzero : t = 0 := le_antisymm ht0 ht
  subst t
  simp only [neg_zero, two_mul]
  exact le_rfl

end

end StatMech.FrontierA
