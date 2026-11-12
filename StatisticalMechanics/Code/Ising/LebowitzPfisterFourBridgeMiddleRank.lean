/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeRankSimplex



namespace StatMech.Ising

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeAgreementSpinMass_sum_five_levels
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z (-4) +
        fourBridgeAgreementSpinMass G J hf w x y z (-2) +
        fourBridgeAgreementSpinMass G J hf w x y z 0 +
        fourBridgeAgreementSpinMass G J hf w x y z 2 +
        fourBridgeAgreementSpinMass G J hf w x y z 4 = 1 := by
  classical
  rw [<- ghsiAgreementProb_sum_eq_one G J hf]
  unfold fourBridgeAgreementSpinMass
  simp_rw [Finset.sum_filter]
  repeat' rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [replicaAgreementSpin_fourBridgeSites]
  cases hw : q w <;> cases hx : q x <;> cases hy : q y <;>
    cases hz : q z <;> norm_num [spin, hw, hx, hy, hz]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in

theorem fourBridgeAgreementSpinMass_zero_eq_marginal_pairs
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeAgreementSpinMass G J hf w x y z 0 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, x} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, y} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, z} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, y} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, z} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y, z} := by
  classical
  have hpair_wx (q : ConfigSpace V) :
      ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {w, x} <->
        q w = true ∧ q x = true ∧ q y = false ∧ q z = false := by
    rw [ghsLAgreeFinset_inter_eq_iff]
    simp (config := { maxSteps := 1000000 })
      [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]
  have hpair_wy (q : ConfigSpace V) :
      ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {w, y} <->
        q w = true ∧ q x = false ∧ q y = true ∧ q z = false := by
    rw [ghsLAgreeFinset_inter_eq_iff]
    simp (config := { maxSteps := 1000000 })
      [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]
  have hpair_wz (q : ConfigSpace V) :
      ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {w, z} <->
        q w = true ∧ q x = false ∧ q y = false ∧ q z = true := by
    rw [ghsLAgreeFinset_inter_eq_iff]
    simp (config := { maxSteps := 1000000 })
      [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]
  have hpair_xy (q : ConfigSpace V) :
      ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {x, y} <->
        q w = false ∧ q x = true ∧ q y = true ∧ q z = false := by
    rw [ghsLAgreeFinset_inter_eq_iff]
    simp (config := { maxSteps := 1000000 })
      [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]
    all_goals
      intro _ _ _ _ v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> simp [fourBridgeMarkedSet]
  have hpair_xz (q : ConfigSpace V) :
      ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {x, z} <->
        q w = false ∧ q x = true ∧ q y = false ∧ q z = true := by
    rw [ghsLAgreeFinset_inter_eq_iff]
    simp (config := { maxSteps := 1000000 })
      [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]
    all_goals
      intro _ _ _ _ v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> simp [fourBridgeMarkedSet]
  have hpair_yz (q : ConfigSpace V) :
      ghsLAgreeFinset q ∩ fourBridgeMarkedSet w x y z = {y, z} <->
        q w = false ∧ q x = false ∧ q y = true ∧ q z = true := by
    rw [ghsLAgreeFinset_inter_eq_iff]
    simp (config := { maxSteps := 1000000 })
      [fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm]
    all_goals
      intro _ _ _ _ v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> simp [fourBridgeMarkedSet]
  unfold fourBridgeAgreementSpinMass ghsiAgreementMarginalProb
  simp_rw [Finset.sum_filter]
  repeat' rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [replicaAgreementSpin_fourBridgeSites]
  cases hw : q w <;> cases hx : q x <;> cases hy : q y <;>
    cases hz : q z <;>
    norm_num [spin, hpair_wx, hpair_wy, hpair_wz, hpair_xy, hpair_xz,
      hpair_yz, hw, hx, hy, hz]


theorem fourBridgeAgreementSpinMass_zero_eq_rankMass_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (w x y z : V) :
    fourBridgeAgreementSpinMass G J hf w x y z 0 =
      fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 2 := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  have hlevels := fourBridgeAgreementSpinMass_sum_five_levels
    G J hf w x y z
  rw [fourBridgeAgreementSpinMass_neg_four_eq_rankMass_zero,
    fourBridgeAgreementSpinMass_neg_two_eq_rankMass_one,
    fourBridgeAgreementSpinMass_two_eq_rankMass_three,
    fourBridgeAgreementSpinMass_four_eq_rankMass_four] at hlevels
  have hrank := fourBridgeRankMass_sum a b c d
  dsimp only [a, b, c, d] at hrank
  linarith



theorem fourBridgeRankMass_two_eq_marginal_pairs
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeRankMass
        (fourBridgeOneCoeff G J hf w x y z)
        (fourBridgeTwoCoeff G J hf w x y z)
        (fourBridgeThreeCoeff G J hf w x y z)
        (fourBridgeFourCoeff G J hf w x y z) 2 =
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, x} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, y} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, z} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, y} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, z} +
      ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y, z} := by
  rw [<- fourBridgeAgreementSpinMass_zero_eq_rankMass_two]
  exact fourBridgeAgreementSpinMass_zero_eq_marginal_pairs
    G J hf hwx hwy hwz hxy hxz hyz

end

end StatMech.Ising
