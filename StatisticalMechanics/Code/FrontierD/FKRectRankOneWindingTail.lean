/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryVerticalFlux
import Code.FrontierD.FKRectEssentialBoundaryInduction
import Code.FrontierD.FKRectSeparatedWindingNoNet
import Code.FrontierD.FKRectTorusWindingCountBridge



namespace StatMech.FrontierD

noncomputable section

private theorem fkRectWalkWinding_transport_configuration
    (R : FKRectTorus) {omega tau : R.Configuration}
    (h : omega = tau) {x : R.Vertex}
    (q : (fkRectOpenGraph R omega).Walk x x) :
    fkRectWalkWinding R (h ▸ q) = fkRectWalkWinding R q := by
  subst tau
  rfl



theorem fkRectVerticalRankOneEvent_subset_windingTail
    (R : FKRectTorus) :
    fkRectVerticalRankOneEvent R ⊆
      {omega | 1 ≤ fkRectUnorientedVerticalWindingNumber R omega} := by
  rintro omega ⟨⟨x, y, hwitness⟩, hnoNet⟩
  obtain ⟨q, hqvertical⟩ :=
    hwitness.exists_closedWalk_winding_snd_ne_zero R omega x y
  have hqne : fkRectWalkWinding R q ≠ (0, 0) := by
    intro hzero
    exact hqvertical (congrArg Prod.snd hzero)
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let qF : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x x := homega.symm ▸ q
  have hqFwind : fkRectWalkWinding R qF = fkRectWalkWinding R q := by
    exact fkRectWalkWinding_transport_configuration R homega.symm q
  obtain ⟨d, hdne⟩ :=
    exists_nonzero_blackBoundaryWinding_of_closedWalk_of_not_hasNet
      R F x qF (by simpa [homega] using hnoNet)
        (by simpa [hqFwind] using hqne)
  let w := fkRectBlackBoundaryPrimalCycleWalk R omega d
  let bd := fkRectWalkWinding R w
  have hbdne : bd ≠ (0, 0) := by
    dsimp [bd, w]
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    rw [← homega]
    exact hdne
  have hdep : ¬ FKRectWindingIndependent bd (fkRectWalkWinding R q) := by
    by_cases hxd : (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1)
    · intro hind
      apply hnoNet
      exact FKRectHasNet.of_connected_closedWalks R omega hxd q w
        ((fkRectWindingIndependent_comm _ _).mp hind)
    · intro hind
      exact (fkRectClosedWalks_not_windingIndependent_of_not_reachable
        R omega hxd q w)
          ((fkRectWindingIndependent_comm _ _).mp hind)
  have hdvertical : bd.2 ≠ 0 := by
    intro hdvertical
    have hdet : bd.1 * (fkRectWalkWinding R q).2 = 0 := by
      unfold FKRectWindingIndependent at hdep
      push Not at hdep
      rw [hdvertical, zero_mul, sub_zero] at hdep
      exact hdep
    have hdfst : bd.1 = 0 :=
      (mul_eq_zero.mp hdet).resolve_right hqvertical
    apply hbdne
    apply Prod.ext
    · exact hdfst
    · exact hdvertical
  have htotal :=
    one_le_fkMedialUnorientedVerticalWindingTotal_of_blackBoundary
      R omega d (by simpa [bd, w] using hdvertical)
  unfold fkRectUnorientedVerticalWindingNumber
    fkRectUnorientedVerticalWindingTotal
  have heven := even_fkMedialUnorientedVerticalWindingTotal
    (fkRectConfigurationToMedialPairing R omega)
  obtain ⟨k, hk⟩ := heven
  change 1 ≤ fkMedialUnorientedVerticalWindingTotal
    (fkRectConfigurationToMedialPairing R omega) / 2
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  omega



theorem fkRectCriticalVerticalRankOneMass_le_windingTail
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalEventMass R q (fkRectVerticalRankOneEvent R) ≤
      fkRectCriticalWindingTailMass R q 1 := by
  have hmono := fkRectCriticalEventMass_mono R hq
    (fkRectVerticalRankOneEvent_subset_windingTail R)
  apply hmono.trans_eq
  rw [fkRectCriticalEventMass_eq_indicatorExpectation]
  unfold fkRectCriticalWindingTailMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases htail : 1 ≤ fkRectUnorientedVerticalWindingNumber R omega
  · simp [htail]
  · simp [htail]


theorem fkRectAugmentedSource_barrierConnectionProduct_le_windingTail
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      fkRectCriticalWindingTailMass R q 1 := by
  exact (fkRectAugmentedSource_barrierConnectionProduct_le_verticalRankOneMass
    R leftRight cut hsep hleft hq hgap x hx hchosen t hpair).trans
      (fkRectCriticalVerticalRankOneMass_le_windingTail
        R (zero_lt_one.trans_le hq))

end

end StatMech.FrontierD
