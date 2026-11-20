/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.Universality.RSWConcreteSeed
import Code.Universality.RSWQOneRectangleCylinder
import Code.Universality.RSWFailureComplementaryArcObstruction

open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Lattice
open StatMech.Percolation
open StatMech.FK
open StatMech.RSW.Box


abbrev Rq1ActiveExtremalPair (n : ℤ) :=
  {pair : RlcDiagonalPathPair n //
    (rlc_extremalPairCandidate pair).Nonempty}

noncomputable instance rq1ActiveExtremalPairFintype (n : ℤ) :
    Fintype (Rq1ActiveExtremalPair n) :=
  Fintype.ofFinite _



theorem rq1_iUnion_activeExtremalPairCandidate (n : ℤ) :
    (⋃ pair : Rq1ActiveExtremalPair n,
        rlc_extremalPairCandidate pair.1) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  rw [← rlc_iUnion_extremalPairCandidate n]
  ext omega
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨pair, homega⟩
    exact ⟨pair.1, homega⟩
  · rintro ⟨pair, homega⟩
    exact ⟨⟨pair, ⟨omega, homega⟩⟩, homega⟩



theorem rq1_activeExtremalPairCandidate_pairwiseDisjoint {n : ℤ}
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise (fun pair pair' : Rq1ActiveExtremalPair n =>
      Disjoint (rlc_extremalPairCandidate pair.1)
        (rlc_extremalPairCandidate pair'.1)) := by
  intro pair pair' hne
  apply rlc_extremalPairCandidate_pairwiseDisjoint hright hleft
  intro heq
  apply hne
  exact Subtype.ext heq




theorem rq1_scaleTwo_not_universal_failure_to_reflected_success :
    ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap →
        rlc_dualReflectConfig omega ∈
          rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap) := by
  intro h
  exact rlc_scaleTwoDoubleFailure_reflected_failure
    (h rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_original_failure)





theorem rq1_axisGapEdges_subset_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1)) :
    rlc_axisGapEdges G ⊆ rlc_mixedAxisGapEdges G := by
  intro e he
  rw [rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  constructor
  · simp only [Finset.mem_union]
    exact Or.inl (Or.inl he)
  · intro hpath
    rw [Finset.mem_union] at hpath
    rcases hpath with hright | hleft
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_axisGapEdges G hdisj)) hright he
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_axisGapEdges G hdisj)) hleft he



theorem rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1)) :
    rlc_axisGapConnectorEvent G ⊆ rlc_mixedAxisGapConnectorEvent G := by
  intro omega homega
  obtain ⟨x, hx, y, hy, hxR, hyR, hxy⟩ := homega
  refine ⟨x, hx, y, hy, hxR, hyR, ?_⟩
  apply StatMech.TwoDim.connectedWithin_mono _ hxy
  intro e
  by_cases he : e ∈ rlc_axisGapEdges G
  · have hemix := rq1_axisGapEdges_subset_mixedAxisGapEdges G hdisj he
    simp [rlc_maskConfig, he, hemix]
  · simp [rlc_maskConfig, he]





noncomputable def rq1_adaptiveWiredConnectorEvent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  match rlc_axisBarrierGap? gamma gamma' with
  | none => Set.univ
  | some G =>
      if G.lower + 1 = G.upper then
        rlc_mixedAxisGapConnectorEvent G
      else
        rlc_mixedWiredConnectorEvent G

theorem rq1_adaptiveWiredConnectorEvent_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    _root_.DependsOn ((rq1_adaptiveWiredConnectorEvent gamma gamma').indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAdaptiveEdges gamma gamma' : Set (Sym2 (Site 2))) := by
  unfold rq1_adaptiveWiredConnectorEvent
  split
  · rename_i hnone
    rw [rlc_mixedAdaptiveEdges, hnone]
    intro omega omega' _hagree
    simp
  · rename_i G hsome
    rw [rlc_mixedAdaptiveEdges, hsome]
    split
    · exact rlc_mixedAxisGapConnectorEvent_dependsOn _
    · exact rlc_mixedWiredConnectorEvent_dependsOn _



theorem rq1_adaptiveWiredConnector_glues_horizontal {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rq1_adaptiveWiredConnectorEvent gamma gamma' ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  unfold rq1_adaptiveWiredConnectorEvent at homega
  split at homega
  · rename_i hnone
    apply rlc_mixedAdaptiveConnector_glues_horizontal n hn gamma gamma'
    refine ⟨homega.1, ?_⟩
    simp [rlc_mixedAdaptiveConnectorEvent, hnone]
  · rename_i G hsome
    split at homega
    · apply rlc_mixedAdaptiveConnector_glues_horizontal n hn gamma gamma'
      refine ⟨homega.1, ?_⟩
      simpa [rlc_mixedAdaptiveConnectorEvent, hsome] using homega.2
    · exact rlc_mixedWiredConnector_glues_horizontal n hn gamma gamma' G
        homega




theorem rq1_adaptiveWiredConnector_half_of_retainedTopology {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hn : 0 < n)
    (htopology : ∀ (G : RlcAxisBarrierGap gamma gamma'),
      rlc_axisBarrierGap? gamma gamma' = some G →
      G.lower + 1 < G.upper →
      RlcFailureSelectedExtremalTraceTopology G) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
      (rq1_adaptiveWiredConnectorEvent gamma gamma') := by
  unfold rq1_adaptiveWiredConnectorEvent
  split
  · rw [probReal_univ]
    norm_num
  · rename_i G hsome
    have hdisj : Disjoint (rlc_pathVertices gamma.1)
        (rlc_pathVertices gamma'.1) := by
      by_contra hnot
      have hnone := rlc_axisBarrierGap?_eq_none_of_not_disjoint
        gamma gamma' hnot
      rw [hsome] at hnone
      contradiction
    split
    · rename_i hadj
      exact (rlc_axisGapConnector_half_of_adjacent G hadj).trans
        (measureReal_mono
          (rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent
            G hdisj))
    · rename_i hne
      have hlt : G.lower + 1 < G.upper := by
        have := G.lower_lt_upper
        omega
      exact
        rlc_mixedWiredConnector_half_of_failureSelectedExtremalTraceTopology
          G hn hlt (htopology G hsome hlt)




theorem rq1_active_four_by_two_crossing_lower_bound (n : ℤ) (hn : 0 < n)
    (hanchor : RlcRightCanonicalAnchorReachability n)
    (hcompetitors : ∀ pair : RlcDiagonalPathPair n,
      (rlc_extremalPairCandidate pair).Nonempty →
        Disjoint
          (rlc_rightLowerPathEdges pair.1 ∪
            rlc_leftUpperPathEdges pair.2)
          (rlc_mixedAdaptiveEdges pair.1 pair.2))
    (hconnector : ∀ pair : RlcDiagonalPathPair n,
      (rlc_extremalPairCandidate pair).Nonempty →
        (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
          (rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)) :
    (1 : ℝ) / 2048 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n) := by
  let Sright := edgesWithinFinset
    (rect_finite 0 (2 * n) (-n) n).toFinset
  let Sleft := edgesWithinFinset
    (rect_finite (-2 * n) 0 (-n) n).toFinset
  have hsafe : RlcRightSafeTraceReachability n :=
    rlc_rightSafeTraceReachability_of_canonicalAnchor hn hanchor
  obtain ⟨hright, hleft⟩ :=
    rlc_envelopeProperties_of_rightSafeTraceReachability hsafe
  have hseed := rlc_bernoulli_rsw_stopping_sixth_power
    (I := Rq1ActiveExtremalPair n)
    (E := Sym2 (Site 2)) (p := (2⁻¹ : ℝ≥0)) half_le_one
    ((1 : ℝ) / 2) (by norm_num)
    (rlc_rightDiagonal n) (rlc_leftDiagonal n)
    (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n)
    Sright Sleft
    (rlc_lrRestrictedEvent_isIncreasing 0 (2 * n) (-n) n
      rlc_lowerHalf rlc_upperHalf)
    (rlc_lrRestrictedEvent_isIncreasing (-2 * n) 0 (-n) n
      rlc_lowerHalf rlc_upperHalf)
    (by
      simpa [Sright, rlc_rightDiagonal] using
        rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
          rlc_lowerHalf rlc_upperHalf)
    (by
      simpa [Sleft, rlc_leftDiagonal] using
        rlc_lrRestrictedEvent_dependsOn (-2 * n) 0 (-n) n
          rlc_lowerHalf rlc_upperHalf)
    (by
      convert rlc_half_rightDiagonal_unconditional n hn using 1
      all_goals norm_num [rba_selfDualMeasure])
    (by
      convert rlc_half_leftDiagonal_unconditional n hn using 1
      all_goals norm_num [rba_selfDualMeasure])
    (fun pair : Rq1ActiveExtremalPair n =>
      rlc_extremalPairCandidate pair.1)
    (fun pair : Rq1ActiveExtremalPair n =>
      rlc_mixedAdaptiveConnectorEvent pair.1.1 pair.1.2)
    (fun pair : Rq1ActiveExtremalPair n =>
      rlc_extremalPairCandidateEdges pair.1)
    (fun pair : Rq1ActiveExtremalPair n =>
      rlc_mixedAdaptiveEdges pair.1.1 pair.1.2)
    (rq1_iUnion_activeExtremalPairCandidate n)
    (rq1_activeExtremalPairCandidate_pairwiseDisjoint hright hleft)
    (fun pair => rlc_extremalPairCandidate_dependsOn pair.1)
    (fun pair =>
      rlc_mixedAdaptiveConnectorEvent_dependsOn pair.1.1 pair.1.2)
    (fun pair =>
      rcs_extremalPairCandidateEdges_disjoint_of_competitors pair.1
        (hcompetitors pair.1 pair.2))
    (fun pair => hconnector pair.1 pair.2)
    (fun pair omega homega =>
      rlc_mixedAdaptiveConnector_glues_horizontal n hn pair.1.1 pair.1.2
        ⟨rlc_extremalPairCandidate_subset_pathPairOpen pair.1 homega.1,
          homega.2⟩)
  norm_num [rba_selfDualMeasure] at hseed ⊢
  exact hseed




theorem rq1_wiredInfiniteVolume_active_four_by_two_lower_bound
    (N : ℕ) (n : ℤ) (hn : 0 < n)
    (hrect : rect (-2 * n) (2 * n) (-n) n ⊆ box 2 N)
    (hanchor : RlcRightCanonicalAnchorReachability n)
    (hcompetitors : ∀ pair : RlcDiagonalPathPair n,
      (rlc_extremalPairCandidate pair).Nonempty →
        Disjoint
          (rlc_rightLowerPathEdges pair.1 ∪
            rlc_leftUpperPathEdges pair.2)
          (rlc_mixedAdaptiveEdges pair.1 pair.2))
    (hconnector : ∀ pair : RlcDiagonalPathPair n,
      (rlc_extremalPairCandidate pair).Nonempty →
        (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
          (rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)) :
    (1 : ℝ) / 2048 ≤
      (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 : ℝ) / 2 < 1)
          (by norm_num : (0 : ℝ) < 1) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n) := by
  rw [rq1_wiredInfiniteVolume_rectangle_eq N
    (-2 * n) (2 * n) (-n) n hrect]
  exact rq1_active_four_by_two_crossing_lower_bound n hn hanchor
    hcompetitors hconnector

end Universality
end StatMech
