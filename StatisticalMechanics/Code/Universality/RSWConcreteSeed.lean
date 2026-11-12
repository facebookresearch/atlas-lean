/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Universality.RSWLowestCrossing
import Code.Universality.CrossingReflection

open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.Percolation
open StatMech.RSW.Box



theorem rcs_centeredSquare_vertical_eq_horizontal (n : ℤ) :
    rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n) =
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
  rw [crf_verticalCrossing_eq_horizontal_swap 0 (2 * n) (-n) n
    (rlc_horizontalCrossingEvent_measurableSet (-n) n 0 (2 * n))]
  let t : Site 2 := ![n, -n]
  have ht := cti_horizontalCrossing_translation_invariant (-n) n 0 (2 * n) t
    (rlc_horizontalCrossingEvent_measurableSet (-n) n 0 (2 * n))
  simpa [t, show n + n = 2 * n by ring,
    show 2 * n + -n = n by ring] using ht.symm



theorem rcs_diagonal_pair_lower_bound (n : ℤ) (hn : 0 < n) :
    let alpha := rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n)
    alpha ^ 3 / 4 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) ∧
      alpha ^ 3 / 4 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
  dsimp only
  have hright := rlc_rightDiagonal_lower_bound (2⁻¹ : ℝ≥0) half_le_one n hn
    (rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n))
    measureReal_nonneg (le_refl _)
  have hvertical : rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) ≤
      rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n) := by
    rw [rcs_centeredSquare_vertical_eq_horizontal]
  have hr : rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) ^ 3 / 4 ≤
      rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
    simpa [rba_selfDualMeasure] using hright hvertical
  refine ⟨hr, ?_⟩
  rw [rlc_leftDiagonal_prob_eq_right]
  exact hr



noncomputable def rcs_rightLower (n : ℤ) :
    Finset (rect 0 (2 * n) (-n) n) :=
  rlc_verticalSegment 0 (2 * n) (-n) n 0 (-n) 0

noncomputable def rcs_rightUpper (n : ℤ) :
    Finset (rect 0 (2 * n) (-n) n) :=
  rlc_verticalSegment 0 (2 * n) (-n) n (2 * n) 0 n

noncomputable def rcs_leftLower (n : ℤ) :
    Finset (rect (-2 * n) 0 (-n) n) :=
  rlc_verticalSegment (-2 * n) 0 (-n) n (-2 * n) (-n) 0

noncomputable def rcs_leftUpper (n : ℤ) :
    Finset (rect (-2 * n) 0 (-n) n) :=
  rlc_verticalSegment (-2 * n) 0 (-n) n 0 0 n

abbrev RcsRightPath (n : ℤ) := RlcBetweenPath (rcs_rightLower n) (rcs_rightUpper n)
abbrev RcsLeftPath (n : ℤ) := RlcBetweenPath (rcs_leftLower n) (rcs_leftUpper n)
abbrev RcsPathPair (n : ℤ) := RcsRightPath n × RcsLeftPath n

theorem rcs_right_between_eq_diagonal (n : ℤ) :
    rlc_betweenEvent (rcs_rightLower n) (rcs_rightUpper n) =
      rlc_rightDiagonal n := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    have hx := rlc_mem_verticalSegment.mp x.2
    have hy := rlc_mem_verticalSegment.mp y.2
    let xl : leftSide 0 (2 * n) (-n) n := ⟨x.1, x.1.2, hx.1⟩
    let yr : rightSide 0 (2 * n) (-n) n := ⟨y.1, y.1.2, hy.1⟩
    exact ⟨xl, yr, hx.2.2, hy.2.1, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    let xr : rect 0 (2 * n) (-n) n := ⟨x, leftSide_subset x.2⟩
    let yr : rect 0 (2 * n) (-n) n := ⟨y, rightSide_subset y.2⟩
    have hxr : xr ∈ rcs_rightLower n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨x.2.2, (leftSide_subset x.2).2.2.1, hx⟩
    have hyr : yr ∈ rcs_rightUpper n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨y.2.2, hy, (rightSide_subset y.2).2.2.2⟩
    exact ⟨⟨xr, hxr⟩, ⟨yr, hyr⟩, hxy⟩

theorem rcs_left_between_eq_diagonal (n : ℤ) :
    rlc_betweenEvent (rcs_leftLower n) (rcs_leftUpper n) =
      rlc_leftDiagonal n := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    have hx := rlc_mem_verticalSegment.mp x.2
    have hy := rlc_mem_verticalSegment.mp y.2
    let xl : leftSide (-2 * n) 0 (-n) n := ⟨x.1, x.1.2, hx.1⟩
    let yr : rightSide (-2 * n) 0 (-n) n := ⟨y.1, y.1.2, hy.1⟩
    exact ⟨xl, yr, hx.2.2, hy.2.1, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    let xr : rect (-2 * n) 0 (-n) n := ⟨x, leftSide_subset x.2⟩
    let yr : rect (-2 * n) 0 (-n) n := ⟨y, rightSide_subset y.2⟩
    have hxr : xr ∈ rcs_leftLower n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨x.2.2, (leftSide_subset x.2).2.2.1, hx⟩
    have hyr : yr ∈ rcs_leftUpper n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨y.2.2, hy, (rightSide_subset y.2).2.2.2⟩
    exact ⟨⟨xr, hxr⟩, ⟨yr, hyr⟩, hxy⟩

def rcs_pathPairOpen {n : ℤ} (i : RcsPathPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_betweenPathOpen i.1 ∩ rlc_betweenPathOpen i.2



theorem rcs_iUnion_pathPairOpen (n : ℤ) :
    (⋃ i : RcsPathPair n, rcs_pathPairOpen i) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  rw [← rcs_right_between_eq_diagonal n, ← rcs_left_between_eq_diagonal n,
    ← rlc_iUnion_betweenPathOpen, ← rlc_iUnion_betweenPathOpen]
  ext omega
  simp only [rcs_pathPairOpen, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨g, h⟩, hg, hh⟩
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
    exact ⟨⟨g, h⟩, hg, hh⟩







theorem rcs_pathPairEdges_disjoint_mixedAdaptiveEdges {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    Disjoint (rlc_pathPairEdges pair)
      (rlc_mixedAdaptiveEdges pair.1 pair.2) := by
  rw [Finset.disjoint_left]
  intro e hePair heFresh
  rw [rlc_pathPairEdges, Finset.mem_union] at hePair
  rcases hePair with heRight | heLeft
  · exact (Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heRight heFresh
  · exact (Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heLeft heFresh




theorem rcs_extremalPairCandidateEdges_disjoint_of_competitors {n : ℤ}
    (pair : RlcDiagonalPathPair n)
    (hcompetitors : Disjoint
      (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2)
      (rlc_mixedAdaptiveEdges pair.1 pair.2)) :
    Disjoint (rlc_extremalPairCandidateEdges pair)
      (rlc_mixedAdaptiveEdges pair.1 pair.2) := by
  rw [Finset.disjoint_left]
  intro e heCandidate heFresh
  rw [rlc_extremalPairCandidateEdges, Finset.mem_union,
    rlc_rightLowestCandidateEdges, rlc_leftHighestCandidateEdges,
    Finset.mem_union, Finset.mem_union] at heCandidate
  rcases heCandidate with (heRight | heLower) | heLeft | heUpper
  · exact (Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heRight heFresh
  · exact (Finset.disjoint_left.mp hcompetitors)
      (Finset.mem_union_left _ heLower) heFresh
  · exact (Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heLeft heFresh
  · exact (Finset.disjoint_left.mp hcompetitors)
      (Finset.mem_union_right _ heUpper) heFresh












theorem rcs_four_by_two_crossing_lower_bound (n : ℤ) (hn : 0 < n)
    (hanchor : RlcRightCanonicalAnchorReachability n)
    (hcompetitors : ∀ pair : RlcDiagonalPathPair n,
      Disjoint
        (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2)
        (rlc_mixedAdaptiveEdges pair.1 pair.2))
    (hconnector : ∀ pair : RlcDiagonalPathPair n,
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
    (fun pair : RlcDiagonalPathPair n => rlc_extremalPairCandidate pair)
    (fun pair : RlcDiagonalPathPair n =>
      rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)
    (fun pair : RlcDiagonalPathPair n => rlc_extremalPairCandidateEdges pair)
    (fun pair : RlcDiagonalPathPair n => rlc_mixedAdaptiveEdges pair.1 pair.2)
    (rlc_iUnion_extremalPairCandidate n)
    (rlc_extremalPairCandidate_pairwiseDisjoint hright hleft)
    rlc_extremalPairCandidate_dependsOn
    (fun pair => rlc_mixedAdaptiveConnectorEvent_dependsOn pair.1 pair.2)
    (fun pair =>
      rcs_extremalPairCandidateEdges_disjoint_of_competitors pair
        (hcompetitors pair))
    hconnector
    (fun pair omega homega =>
      rlc_mixedAdaptiveConnector_glues_horizontal n hn pair.1 pair.2
        ⟨rlc_extremalPairCandidate_subset_pathPairOpen pair homega.1,
          homega.2⟩)
  norm_num [rba_selfDualMeasure] at hseed ⊢
  exact hseed

end Universality

end StatMech
