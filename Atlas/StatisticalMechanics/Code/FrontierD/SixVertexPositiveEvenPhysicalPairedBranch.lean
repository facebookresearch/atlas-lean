/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
import Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor
import Code.FrontierD.SixVertexConfigurationPhysicalRowCycle
import Code.FrontierD.SixVertexConfigurationPhysicalParticleHole
import Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity
import Code.FrontierD.SixVertexFourByTwoTwoCycleHall
import Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch









open Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section



set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoMatchingTable_components_ne (i : Fin 200) :
    (sixVertexFourByTwoMatchingTable i).1 ≠
      (sixVertexFourByTwoMatchingTable i).2 := by
  fin_cases i <;> decide

theorem sixVertexFourByTwoMatchingIndex_components_ne (i : Fin 4 × Fin 50) :
    (sixVertexFourByTwoMatchingIndex i).1 ≠
      (sixVertexFourByTwoMatchingIndex i).2 := by
  exact sixVertexFourByTwoMatchingTable_components_ne
    (finProdFinEquiv (m := 4) (n := 50) i)




theorem sixVertexFourByTwoConfigurationPairMatching_components_ne
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    (sixVertexFourByTwoConfigurationPairMatching source).1 ≠
      (sixVertexFourByTwoConfigurationPairMatching source).2 := by
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hindex := sixVertexFourByTwoMatchingIndex_components_ne i
  intro heq
  apply hindex
  apply sixVertexFourByTwoSectorOneEquiv.injective
  simpa [sixVertexFourByTwoConfigurationPairMatching,
    sixVertexFourByTwoTargetPairEquiv, i] using heq

def sixVertexFourByTwoConfigurationPairMatchingEmbedding :
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne) where
  toFun := sixVertexFourByTwoConfigurationPairMatching
  inj' := sixVertexFourByTwoConfigurationPairMatching_injective



def sixVertexFourByTwoPhysicalBranch (choice : Bool) :
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne) :=
  if choice then
    sixVertexFourByTwoConfigurationPairMatchingEmbedding.trans
      (Equiv.prodComm _ _).toEmbedding
  else
    sixVertexFourByTwoConfigurationPairMatchingEmbedding

theorem sixVertexFourByTwoPhysicalBranch_distinct
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    sixVertexFourByTwoPhysicalBranch false source ≠
      sixVertexFourByTwoPhysicalBranch true source := by
  intro heq
  have hcomponents := congrArg Prod.fst heq
  exact sixVertexFourByTwoConfigurationPairMatching_components_ne source
    (by simpa [sixVertexFourByTwoPhysicalBranch] using hcomponents)

theorem sixVertexFourByTwoPhysicalBranch_totalC
    (choice : Bool)
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoPhysicalBranch choice source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  have hrelated :=
    sixVertexFourByTwoConfigurationPairMatching_fineRelated source
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC hrelated
  cases choice <;>
    simpa [sixVertexFourByTwoPhysicalBranch,
      sixVertexConfigurationPairTotalCPhysical, Nat.add_comm] using htotal.symm

theorem sixVertexFourByTwoSectorOne_pos :
    0 < sixVertexFourByTwoSectorOne.val := by
  norm_num [sixVertexFourByTwoSectorOne]

theorem sixVertexFourByTwoSectorOne_lt_width :
    sixVertexFourByTwoSectorOne.val < sixVertexFourByTwoTorus.width := by
  norm_num [sixVertexFourByTwoSectorOne, sixVertexFourByTwoTorus]




def sixVertexFourByTwoPhysicalSourceEmbedding :
    SixVertexConfigurationPhysicalSource
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) where
  toFun source :=
    (⟨source.1.1, source.1.2.1, by
        simpa [sixVertexFourByTwoSectorZero,
          sixVertexFourByTwoSectorOne] using source.1.2.2⟩,
      ⟨source.2.1, source.2.2.1, by
        simpa [sixVertexFourByTwoSectorTwo,
          sixVertexFourByTwoSectorOne] using source.2.2.2⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun pair => pair.1.1) heq
    · apply Subtype.ext
      exact congrArg (fun pair => pair.2.1) heq

@[simp] theorem sixVertexFourByTwoPhysicalSourceEmbedding_totalC
    (source : SixVertexConfigurationPhysicalSource
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoPhysicalSourceEmbedding source) =
      sixVertexConfigurationPairTotalCPhysical source := rfl



def sixVertexFourByTwoPhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width where
  branch choice :=
    sixVertexFourByTwoPhysicalSourceEmbedding.trans
      (sixVertexFourByTwoPhysicalBranch choice)
  distinct source := by
    exact sixVertexFourByTwoPhysicalBranch_distinct
      (sixVertexFourByTwoPhysicalSourceEmbedding source)
  aggregateTotalC source := by
    change
      2 * sixVertexConfigurationPairTotalCPhysical source <=
        sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoPhysicalBranch false
              (sixVertexFourByTwoPhysicalSourceEmbedding source)) +
          sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoPhysicalBranch true
              (sixVertexFourByTwoPhysicalSourceEmbedding source))
    have hfalse := sixVertexFourByTwoPhysicalBranch_totalC false
      (sixVertexFourByTwoPhysicalSourceEmbedding source)
    have htrue := sixVertexFourByTwoPhysicalBranch_totalC true
      (sixVertexFourByTwoPhysicalSourceEmbedding source)
    rw [hfalse, htrue]
    simp only [sixVertexFourByTwoPhysicalSourceEmbedding_totalC]
    omega



theorem sixVertexFourByTwo_sectorTrace_logConcave_of_physicalBranches
    {c : Real} (hc : 1 <= c) :
    Matrix.trace (sixVertexSectorTransfer 4 0 c ^ 2) *
        Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) <=
      Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) ^ 2 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne_pos
      sixVertexFourByTwoSectorOne_lt_width
      hc sixVertexFourByTwoPhysicalPairedBranchEmbeddings



theorem sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨1, by norm_num [sixVertexPositiveEvenTorus]⟩
        (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
  simpa [sixVertexPositiveEvenTorus, sixVertexPositiveEvenHeight,
    sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    (show Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        (by norm_num [sixVertexFourByTwoSectorOne])
        (by norm_num [sixVertexFourByTwoSectorOne,
          sixVertexFourByTwoTorus])) from
      ⟨sixVertexFourByTwoPhysicalPairedBranchEmbeddings⟩)


theorem sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨2, by norm_num [sixVertexPositiveEvenTorus]⟩
        (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
  simpa [sixVertexPositiveEvenTorus, sixVertexPositiveEvenHeight,
    sixVertexFourByTwoTorus, sixVertexFourByTwoSectorTwo] using
    (show Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoSectorTwo_pos
        sixVertexFourByTwoSectorTwo_lt_width) from
      ⟨sixVertexFourByTwoCentralPhysicalPairedBranchEmbeddings⟩)



theorem sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨3, by norm_num [sixVertexPositiveEvenTorus]⟩
        (by norm_num) (by norm_num [sixVertexPositiveEvenTorus])) := by
  simpa [sixVertexPositiveEvenTorus, sixVertexPositiveEvenHeight,
    sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne,
    sixVertexPhysicalParticleHoleMiddle] using
    (show Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByTwoTorus
        (sixVertexPhysicalParticleHoleMiddle sixVertexFourByTwoSectorOne)
        (sixVertexPhysicalParticleHoleMiddle_pos sixVertexFourByTwoSectorOne
          sixVertexFourByTwoSectorOne_lt_width)
        (sixVertexPhysicalParticleHoleMiddle_lt sixVertexFourByTwoSectorOne
          sixVertexFourByTwoSectorOne_pos)) from
      ⟨sixVertexFourByTwoPhysicalPairedBranchEmbeddings.particleHole⟩)



theorem sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors
    (n : Nat) (hn0 : 0 < n) (hn4 : n < 4) :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus 4 0 (by norm_num) (by norm_num))
        ⟨n, by norm_num [sixVertexPositiveEvenTorus]; omega⟩ hn0 hn4) := by
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl
  · simpa using sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches
  · simpa using sixVertexFourByTwo_positiveEvenBaseCentralPhysicalPairedBranches
  · simpa using
      sixVertexFourByTwo_positiveEvenBaseParticleHolePhysicalPairedBranches



def SixVertexPositiveEvenTracePhysicalPairedBranches
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)





def SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
    Nonempty
      (SixVertexConfigurationPhysicalCommonFactor
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        (sixVertexPositiveEvenTorus N (M + 1) hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩
        hn0 hnN hn0 hnN)




theorem sixVertexFour_twoRowCommonFactor_cardinality_obstruction :
    ¬ ∃ factor : Nat,
      (4 * 50) * factor = 16 * 1682 ∧
        (28 * 28) * factor = 628 * 628 := by
  rintro ⟨factor, hsource, _htarget⟩
  norm_num at hsource
  omega




def SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
    forall embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      (sixVertexPositiveEvenTorus N M hNpos hNeven)
      ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN,
    Nonempty
      (SixVertexConfigurationPhysicalFiberExtension
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        (sixVertexPositiveEvenTorus N (M + 1) hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩
        hn0 hnN hn0 hnN embeddings)



theorem sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    (hbase : forall n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
      Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          (sixVertexPositiveEvenTorus N 0 hNpos hNeven)
          ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN))
    (hsteps : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations
      N hNpos hNeven) :
    SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven := by
  intro M
  induction M with
  | zero =>
      intro n hn0 hnN
      exact hbase n hn0 hnN
  | succ M ih =>
      intro n hn0 hnN
      obtain ⟨embeddings⟩ := ih n hn0 hnN
      obtain ⟨factorization⟩ := hsteps M n hn0 hnN
      refine ⟨?_⟩
      simpa [Nat.succ_eq_add_one] using factorization.lift embeddings



theorem sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    (hbase : forall n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
      Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          (sixVertexPositiveEvenTorus N 0 hNpos hNeven)
          ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN))
    (hroutes :
      SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings
        N hNpos hNeven) :
    SixVertexPositiveEvenTracePhysicalPairedBranches N hNpos hNeven := by
  intro M
  induction M with
  | zero =>
      intro n hn0 hnN
      exact hbase n hn0 hnN
  | succ M ih =>
      intro n hn0 hnN
      obtain ⟨embeddings⟩ := ih n hn0 hnN
      obtain ⟨extension⟩ := hroutes M n hn0 hnN embeddings
      refine ⟨?_⟩
      simpa [Nat.succ_eq_add_one] using extension.lift



theorem sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightSteps
    (hsteps : SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations
      4 (by norm_num) (by norm_num)) :
    SixVertexPositiveEvenTracePhysicalPairedBranches
      4 (by norm_num) (by norm_num) := by
  apply sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightSteps
    4 (by norm_num) (by norm_num)
  · intro n hn0 hn4
    simpa using
      sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors
        n hn0 hn4
  · exact hsteps



theorem
    sixVertexFour_positiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings
    (hroutes :
      SixVertexPositiveEvenPhysicalPairedBranchHeightStepFiberRoutings
        4 (by norm_num) (by norm_num)) :
    SixVertexPositiveEvenTracePhysicalPairedBranches
      4 (by norm_num) (by norm_num) := by
  apply sixVertexPositiveEvenTracePhysicalPairedBranches_of_heightFiberRoutings
    4 (by norm_num) (by norm_num)
  · intro n hn0 hn4
    simpa using
      sixVertexFourByTwo_positiveEvenBasePhysicalPairedBranches_allSectors
        n hn0 hn4
  · exact hroutes



theorem sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 1 <= c)
    (hbranches : SixVertexPositiveEvenTracePhysicalPairedBranches
      N hNpos hNeven) :
    SixVertexSectorPositiveEvenTraceLogConcave N c := by
  intro M n hn0 hnN
  let T := sixVertexPositiveEvenTorus N M hNpos hNeven
  let middle : Fin (T.width + 1) :=
    ⟨n, by simp [T, sixVertexPositiveEvenTorus]; omega⟩
  obtain ⟨embeddings⟩ := hbranches M n hn0 hnN
  simpa [T, middle, sixVertexPositiveEvenTorus] using
    (sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      T middle hn0 hnN hc embeddings)



theorem sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 1 <= c)
    (hbranches : SixVertexPositiveEvenTracePhysicalPairedBranches
      N hNpos hNeven) :
    SixVertexSectorPerronLogConcave N c :=
  sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave N
    (lt_of_lt_of_le Real.zero_lt_one hc)
    (sixVertexSectorPositiveEvenTraceLogConcave_of_physicalPairedBranches
      N hNpos hNeven hc hbranches)


def SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTracePhysicalPairedBranches
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))



theorem
    tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches
    {q : Real} (hq : 4 < q) (r : Nat)
    (hbranches :
      SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [] with k
  apply fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k
  exact
    sixVertexSectorPerronLogConcave_of_positiveEvenPhysicalPairedBranches
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))
      (by linarith [two_lt_fkQgt4SixVertexWeight hq])
      (hbranches r k)



theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hbranches :
      SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact
    tendsto_fkRectBalancedShareSpectralGap_zero_of_physicalPairedBranches
      hq r hbranches

end

end StatMech.FrontierD
