/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMinimalCyclePhysicalRepair
import Code.FrontierD.SixVertexFourByTwoTwoCycleHall
import Code.FrontierD.SixVertexWindingCycleBranchRecovery

















namespace StatMech.FrontierD

noncomputable section



theorem sixVertexPairAtMostTwoCycleFineRelated_swap_target
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    sixVertexPairAtMostTwoCycleFineRelated source (target.2, target.1) := by
  rcases target with ⟨targetFirst, targetSecond⟩
  rcases hrelated.1 with ⟨family, sign, hhorizontal, hvertical⟩
  constructor
  · refine ⟨family, sign, ?_, ?_⟩
    · rw [show sixVertexPairUnionHorizontalDelta source
          (targetSecond, targetFirst) =
          sixVertexPairUnionHorizontalDelta source
            (targetFirst, targetSecond) by
        funext v
        simp only [sixVertexPairUnionHorizontalDelta,
          sixVertexPairUnionHorizontal]
        omega]
      exact hhorizontal
    · rw [show sixVertexPairUnionVerticalDelta source
          (targetSecond, targetFirst) =
          sixVertexPairUnionVerticalDelta source
            (targetFirst, targetSecond) by
        funext v
        simp only [sixVertexPairUnionVerticalDelta,
          sixVertexPairUnionVertical]
        omega]
      exact hvertical
  · calc
      sixVertexHorizontalPairBoundedFineRowProfile
          (source.1.horizontal, source.2.horizontal) =
          sixVertexHorizontalPairBoundedFineRowProfile
            (targetFirst.horizontal, targetSecond.horizontal) := hrelated.2
      _ = sixVertexHorizontalPairBoundedFineRowProfile
            (targetSecond.horizontal, targetFirst.horizontal) :=
        (sixVertexSwapHorizontalLayers_boundedFineRowProfile
          (targetFirst.horizontal, targetSecond.horizontal)).symm


def sixVertexSwapPhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    SixVertexConfigurationPhysicalTarget T middle :=
  (target.2, target.1)

@[simp] theorem sixVertexSwapPhysicalTarget_swap
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    sixVertexSwapPhysicalTarget (sixVertexSwapPhysicalTarget target) =
      target := by
  rfl

theorem sixVertexSwapPhysicalTarget_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexSwapPhysicalTarget (T := T) (middle := middle)) := by
  intro first second heq
  have := congrArg sixVertexSwapPhysicalTarget heq
  simpa using this




structure SixVertexConfigurationPairUnionCyclePairedRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  target : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt → Bool →
    SixVertexConfigurationPhysicalTarget T middle
  related : ∀ source branch,
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1)
      ((target source branch).1.1, (target source branch).2.1)
  source_recoverable : ∀ first second branch,
    target first branch = target second branch → first = second
  branch_distinct : ∀ source,
    target source false ≠ target source true



structure SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  target : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt ↪
    SixVertexConfigurationPhysicalTarget T middle
  related : ∀ source,
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1)
      ((target source).1.1, (target source).2.1)
  layers_ne : ∀ source, (target source).1 ≠ (target source).2

namespace SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding


def toPairedRepairs
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (embedding : SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt where
  target source branch :=
    if branch then sixVertexSwapPhysicalTarget (embedding.target source)
    else embedding.target source
  related source branch := by
    cases branch
    · simpa using embedding.related source
    · simpa [sixVertexSwapPhysicalTarget] using
        sixVertexPairAtMostTwoCycleFineRelated_swap_target
          (embedding.related source)
  source_recoverable := by
    intro first second branch heq
    cases branch
    · exact embedding.target.injective heq
    · apply embedding.target.injective
      exact sixVertexSwapPhysicalTarget_injective heq
  branch_distinct := by
    intro source heq
    apply embedding.layers_ne source
    exact congrArg Prod.fst heq

end SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding

namespace SixVertexConfigurationPairUnionCyclePairedRepairs



theorem target_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source) (branch) :
    sixVertexConfigurationPairTotalCPhysical
        (repairs.target source branch) =
      sixVertexConfigurationPairTotalCPhysical source := by
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC
    (repairs.related source branch)
  simpa [sixVertexConfigurationPairTotalCPhysical] using htotal.symm



noncomputable def family
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) (branch : Bool) :
    SixVertexAtMostTwoCycleFamily T :=
  Classical.choose (repairs.related source branch).1

noncomputable def sign
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) (branch : Bool) : Bool :=
  Classical.choose (Classical.choose_spec
    (repairs.related source branch).1)


noncomputable def signedTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) (branch : Bool) :
    SixVertexSignedWindingCycleTarget
      (source.1.1, source.2.1) (repairs.family source branch)
      (repairs.sign source branch) where
  target := ((repairs.target source branch).1.1,
    (repairs.target source branch).2.1)
  horizontalDelta := (Classical.choose_spec (Classical.choose_spec
    (repairs.related source branch).1)).1
  verticalDelta := (Classical.choose_spec (Classical.choose_spec
    (repairs.related source branch).1)).2



def toPhysicalPairedBranches
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt where
  branch choice :=
    { toFun := fun source => repairs.target source choice
      inj' := by
        intro first second heq
        exact repairs.source_recoverable first second choice heq }
  distinct := repairs.branch_distinct
  aggregateTotalC := by
    intro source
    change 2 * sixVertexConfigurationPairTotalCPhysical source ≤
      sixVertexConfigurationPairTotalCPhysical
          (repairs.target source false) +
        sixVertexConfigurationPairTotalCPhysical
          (repairs.target source true)
    rw [repairs.target_totalC source false,
      repairs.target_totalC source true]
    omega



theorem twoCycleFineHall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairTwoCycleFineHall T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩ := by
  rw [configurationPairTwoCycleFineHall_iff_exists_injective]
  exact ⟨fun source => repairs.target source false,
    fun first second heq =>
      repairs.source_recoverable first second false heq,
    fun source => repairs.related source false⟩



theorem markedTraceCoefficientwiseLogConcave
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
    T middle hmiddle_pos hmiddle_lt repairs.twoCycleFineHall

end SixVertexConfigurationPairUnionCyclePairedRepairs



def SixVertexConfigurationUnitCyclePairedRepairs.toPairUnionCycle
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationUnitCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt where
  target source branch :=
    sixVertexUnitCyclePhysicalTarget source (repairs.repair source branch)
  related source branch :=
    (repairs.repair source branch).target_twoCycleFine
  source_recoverable := repairs.source_recoverable
  branch_distinct := repairs.branch_distinct


def SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  ∀ M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationPairUnionCyclePairedRepairs
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)

def SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs : Prop :=
  ∀ r k : Nat,
    SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))



def SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  ∀ M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)

def SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings :
    Prop :=
  ∀ r k : Nat,
    SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))

theorem pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
    {N : Nat} {hNpos : 0 < N} {hNeven : Even N}
    (hembeddings :
      SixVertexPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings
        N hNpos hNeven) :
    SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      N hNpos hNeven := by
  intro M n hn0 hnN
  obtain ⟨embedding⟩ := hembeddings M n hn0 hnN
  exact ⟨embedding.toPairedRepairs⟩

theorem canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
    (hembeddings :
      SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings) :
    SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs := by
  intro r k
  exact pairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
    (hembeddings r k)


theorem sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 2 ≤ c)
    (hrepairs : SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      N hNpos hNeven) :
    SixVertexSectorPositiveEvenTraceLogConcave N c := by
  intro M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs M n hn0 hnN
  let T := sixVertexPositiveEvenTorus N M hNpos hNeven
  let middle : Fin (T.width + 1) :=
    ⟨n, by simp [T, sixVertexPositiveEvenTorus]; omega⟩
  simpa [T, middle, sixVertexPositiveEvenTorus] using
    sixVertexSectorTrace_logConcave_of_twoCycleFineHall
      T middle hn0 hnN hc repairs.twoCycleFineHall

theorem sixVertexSectorPerronLogConcave_of_pairUnionCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N)
    {c : Real} (hc : 2 ≤ c)
    (hrepairs : SixVertexPositiveEvenTracePairUnionCyclePairedRepairs
      N hNpos hNeven) :
    SixVertexSectorPerronLogConcave N c :=
  sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave N
    (by linarith)
    (sixVertexSectorPositiveEvenTraceLogConcave_of_pairUnionCyclePairedRepairs
      N hNpos hNeven hc hrepairs)

theorem canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs
    (hrepairs :
      SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs) :
    SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
  intro r k M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs r k M n hn0 hnN
  exact ⟨repairs.toPhysicalPairedBranches⟩

theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : ∀ scale k : Nat,
      0 < scale → Even scale →
      12 * scale + 2 < 2 * (k + 3) →
      ∀ᶠ blocks in Filter.atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hrepairs :
      SixVertexCanonicalPositiveEvenTracePairUnionCyclePairedRepairs) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
    hq hhard hcross
      (canonicalPhysicalPairedBranches_of_pairUnionCyclePairedRepairs hrepairs)



theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCycleOffDiagonalEmbeddings
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : ∀ scale k : Nat,
      0 < scale → Even scale →
      12 * scale + 2 < 2 * (k + 3) →
      ∀ᶠ blocks in Filter.atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hembeddings :
      SixVertexCanonicalPositiveEvenTracePairUnionCycleOffDiagonalEmbeddings) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_pairUnionCyclePairedRepairs
    hq hhard hcross
      (canonicalPairUnionCyclePairedRepairs_of_offDiagonalEmbeddings
        hembeddings)



set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoMatchingTable_layers_ne (i : Fin 200) :
    (sixVertexFourByTwoMatchingTable i).1 ≠
      (sixVertexFourByTwoMatchingTable i).2 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoConfigurationPairMatching_layers_ne
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    (sixVertexFourByTwoConfigurationPairMatching source).1 ≠
      (sixVertexFourByTwoConfigurationPairMatching source).2 := by
  intro heq
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hindex :
      (sixVertexFourByTwoMatchingIndex i).1 =
        (sixVertexFourByTwoMatchingIndex i).2 := by
    apply sixVertexFourByTwoSectorOneConfiguration_injective
    exact heq
  apply sixVertexFourByTwoMatchingTable_layers_ne
    (finProdFinEquiv (m := 4) (n := 50) i)
  exact hindex



def sixVertexFourByTwoPairUnionCycleOffDiagonalEmbedding :
    SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne]) where
  target :=
    { toFun := sixVertexFourByTwoConfigurationPairMatching
      inj' := sixVertexFourByTwoConfigurationPairMatching_injective }
  related := sixVertexFourByTwoConfigurationPairMatching_fineRelated
  layers_ne := sixVertexFourByTwoConfigurationPairMatching_layers_ne





def sixVertexFourByTwoPairUnionCyclePairedRepairs :
    SixVertexConfigurationPairUnionCyclePairedRepairs
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne]) :=
  sixVertexFourByTwoPairUnionCycleOffDiagonalEmbedding.toPairedRepairs

end

end StatMech.FrontierD
