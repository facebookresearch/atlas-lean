/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairedBranchResidualHall












open Finset

namespace StatMech.FrontierD

noncomputable section

local instance twoCycleCapacityHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p




theorem finiteRelationHall_of_keyCapacity
    {Source Target Key : Type*}
    [Fintype Source] [Fintype Target] [Fintype Key]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Key]
    (sourceKey : Source -> Key) (targetKey : Target -> Key)
    (keyRelated : Key -> Key -> Prop) [DecidableRel keyRelated]
    (related : Source -> Target -> Prop) [DecidableRel related]
    (hsound : forall source target,
      keyRelated (sourceKey source) (targetKey target) ->
        related source target)
    (hcapacity : forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys,
        Fintype.card {source : Source // sourceKey source = key}) <=
      ∑ key ∈ (Finset.univ.filter fun targetKeyValue =>
          exists sourceKeyValue,
            sourceKeyValue ∈ sourceKeys ∧
              keyRelated sourceKeyValue targetKeyValue),
        Fintype.card {target : Target // targetKey target = key}) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧ related source target).card := by
  intro sources
  let sourceKeys : Finset Key := sources.image sourceKey
  let targetKeys : Finset Key := Finset.univ.filter fun targetKeyValue =>
    exists sourceKeyValue,
      sourceKeyValue ∈ sourceKeys ∧
        keyRelated sourceKeyValue targetKeyValue
  let keyTargets : Finset Target := Finset.univ.filter fun target =>
    targetKey target ∈ targetKeys
  let relationTargets : Finset Target := Finset.univ.filter fun target =>
    exists source, source ∈ sources ∧ related source target
  have hsource : sources.card <=
      ∑ key ∈ sourceKeys,
        Fintype.card {source : Source // sourceKey source = key} := by
    rw [Finset.card_eq_sum_card_image sourceKey sources]
    apply Finset.sum_le_sum
    intro key hkey
    calc
      (sources.filter fun source => sourceKey source = key).card <=
          (Finset.univ.filter fun source =>
            sourceKey source = key).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ (Finset.subset_univ sources)
      _ = Fintype.card {source : Source // sourceKey source = key} := by
        rw [Fintype.card_subtype]
  have hkeyTargets :
      (∑ key ∈ targetKeys,
        Fintype.card {target : Target // targetKey target = key}) =
        keyTargets.card := by
    rw [show keyTargets = Finset.univ.filter fun target =>
        targetKey target ∈ targetKeys by rfl]
    simp only [Fintype.card_subtype]
    exact Finset.sum_card_fiberwise_eq_card_filter
      Finset.univ targetKeys targetKey
  have hsubset : keyTargets ⊆ relationTargets := by
    intro target htarget
    have htargetKey : targetKey target ∈ targetKeys := by
      simpa [keyTargets] using htarget
    obtain ⟨sourceKeyValue, hsourceKey, hkeyRelated⟩ := by
      simpa [targetKeys] using htargetKey
    obtain ⟨source, hsource, hsourceKeyEq⟩ :=
      Finset.mem_image.mp hsourceKey
    have hrelated : related source target := by
      apply hsound source target
      rwa [hsourceKeyEq]
    rw [show relationTargets = Finset.univ.filter fun target =>
        exists source, source ∈ sources ∧ related source target by rfl]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsource, hrelated⟩
  calc
    sources.card <=
        ∑ key ∈ sourceKeys,
          Fintype.card {source : Source // sourceKey source = key} := hsource
    _ <= ∑ key ∈ targetKeys,
          Fintype.card {target : Target // targetKey target = key} := by
      exact hcapacity sourceKeys
    _ = keyTargets.card := hkeyTargets
    _ <= relationTargets.card := Finset.card_le_card hsubset


structure FiniteKeyCapacityTransport
    (Key : Type*) [Fintype Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) where
  flow : Key -> Key -> Nat
  row_sum : forall source,
    (∑ target, flow source target) = sourceCapacity source
  column_le : forall target,
    (∑ source, flow source target) <= targetCapacity target
  supported : forall source target,
    ¬ related source target -> flow source target = 0



theorem FiniteKeyCapacityTransport.hall
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    {sourceCapacity targetCapacity : Key -> Nat}
    {related : Key -> Key -> Prop} [DecidableRel related]
    (transport : FiniteKeyCapacityTransport Key
      sourceCapacity targetCapacity related) :
    forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
      ∑ key ∈ (Finset.univ.filter fun targetKey =>
          exists sourceKey, sourceKey ∈ sourceKeys ∧
            related sourceKey targetKey),
        targetCapacity key := by
  intro sourceKeys
  let targetKeys : Finset Key := Finset.univ.filter fun targetKey =>
    exists sourceKey, sourceKey ∈ sourceKeys ∧
      related sourceKey targetKey
  have houtside (target : Key) (htarget : target ∉ targetKeys) :
      ∑ source ∈ sourceKeys, transport.flow source target = 0 := by
    apply Finset.sum_eq_zero
    intro source hsource
    apply transport.supported
    intro hrelated
    apply htarget
    rw [show targetKeys = Finset.univ.filter fun targetKey =>
        exists sourceKey, sourceKey ∈ sourceKeys ∧
          related sourceKey targetKey by rfl]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsource, hrelated⟩
  calc
    (∑ key ∈ sourceKeys, sourceCapacity key) =
        ∑ source ∈ sourceKeys,
          ∑ target, transport.flow source target := by
      apply Finset.sum_congr rfl
      intro source hsource
      exact (transport.row_sum source).symm
    _ = ∑ target, ∑ source ∈ sourceKeys,
          transport.flow source target := by
      rw [Finset.sum_comm]
    _ = ∑ target ∈ targetKeys,
          ∑ source ∈ sourceKeys,
            transport.flow source target := by
      symm
      apply Finset.sum_subset (Finset.subset_univ targetKeys)
      intro target htargetUniv htargetOutside
      exact houtside target htargetOutside
    _ <= ∑ target ∈ targetKeys,
          ∑ source, transport.flow source target := by
      apply Finset.sum_le_sum
      intro target htarget
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ sourceKeys) (by
          intro source hsourceUniv hsourceOutside
          exact Nat.zero_le _)
    _ <= ∑ target ∈ targetKeys, targetCapacity target := by
      exact Finset.sum_le_sum fun target htarget =>
        transport.column_le target




theorem finiteKeyCapacityHall_of_injectiveRouting
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) [DecidableRel related]
    (route : Key -> Key) (hinjective : Function.Injective route)
    (hsupported : forall key, related key (route key))
    (hcapacity : forall key,
      sourceCapacity key <= targetCapacity (route key)) :
    forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
        ∑ key ∈ (Finset.univ.filter fun targetKey =>
            exists sourceKey, sourceKey ∈ sourceKeys ∧
              related sourceKey targetKey),
          targetCapacity key := by
  intro sourceKeys
  let targetKeys : Finset Key := Finset.univ.filter fun targetKey =>
    exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey
  have himage : sourceKeys.image route ⊆ targetKeys := by
    intro target htarget
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htarget
    simp only [targetKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsource, hsupported source⟩
  calc
    (∑ key ∈ sourceKeys, sourceCapacity key) <=
        ∑ key ∈ sourceKeys, targetCapacity (route key) := by
      exact Finset.sum_le_sum fun key _ => hcapacity key
    _ = ∑ key ∈ sourceKeys.image route, targetCapacity key := by
      rw [Finset.sum_image hinjective.injOn]
    _ <= ∑ key ∈ targetKeys, targetCapacity key := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro key _ _
        exact Nat.zero_le _)



structure SixVertexPairFineUnionKey (T : EvenTorus) where
  fine : SixVertexHorizontalBoundedFineRowProfile T
  horizontal : T.Vertex -> Fin 3
  vertical : T.Vertex -> Fin 3
deriving DecidableEq, Fintype

def sixVertexPairFineUnionKey
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    SixVertexPairFineUnionKey T where
  fine := sixVertexHorizontalPairBoundedFineRowProfile
    (pair.1.horizontal, pair.2.horizontal)
  horizontal v := ⟨(pair.1.horizontal v).toNat +
      (pair.2.horizontal v).toNat, by
    cases pair.1.horizontal v <;> cases pair.2.horizontal v <;> decide⟩
  vertical v := ⟨(pair.1.vertical v).toNat +
      (pair.2.vertical v).toNat, by
    cases pair.1.vertical v <;> cases pair.2.vertical v <;> decide⟩


def SixVertexPairFineUnionKeyTwoCycleRelated
    {T : EvenTorus}
    (source target : SixVertexPairFineUnionKey T) : Prop :=
  source.fine = target.fine ∧
    exists family : SixVertexAtMostTwoCycleFamily T, exists sign : Bool,
      ((fun v => (target.horizontal v).val -
          (source.horizontal v).val : T.Vertex -> Int) =
        fun v => if sign then family.horizontalFlow v
          else -family.horizontalFlow v) ∧
      ((fun v => (target.vertical v).val -
          (source.vertical v).val : T.Vertex -> Int) =
        fun v => if sign then family.verticalFlow v
          else -family.verticalFlow v)

theorem sixVertexPairFineUnionKeyTwoCycleRelated_refl
    {T : EvenTorus} (key : SixVertexPairFineUnionKey T) :
    SixVertexPairFineUnionKeyTwoCycleRelated key key := by
  refine ⟨rfl, SixVertexAtMostTwoCycleFamily.empty T, true, ?_, ?_⟩
  all_goals funext v
  all_goals simp [SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexAtMostTwoCycleFamily.empty]

theorem sixVertexPairFineUnionKeyTwoCycleRelated_symm
    {T : EvenTorus} {source target : SixVertexPairFineUnionKey T}
    (hrelated : SixVertexPairFineUnionKeyTwoCycleRelated source target) :
    SixVertexPairFineUnionKeyTwoCycleRelated target source := by
  rcases hrelated with
    ⟨hfine, family, sign, hhorizontal, hvertical⟩
  refine ⟨hfine.symm, family, !sign, ?_, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    cases sign <;> simp at h ⊢ <;> omega
  · funext v
    have h := congrFun hvertical v
    cases sign <;> simp at h ⊢ <;> omega


theorem sixVertexPairFineUnionKeyTwoCycleRelated_sound
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : SixVertexPairFineUnionKeyTwoCycleRelated
      (sixVertexPairFineUnionKey source)
      (sixVertexPairFineUnionKey target)) :
    sixVertexPairAtMostTwoCycleFineRelated source target := by
  rcases hrelated with ⟨hfine, family, sign, hhorizontal, hvertical⟩
  refine ⟨⟨family, sign, ?_, ?_⟩, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionHorizontalDelta,
      sixVertexPairUnionHorizontal] using h
  · funext v
    have h := congrFun hvertical v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionVerticalDelta,
      sixVertexPairUnionVertical] using h
  · simpa [sixVertexPairFineUnionKey] using hfine



theorem sixVertexPairFineUnionKeyTwoCycleRelated_complete
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    SixVertexPairFineUnionKeyTwoCycleRelated
      (sixVertexPairFineUnionKey source)
      (sixVertexPairFineUnionKey target) := by
  rcases hrelated with
    ⟨⟨family, sign, hhorizontal, hvertical⟩, hfine⟩
  refine ⟨?_, family, sign, ?_, ?_⟩
  · simpa [sixVertexPairFineUnionKey] using hfine
  · funext v
    have h := congrFun hhorizontal v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionHorizontalDelta,
      sixVertexPairUnionHorizontal] using h
  · funext v
    have h := congrFun hvertical v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionVerticalDelta,
      sixVertexPairUnionVertical] using h

def sixVertexHorizontalActualDeficitFineUnionKey
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (source : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexPairFineUnionKey T :=
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  sixVertexPairFineUnionKey (pair.1.1.1, pair.1.2.1)

def sixVertexHorizontalActualSurplusFineUnionKey
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (target : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexPairFineUnionKey T :=
  let pair := sixVertexHorizontalActualSurplusConfigurationPair target
  sixVertexPairFineUnionKey (pair.1.1.1, pair.1.2.1)

def sixVertexHorizontalActualDeficitFineUnionCapacity
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) : Nat :=
  Fintype.card {source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualDeficitFineUnionKey source = key}

def sixVertexHorizontalActualSurplusFineUnionCapacity
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) : Nat :=
  Fintype.card {target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualSurplusFineUnionKey target = key}



def SixVertexHorizontalTwoCycleKeyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade (sourceKeys : Finset (SixVertexPairFineUnionKey T)),
    (∑ key ∈ sourceKeys,
      sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key) <=
    ∑ key ∈ (Finset.univ.filter fun targetKey =>
        exists sourceKey,
          sourceKey ∈ sourceKeys ∧
            SixVertexPairFineUnionKeyTwoCycleRelated sourceKey targetKey),
      sixVertexHorizontalActualSurplusFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key


def SixVertexHorizontalTwoCycleKeyCapacityTransports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty (FiniteKeyCapacityTransport
    (SixVertexPairFineUnionKey T)
    (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    SixVertexPairFineUnionKeyTwoCycleRelated)




def SixVertexHorizontalTwoCycleInjectiveKeyRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, exists route : SixVertexPairFineUnionKey T ->
      SixVertexPairFineUnionKey T,
    Function.Injective route /\
      (forall key,
        SixVertexPairFineUnionKeyTwoCycleRelated key (route key)) /\
      forall key,
        sixVertexHorizontalActualDeficitFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade key <=
          sixVertexHorizontalActualSurplusFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade (route key)


theorem twoCycleKeyCapacityHall_of_injectiveKeyRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hrouting : SixVertexHorizontalTwoCycleInjectiveKeyRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨route, hinjective, hsupported, hcapacity⟩ := hrouting grade
  exact finiteKeyCapacityHall_of_injectiveRouting
    (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    SixVertexPairFineUnionKeyTwoCycleRelated route hinjective
    hsupported hcapacity

theorem twoCycleKeyCapacityHall_of_transports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨transport⟩ := htransports grade
  exact transport.hall



theorem actualDeficitTokenHall_of_twoCycleKeyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalActualDeficitTokenHall T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
      (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
        hmiddle_pos hmiddle_lt) := by
  intro grade
  apply finiteRelationHall_of_keyCapacity
    sixVertexHorizontalActualDeficitFineUnionKey
    sixVertexHorizontalActualSurplusFineUnionKey
    SixVertexPairFineUnionKeyTwoCycleRelated
    (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade)
  · intro source target hrelated
    change SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source).1
      (sixVertexHorizontalActualSurplusConfigurationPair target).1
    exact sixVertexPairFineUnionKeyTwoCycleRelated_sound hrelated
  · exact hcapacity grade

theorem offDiagonalTwoCycleMatching_of_keyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt :=
  (actualDeficitTokenHall_iff_supportedMatching T
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
    (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt)).mp
    (actualDeficitTokenHall_of_twoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt hcapacity)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_keyCapacityHall T middle
        hmiddle_pos hmiddle_lt hcapacity)

theorem sixVertexSectorTrace_logConcave_of_keyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt hc
      (offDiagonalTwoCycleMatching_of_keyCapacityHall T middle
        hmiddle_pos hmiddle_lt hcapacity)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityTransports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt
      (twoCycleKeyCapacityHall_of_transports T middle
        hmiddle_pos hmiddle_lt htransports)

theorem sixVertexSectorTrace_logConcave_of_keyCapacityTransports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt hc
      (twoCycleKeyCapacityHall_of_transports T middle
        hmiddle_pos hmiddle_lt htransports)

end

end StatMech.FrontierD
