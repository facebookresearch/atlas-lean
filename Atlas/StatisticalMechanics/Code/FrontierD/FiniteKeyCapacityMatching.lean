/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexTwoCycleCapacityHall










open Finset

namespace StatMech.FrontierD

noncomputable section


abbrev FiniteKeyCapacityCopies
    (Key : Type*) (capacity : Key -> Nat) :=
  Sigma fun key : Key => Fin (capacity key)


def FiniteKeyCapacityExpandedRelated
    {Key : Type*} {sourceCapacity targetCapacity : Key -> Nat}
    (related : Key -> Key -> Prop)
    (source : FiniteKeyCapacityCopies Key sourceCapacity)
    (target : FiniteKeyCapacityCopies Key targetCapacity) : Prop :=
  related source.1 target.1

def sigmaFinFiberEquiv
    {Key : Type*} (capacity : Key -> Nat) (key : Key) :
    {source : FiniteKeyCapacityCopies Key capacity // source.1 = key} ≃
      Fin (capacity key) where
  toFun source := Fin.cast (congrArg capacity source.property) source.1.2
  invFun index := ⟨⟨key, index⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨sourceKey, index⟩, hkey⟩
    cases hkey
    rfl
  right_inv index := by rfl

theorem sigmaFinFiberCard
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (capacity : Key -> Nat) (key : Key) :
    Fintype.card
        {source : FiniteKeyCapacityCopies Key capacity // source.1 = key} =
      capacity key := by
  rw [Fintype.card_congr (sigmaFinFiberEquiv capacity key)]
  exact Fintype.card_fin _



noncomputable def finiteKeyCapacityCopiesEquiv
    {Source Key : Type*} [Fintype Source] [Fintype Key]
    [DecidableEq Key] (keyOf : Source -> Key) :
    Source ≃ FiniteKeyCapacityCopies Key
      (fun key => Fintype.card {source : Source // keyOf source = key}) :=
  (Equiv.sigmaFiberEquiv keyOf).symm.trans
    (Equiv.sigmaCongrRight fun _ => Fintype.equivFin _)

@[simp] theorem finiteKeyCapacityCopiesEquiv_key
    {Source Key : Type*} [Fintype Source] [Fintype Key]
    [DecidableEq Key] (keyOf : Source -> Key) (source : Source) :
    (finiteKeyCapacityCopiesEquiv keyOf source).1 = keyOf source := by
  rfl

@[simp] theorem finiteKeyCapacityCopiesEquiv_symm_key
    {Source Key : Type*} [Fintype Source] [Fintype Key]
    [DecidableEq Key] (keyOf : Source -> Key)
    (copy : FiniteKeyCapacityCopies Key
      (fun key => Fintype.card {source : Source // keyOf source = key})) :
    keyOf ((finiteKeyCapacityCopiesEquiv keyOf).symm copy) = copy.1 := by
  have h := finiteKeyCapacityCopiesEquiv_key keyOf
    ((finiteKeyCapacityCopiesEquiv keyOf).symm copy)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm



theorem finiteKeyExpandedMatching_of_supportedMatching
    {Source Target Key : Type*}
    [Fintype Source] [Fintype Target] [Fintype Key]
    [DecidableEq Key]
    (sourceKey : Source -> Key) (targetKey : Target -> Key)
    (related : Key -> Key -> Prop)
    (matching : Source -> Target) (hinjective : Function.Injective matching)
    (hsupported : forall source,
      related (sourceKey source) (targetKey (matching source))) :
    exists copiedMatching :
        FiniteKeyCapacityCopies Key
            (fun key => Fintype.card
              {source : Source // sourceKey source = key}) ->
          FiniteKeyCapacityCopies Key
            (fun key => Fintype.card
              {target : Target // targetKey target = key}),
      Function.Injective copiedMatching ∧
        forall source,
          related source.1 (copiedMatching source).1 := by
  let sourceEquiv := finiteKeyCapacityCopiesEquiv sourceKey
  let targetEquiv := finiteKeyCapacityCopiesEquiv targetKey
  let copiedMatching := fun source =>
    targetEquiv (matching (sourceEquiv.symm source))
  refine ⟨copiedMatching, ?_, ?_⟩
  · intro first second heq
    apply sourceEquiv.symm.injective
    apply hinjective
    apply targetEquiv.injective
    exact heq
  · intro source
    change related source.1
      (targetEquiv (matching (sourceEquiv.symm source))).1
    rw [finiteKeyCapacityCopiesEquiv_key]
    have h := hsupported (sourceEquiv.symm source)
    simpa [sourceEquiv] using h



theorem finiteKeyCapacityHall_iff_exists_expandedMatching
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) [DecidableRel related] :
    (forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
      ∑ key ∈ (Finset.univ.filter fun targetKey =>
          exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey),
        targetCapacity key) <->
    exists matching : FiniteKeyCapacityCopies Key sourceCapacity ->
        FiniteKeyCapacityCopies Key targetCapacity,
      Function.Injective matching ∧
        forall source, related source.1 (matching source).1 := by
  let expandedRelated :
      FiniteKeyCapacityCopies Key sourceCapacity ->
        FiniteKeyCapacityCopies Key targetCapacity -> Prop :=
    FiniteKeyCapacityExpandedRelated related
  letI : DecidableRel expandedRelated := by
    intro source target
    change Decidable (related source.1 target.1)
    infer_instance
  constructor
  · intro hcapacity
    apply (Fintype.all_card_le_filter_rel_iff_exists_injective
      expandedRelated).mp
    apply finiteRelationHall_of_keyCapacity
      (fun source => source.1) (fun target => target.1)
      related expandedRelated
    · intro source target hrelated
      exact hrelated
    · intro sourceKeys
      calc
        (∑ key ∈ sourceKeys,
            Fintype.card {source :
              FiniteKeyCapacityCopies Key sourceCapacity //
                source.1 = key}) =
            ∑ key ∈ sourceKeys, sourceCapacity key := by
          apply Finset.sum_congr rfl
          intro key hkey
          exact sigmaFinFiberCard sourceCapacity key
        _ <= ∑ key ∈ (Finset.univ.filter fun targetKey =>
              exists sourceKey, sourceKey ∈ sourceKeys ∧
                related sourceKey targetKey),
              targetCapacity key := hcapacity sourceKeys
        _ = ∑ key ∈ (Finset.univ.filter fun targetKey =>
              exists sourceKey, sourceKey ∈ sourceKeys ∧
                related sourceKey targetKey),
              Fintype.card {target :
                FiniteKeyCapacityCopies Key targetCapacity //
                  target.1 = key} := by
          apply Finset.sum_congr rfl
          intro key hkey
          exact (sigmaFinFiberCard targetCapacity key).symm
  · rintro ⟨matching, hinjective, hsupported⟩ sourceKeys
    let expandedSources :
        Finset (FiniteKeyCapacityCopies Key sourceCapacity) :=
      Finset.univ.filter fun source => source.1 ∈ sourceKeys
    let expandedTargets :
        Finset (FiniteKeyCapacityCopies Key targetCapacity) :=
      Finset.univ.filter fun target => exists source,
        source ∈ expandedSources ∧ expandedRelated source target
    let targetKeys : Finset Key := Finset.univ.filter fun targetKey =>
      exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey
    let keyTargets :
        Finset (FiniteKeyCapacityCopies Key targetCapacity) :=
      Finset.univ.filter fun target => target.1 ∈ targetKeys
    have hhall : expandedSources.card <= expandedTargets.card := by
      have hall :=
        (Fintype.all_card_le_filter_rel_iff_exists_injective
          expandedRelated).mpr ⟨matching, hinjective, hsupported⟩
      exact hall expandedSources
    have hsourceCard :
        expandedSources.card = ∑ key ∈ sourceKeys, sourceCapacity key := by
      rw [show expandedSources = Finset.univ.filter fun source =>
          source.1 ∈ sourceKeys by rfl]
      rw [← Finset.sum_card_fiberwise_eq_card_filter
        Finset.univ sourceKeys (fun source :
          FiniteKeyCapacityCopies Key sourceCapacity => source.1)]
      apply Finset.sum_congr rfl
      intro key hkey
      rw [← Fintype.card_subtype]
      exact sigmaFinFiberCard sourceCapacity key
    have htargetSubset : expandedTargets ⊆ keyTargets := by
      intro target htarget
      have htarget' : exists source,
          source ∈ expandedSources ∧ expandedRelated source target := by
        simpa [expandedTargets] using htarget
      obtain ⟨source, hsource, hrelated⟩ := htarget'
      have hsourceKey : source.1 ∈ sourceKeys := by
        simpa [expandedSources] using hsource
      rw [show keyTargets = Finset.univ.filter fun target =>
          target.1 ∈ targetKeys by rfl]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show targetKeys = Finset.univ.filter fun targetKey =>
          exists sourceKey, sourceKey ∈ sourceKeys ∧
            related sourceKey targetKey by rfl]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨source.1, hsourceKey, hrelated⟩
    have htargetCard :
        keyTargets.card = ∑ key ∈ targetKeys, targetCapacity key := by
      rw [show keyTargets = Finset.univ.filter fun target =>
          target.1 ∈ targetKeys by rfl]
      rw [← Finset.sum_card_fiberwise_eq_card_filter
        Finset.univ targetKeys (fun target :
          FiniteKeyCapacityCopies Key targetCapacity => target.1)]
      apply Finset.sum_congr rfl
      intro key hkey
      rw [← Fintype.card_subtype]
      exact sigmaFinFiberCard targetCapacity key
    calc
      (∑ key ∈ sourceKeys, sourceCapacity key) =
          expandedSources.card := hsourceCard.symm
      _ <= expandedTargets.card := hhall
      _ <= keyTargets.card := Finset.card_le_card htargetSubset
      _ = ∑ key ∈ targetKeys, targetCapacity key := htargetCard



def SixVertexHorizontalTwoCycleExpandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, exists matching :
      FiniteKeyCapacityCopies (SixVertexPairFineUnionKey T)
          (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade) ->
        FiniteKeyCapacityCopies (SixVertexPairFineUnionKey T)
          (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
            hmiddle_pos hmiddle_lt grade),
    Function.Injective matching ∧
      forall source,
        SixVertexPairFineUnionKeyTwoCycleRelated
          source.1 (matching source).1




theorem twoCycleExpandedCapacityMatchings_of_offDiagonalMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨matching, hinjective, hsupported⟩ := hmatching grade
  have hcopies := finiteKeyExpandedMatching_of_supportedMatching
    (sixVertexHorizontalActualDeficitFineUnionKey
      (T := T) (grade := grade))
    (sixVertexHorizontalActualSurplusFineUnionKey
      (T := T) (grade := grade))
    SixVertexPairFineUnionKeyTwoCycleRelated matching hinjective (by
      intro source
      apply sixVertexPairFineUnionKeyTwoCycleRelated_complete
      have h := hsupported source
      change SixVertexConfigurationPairTwoCycleFineRelated
        (sixVertexHorizontalActualDeficitConfigurationPair source).1
        (sixVertexHorizontalActualSurplusConfigurationPair
          (matching source)).1 at h
      exact h)
  simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
    sixVertexHorizontalActualSurplusFineUnionCapacity] using hcopies



theorem twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
        hmiddle_pos hmiddle_lt <->
      SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
        hmiddle_pos hmiddle_lt := by
  classical
  unfold SixVertexHorizontalTwoCycleKeyCapacityHall
    SixVertexHorizontalTwoCycleExpandedCapacityMatchings
  constructor
  · intro hcapacity grade
    exact (finiteKeyCapacityHall_iff_exists_expandedMatching
      (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      SixVertexPairFineUnionKeyTwoCycleRelated).mp (hcapacity grade)
  · intro hmatching grade
    exact (finiteKeyCapacityHall_iff_exists_expandedMatching
      (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      SixVertexPairFineUnionKeyTwoCycleRelated).mpr (hmatching grade)



theorem offDiagonalTwoCycleMatching_iff_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
        hmiddle_pos hmiddle_lt <->
      SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
        hmiddle_pos hmiddle_lt := by
  constructor
  · exact twoCycleExpandedCapacityMatchings_of_offDiagonalMatching
      T middle hmiddle_pos hmiddle_lt
  · intro hmatching
    apply offDiagonalTwoCycleMatching_of_keyCapacityHall
    exact (twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
      T middle hmiddle_pos hmiddle_lt).mpr hmatching

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt
      ((twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
        T middle hmiddle_pos hmiddle_lt).mpr hmatching)

theorem sixVertexSectorTrace_logConcave_of_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hmatching : SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt hc
      ((twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
        T middle hmiddle_pos hmiddle_lt).mpr hmatching)

end

end StatMech.FrontierD
