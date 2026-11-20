/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FiniteKeyCapacityMatching










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance activeKeyCapacityDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p




theorem finiteKeyCapacityHall_of_activeInjectiveRouting
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) [DecidableRel related]
    (route : Key -> Key)
    (hinjective : forall first second,
      0 < sourceCapacity first -> 0 < sourceCapacity second ->
      route first = route second -> first = second)
    (hsupported : forall key, 0 < sourceCapacity key ->
      related key (route key))
    (hcapacity : forall key, 0 < sourceCapacity key ->
      sourceCapacity key <= targetCapacity (route key)) :
    forall sourceKeys : Finset Key,
      (∑ key ∈ sourceKeys, sourceCapacity key) <=
        ∑ key ∈ (Finset.univ.filter fun targetKey =>
            exists sourceKey, sourceKey ∈ sourceKeys /\
              related sourceKey targetKey),
          targetCapacity key := by
  intro sourceKeys
  let activeSourceKeys := sourceKeys.filter fun key =>
    0 < sourceCapacity key
  let targetKeys := Finset.univ.filter fun targetKey =>
    exists sourceKey, sourceKey ∈ sourceKeys /\ related sourceKey targetKey
  have hsourceSum :
      (∑ key ∈ sourceKeys, sourceCapacity key) =
        ∑ key ∈ activeSourceKeys, sourceCapacity key := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro key hsource hnotActive
    have hnotPos : ¬ 0 < sourceCapacity key := by
      intro hpos
      apply hnotActive
      exact Finset.mem_filter.mpr ⟨hsource, hpos⟩
    omega
  have hrouteInjective : Set.InjOn route activeSourceKeys := by
    intro first hfirst second hsecond heq
    apply hinjective first second
    · exact (Finset.mem_filter.mp hfirst).2
    · exact (Finset.mem_filter.mp hsecond).2
    · exact heq
  have himage : activeSourceKeys.image route ⊆ targetKeys := by
    intro target htarget
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htarget
    have hsourceOriginal : source ∈ sourceKeys :=
      (Finset.mem_filter.mp hsource).1
    have hsourcePos : 0 < sourceCapacity source :=
      (Finset.mem_filter.mp hsource).2
    simp only [targetKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨source, hsourceOriginal, hsupported source hsourcePos⟩
  calc
    (∑ key ∈ sourceKeys, sourceCapacity key) =
        ∑ key ∈ activeSourceKeys, sourceCapacity key := hsourceSum
    _ <= ∑ key ∈ activeSourceKeys, targetCapacity (route key) := by
      apply Finset.sum_le_sum
      intro key hkey
      exact hcapacity key ((Finset.mem_filter.mp hkey).2)
    _ = ∑ key ∈ activeSourceKeys.image route, targetCapacity key := by
      rw [Finset.sum_image hrouteInjective]
    _ <= ∑ key ∈ targetKeys, targetCapacity key := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro key _ _
        exact Nat.zero_le _)

abbrev SixVertexHorizontalActualDeficitFineUnionKeyFiber
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) :=
  {source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualDeficitFineUnionKey source = key}

abbrev SixVertexHorizontalActualSurplusFineUnionKeyFiber
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) :=
  {target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualSurplusFineUnionKey target = key}




structure SixVertexHorizontalTwoCycleActiveKeyFiberRouting
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  route : SixVertexPairFineUnionKey T -> SixVertexPairFineUnionKey T
  active_injective : forall first second,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade first ->
      0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade second ->
      route first = route second -> first = second
  supported : forall key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      SixVertexPairFineUnionKeyTwoCycleRelated key (route key)
  fiberEmbedding : forall key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade key ↪
        SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade (route key)


def SixVertexHorizontalTwoCycleActiveKeyFiberRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty
    (SixVertexHorizontalTwoCycleActiveKeyFiberRouting T middle
      hmiddle_pos hmiddle_lt grade)



theorem twoCycleKeyCapacityHall_of_activeKeyFiberRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨routing⟩ := hroutings grade
  apply finiteKeyCapacityHall_of_activeInjectiveRouting
    (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    SixVertexPairFineUnionKeyTwoCycleRelated routing.route
  · exact routing.active_injective
  · exact routing.supported
  · intro key hkey
    simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
      sixVertexHorizontalActualSurplusFineUnionCapacity] using
      Fintype.card_le_of_embedding (routing.fiberEmbedding key hkey)



def SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      Nonempty
        (SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
            hmiddle_pos hmiddle_lt grade key ↪
          SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
            hmiddle_pos hmiddle_lt grade key)



theorem activeKeyFiberRoutings_of_reflexiveFiberEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hembeddings :
      SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings T middle
        hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  refine ⟨{
    route := id
    active_injective := ?_
    supported := ?_
    fiberEmbedding := ?_ }⟩
  · intro first second hfirst hsecond heq
    exact heq
  · intro key hkey
    exact sixVertexPairFineUnionKeyTwoCycleRelated_refl key
  · intro key hkey
    exact Classical.choice (hembeddings grade key hkey)

theorem twoCycleKeyCapacityHall_of_reflexiveFiberEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hembeddings :
      SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings T middle
        hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt :=
  twoCycleKeyCapacityHall_of_activeKeyFiberRoutings T middle
    hmiddle_pos hmiddle_lt
      (activeKeyFiberRoutings_of_reflexiveFiberEmbeddings
        T middle hmiddle_pos hmiddle_lt hembeddings)



theorem activeKeyFiberRoutings_of_injectiveKeyRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleInjectiveKeyRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨route, hinjective, hsupported, hcapacity⟩ := hroutings grade
  refine ⟨{
    route := route
    active_injective := ?_
    supported := ?_
    fiberEmbedding := ?_ }⟩
  · intro first second hfirst hsecond heq
    exact hinjective heq
  · intro key hkey
    exact hsupported key
  · intro key hkey
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
      sixVertexHorizontalActualSurplusFineUnionCapacity] using hcapacity key

end

end StatMech.FrontierD
