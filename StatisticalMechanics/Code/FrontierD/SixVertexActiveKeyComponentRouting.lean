/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexActiveKeyCapacityRouting










namespace StatMech.FrontierD

noncomputable section






structure SixVertexHorizontalTwoCycleFiberReconnectionComponents
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (sourceKey targetKey : SixVertexPairFineUnionKey T)
    where
  Component : Type
  componentFintype : Fintype Component
  sourceComponent :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
      hmiddle_pos hmiddle_lt grade sourceKey -> Component
  reconnect :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade sourceKey ->
      SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade targetKey
  output_recovers_component : forall first second,
    reconnect first = reconnect second ->
      sourceComponent first = sourceComponent second
  injective_within_component : forall first second,
    sourceComponent first = sourceComponent second ->
      reconnect first = reconnect second -> first = second

attribute [instance]
  SixVertexHorizontalTwoCycleFiberReconnectionComponents.componentFintype



def SixVertexHorizontalTwoCycleFiberReconnectionComponents.toEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat} {sourceKey targetKey : SixVertexPairFineUnionKey T}
    (components : SixVertexHorizontalTwoCycleFiberReconnectionComponents
      T middle hmiddle_pos hmiddle_lt grade sourceKey targetKey) :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade sourceKey ↪
      SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
        hmiddle_pos hmiddle_lt grade targetKey where
  toFun := components.reconnect
  inj' := by
    intro first second heq
    exact components.injective_within_component first second
      (components.output_recovers_component first second heq) heq




def sixVertexHorizontalTwoCycleFiberReconnectionComponentsOfEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat} {sourceKey targetKey : SixVertexPairFineUnionKey T}
    (embedding :
      SixVertexHorizontalActualDeficitFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade sourceKey ↪
        SixVertexHorizontalActualSurplusFineUnionKeyFiber T middle
          hmiddle_pos hmiddle_lt grade targetKey) :
    SixVertexHorizontalTwoCycleFiberReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade sourceKey targetKey where
  Component := Unit
  componentFintype := inferInstance
  sourceComponent := fun _ => ()
  reconnect := embedding
  output_recovers_component := by simp
  injective_within_component := by
    intro first second _ heq
    exact embedding.injective heq




structure SixVertexHorizontalTwoCycleActiveKeyComponentRouting
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
  components : forall key,
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade key ->
      SixVertexHorizontalTwoCycleFiberReconnectionComponents T middle
        hmiddle_pos hmiddle_lt grade key (route key)



def SixVertexHorizontalTwoCycleActiveKeyComponentRouting.toActiveKeyFiberRouting
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalTwoCycleActiveKeyComponentRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRouting T middle
      hmiddle_pos hmiddle_lt grade where
  route := routing.route
  active_injective := routing.active_injective
  supported := routing.supported
  fiberEmbedding := fun key hkey => (routing.components key hkey).toEmbedding


def SixVertexHorizontalTwoCycleActiveKeyComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty
    (SixVertexHorizontalTwoCycleActiveKeyComponentRouting T middle
      hmiddle_pos hmiddle_lt grade)


theorem activeKeyFiberRoutings_of_componentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleActiveKeyComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨routing⟩ := hroutings grade
  exact ⟨routing.toActiveKeyFiberRouting⟩



theorem twoCycleKeyCapacityHall_of_activeKeyComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleActiveKeyComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt :=
  twoCycleKeyCapacityHall_of_activeKeyFiberRoutings T middle
    hmiddle_pos hmiddle_lt
      (activeKeyFiberRoutings_of_componentRoutings T middle
        hmiddle_pos hmiddle_lt hroutings)





structure SixVertexHorizontalTwoCycleTokenReconnectionComponents
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  Component : Type
  componentFintype : Fintype Component
  sourceComponent :
    SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
        Component
  reconnect :
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
      SixVertexHorizontalActualSurplusTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
  supported : forall source,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (reconnect source)
  output_recovers_component : forall first second,
    reconnect first = reconnect second ->
      sourceComponent first = sourceComponent second
  injective_within_component : forall first second,
    sourceComponent first = sourceComponent second ->
      reconnect first = reconnect second -> first = second

attribute [instance]
  SixVertexHorizontalTwoCycleTokenReconnectionComponents.componentFintype



def SixVertexHorizontalTwoCycleTokenReconnectionComponents.toSupportedMatching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (components : SixVertexHorizontalTwoCycleTokenReconnectionComponents
      T middle hmiddle_pos hmiddle_lt grade) :
    exists matching :
      SixVertexHorizontalActualDeficitTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
        SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle,
      Function.Injective matching /\
        forall source,
          sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
            hmiddle_pos hmiddle_lt grade source (matching source) := by
  refine ⟨components.reconnect, ?_, components.supported⟩
  intro first second heq
  exact components.injective_within_component first second
    (components.output_recovers_component first second heq) heq


def SixVertexHorizontalTwoCycleTokenComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty
    (SixVertexHorizontalTwoCycleTokenReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade)



theorem offDiagonalTwoCycleMatching_of_tokenComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleTokenComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨components⟩ := hroutings grade
  exact components.toSupportedMatching



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_tokenComponentRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalTwoCycleTokenComponentRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_tokenComponentRoutings T middle
        hmiddle_pos hmiddle_lt hroutings)

end

end StatMech.FrontierD
