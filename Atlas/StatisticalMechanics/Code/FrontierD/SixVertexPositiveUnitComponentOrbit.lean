/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoComponentStrand
import Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall











open Finset
open scoped symmDiff

namespace StatMech.FrontierD

noncomputable section

local instance positiveUnitComponentOrbitDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p


structure SixVertexPositiveUnitComponentOrbitBase
    (T : EvenTorus) (middle : Fin (T.width + 1)) (k : Nat) where
  first : SixVertexArrows T
  second : SixVertexArrows T
  firstIce : first.IceRule
  secondIce : second.IceRule
  degreeTwo : SixVertexLocallyDegreeTwo first second
  k_pos : 0 < k
  k_le_middle : k ≤ middle.val
  middle_add_k_le_width : middle.val + k ≤ T.width
  firstSector : sixVertexUpCount
    (svTorusVerticalRows T first (svFinLast T.height_pos)) = middle.val - k
  secondSector : sixVertexUpCount
    (svTorusVerticalRows T second (svFinLast T.height_pos)) = middle.val + k
  component_card :
    Fintype.card (SixVertexDisagreementComponent first second) = 2 * k
  component_charge : forall component :
      SixVertexDisagreementComponent first second,
    sixVertexDisagreementComponentCharge first second component = 1

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}



def negativeComponents
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    Finset (SixVertexDisagreementComponent base.first base.second) :=
  positive.1ᶜ


def mask
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    SixVertexArrows T :=
  sixVertexDisagreementComponentSetMask base.first base.second
    (base.negativeComponents positive)

theorem negativeComponents_card
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    (base.negativeComponents positive).card = 2 * k - cardinality := by
  rw [negativeComponents, Finset.card_compl, positive.2,
    base.component_card]

theorem mask_full
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    SixVertexFullDisagreementMask base.first base.second
      (base.mask positive) :=
  sixVertexDisagreementComponentSetMask_full base.first base.second _

theorem mask_seamTransfer
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    sixVertexTorusMaskSeamTransfer (base.mask positive)
        base.first base.second = ((2 * k - cardinality : Nat) : Int) := by
  rw [mask, sixVertexDisagreementComponentSetMask_seamTransfer_of_unit
    base.first base.second base.component_charge,
    base.negativeComponents_card]



theorem mask_injective
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat} :
    Function.Injective (base.mask (cardinality := cardinality)) := by
  intro first second hmasks
  apply Subtype.ext
  apply compl_injective
  apply sixVertexDisagreementComponentSetMask_injective
    base.first base.second
  exact hmasks



def source
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt := by
  let mask := base.mask positive
  have hfull := base.mask_full positive
  have hkpos := base.k_pos
  have hk := base.k_le_middle
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      base.first base.second = ((k - 1 : Nat) : Int) := by
    rw [show mask = base.mask positive by rfl, base.mask_seamTransfer]
    omega
  have hfirstCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchFirst mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val - 1 := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchFirst mask base.first base.second)
          (svFinLast T.height_pos)) : Int) =
        ((middle.val - 1 : Nat) : Int) := by
      rw [intCast_upCount_switchFirst_eq_add_seamTransfer,
        base.firstSector, htransfer]
      omega
    exact_mod_cast hcount
  have hsecondCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchSecond mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val + 1 := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchSecond mask base.first base.second)
          (svFinLast T.height_pos)) : Int) =
        ((middle.val + 1 : Nat) : Int) := by
      rw [intCast_upCount_switchSecond_eq_sub_seamTransfer,
        base.secondSector, htransfer]
      push_cast
      omega
    exact_mod_cast hcount
  exact
    (⟨sixVertexTorusSwitchFirst mask base.first base.second,
      hfull.switchFirst_ice base.firstIce base.secondIce, hfirstCount⟩,
    ⟨sixVertexTorusSwitchSecond mask base.first base.second,
      hfull.switchSecond_ice base.firstIce base.secondIce, hsecondCount⟩)



def target
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k) :
    SixVertexConfigurationPhysicalTarget T middle := by
  let mask := base.mask positive
  have hfull := base.mask_full positive
  have hk := base.k_le_middle
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      base.first base.second = (k : Int) := by
    rw [show mask = base.mask positive by rfl, base.mask_seamTransfer]
    omega
  have hfirstCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchFirst mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchFirst mask base.first base.second)
          (svFinLast T.height_pos)) : Int) = (middle.val : Int) := by
      rw [intCast_upCount_switchFirst_eq_add_seamTransfer,
        base.firstSector, htransfer]
      omega
    exact_mod_cast hcount
  have hsecondCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchSecond mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchSecond mask base.first base.second)
          (svFinLast T.height_pos)) : Int) = (middle.val : Int) := by
      rw [intCast_upCount_switchSecond_eq_sub_seamTransfer,
        base.secondSector, htransfer]
      push_cast
      omega
    exact_mod_cast hcount
  exact
    (⟨sixVertexTorusSwitchFirst mask base.first base.second,
      hfull.switchFirst_ice base.firstIce base.secondIce, hfirstCount⟩,
    ⟨sixVertexTorusSwitchSecond mask base.first base.second,
      hfull.switchSecond_ice base.firstIce base.secondIce, hsecondCount⟩)

theorem source_injective
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    Function.Injective (fun positive =>
      base.source positive hmiddle_pos hmiddle_lt) := by
  intro first second heq
  apply base.mask_injective
  apply sixVertexTorusSwitchFirst_injective_on_fullMasks
    (base.mask_full first) (base.mask_full second)
  have harrows := congrArg (fun source => source.1.1) heq
  change sixVertexTorusSwitchFirst (base.mask first) base.first base.second =
    sixVertexTorusSwitchFirst (base.mask second) base.first base.second at harrows
  exact harrows

theorem target_injective
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k) :
    Function.Injective base.target := by
  intro first second heq
  apply base.mask_injective
  apply sixVertexTorusSwitchFirst_injective_on_fullMasks
    (base.mask_full first) (base.mask_full second)
  have harrows := congrArg (fun target => target.1.1) heq
  change sixVertexTorusSwitchFirst (base.mask first) base.first base.second =
    sixVertexTorusSwitchFirst (base.mask second) base.first base.second at harrows
  exact harrows


def sourceEmbedding
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    BooleanLayer (SixVertexDisagreementComponent base.first base.second)
        (k + 1) ↪
      SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt :=
  ⟨fun positive => base.source positive hmiddle_pos hmiddle_lt,
    base.source_injective hmiddle_pos hmiddle_lt⟩


def targetEmbedding
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k) :
    BooleanLayer (SixVertexDisagreementComponent base.first base.second) k ↪
      SixVertexConfigurationPhysicalTarget T middle :=
  ⟨base.target, base.target_injective⟩


theorem source_degreeTwo
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexLocallyDegreeTwo
      (base.source positive hmiddle_pos hmiddle_lt).1.1
      (base.source positive hmiddle_pos hmiddle_lt).2.1 := by
  change SixVertexLocallyDegreeTwo
    (sixVertexTorusSwitchFirst (base.mask positive)
      base.first base.second)
    (sixVertexTorusSwitchSecond (base.mask positive)
      base.first base.second)
  exact base.degreeTwo.pairSwitch



theorem target_mask_eq_xor_of_related
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (hrelated : booleanMiddleLayerDownRelation source target) :
    base.mask target = sixVertexTorusMaskXor (base.mask source)
      (sixVertexDisagreementComponentSetMask base.first base.second
        {booleanMiddleLayerAddedElement target source}) := by
  let component := booleanMiddleLayerAddedElement target source
  have hsource := booleanMiddleLayer_source_eq_insert_addedElement
    target source hrelated
  have hnegative : base.negativeComponents target =
      base.negativeComponents source ∆ {component} := by
    ext other
    dsimp [component]
    simp only [negativeComponents, Finset.mem_compl,
      Finset.mem_symmDiff, Finset.mem_singleton]
    rw [hsource]
    by_cases hother : other = booleanMiddleLayerAddedElement target source
    · subst other
      simp [booleanMiddleLayerAddedElement_not_mem_target]
    · simp [hother]
  rw [mask, mask, hnegative,
    sixVertexDisagreementComponentSetMask_symmDiff]



theorem related_of_target_mask_eq_xor
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (component : SixVertexDisagreementComponent base.first base.second)
    (hmasks : base.mask target = sixVertexTorusMaskXor (base.mask source)
      (sixVertexDisagreementComponentSetMask base.first base.second
        {component})) :
    booleanMiddleLayerDownRelation source target := by
  have hsets : base.negativeComponents target =
      base.negativeComponents source ∆ {component} := by
    apply sixVertexDisagreementComponentSetMask_injective
      base.first base.second
    rw [sixVertexDisagreementComponentSetMask_symmDiff]
    exact hmasks
  have hcomponent : component ∉ base.negativeComponents source := by
    intro hmem
    have herase : base.negativeComponents source ∆ {component} =
        (base.negativeComponents source).erase component := by
      ext other
      by_cases hother : other = component
      · subst other
        simp [Finset.mem_symmDiff, hmem]
      · simp [Finset.mem_symmDiff, hother]
    have hcard := congrArg Finset.card hsets
    rw [herase, Finset.card_erase_of_mem hmem,
      base.negativeComponents_card target,
      base.negativeComponents_card source] at hcard
    have hkpos := base.k_pos
    omega
  intro other htarget
  by_contra hsource
  have hnegativeSource : other ∈ base.negativeComponents source := by
    simp [negativeComponents, hsource]
  have hne : other ≠ component := by
    intro heq
    apply hcomponent
    simpa [heq] using hnegativeSource
  have hsymm : other ∈ base.negativeComponents source ∆ {component} :=
    (Finset.mem_symmDiff).2 (Or.inl ⟨hnegativeSource, by simp [hne]⟩)
  have hnegativeTarget : other ∈ base.negativeComponents target := by
    rw [hsets]
    exact hsymm
  simp [negativeComponents, htarget] at hnegativeTarget


noncomputable def componentRepresentativeEdge
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (component : SixVertexDisagreementComponent base.first base.second) :
    SixVertexTorusEdge T :=
  Classical.choose component.2

theorem componentRepresentativeEdge_disagrees
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (component : SixVertexDisagreementComponent base.first base.second) :
    sixVertexTorusEdgeDisagrees base.first base.second
      (base.componentRepresentativeEdge component) :=
  (Classical.choose_spec component.2).1

theorem componentRepresentativeEdge_component
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (component : SixVertexDisagreementComponent base.first base.second) :
    (sixVertexTorusDisagreementGraph base.first base.second).connectedComponentMk
        (base.componentRepresentativeEdge component) =
      component.1 :=
  (Classical.choose_spec component.2).2



noncomputable def sourceComponentSeed
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (component : SixVertexDisagreementComponent base.first base.second) :
    SixVertexOrientedDisagreementDart
      (base.source positive hmiddle_pos hmiddle_lt).1.1
      (base.source positive hmiddle_pos hmiddle_lt).2.1 :=
  (sixVertexOrientedDisagreementDartEquivEdge
    (base.source positive hmiddle_pos hmiddle_lt).1.2.1
    (base.source positive hmiddle_pos hmiddle_lt).2.2.1
    (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)).symm
      ⟨base.componentRepresentativeEdge component, by
        change sixVertexTorusEdgeDisagrees
          (sixVertexTorusSwitchFirst (base.mask positive)
            base.first base.second)
          (sixVertexTorusSwitchSecond (base.mask positive)
            base.first base.second)
          (base.componentRepresentativeEdge component)
        rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
        exact base.componentRepresentativeEdge_disagrees component⟩



theorem sourceComponentSeed_edge
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (component : SixVertexDisagreementComponent base.first base.second) :
    sixVertexDegreeTwoOrientedComponentEdge
        (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)
        (base.sourceComponentSeed positive hmiddle_pos hmiddle_lt component) =
      base.componentRepresentativeEdge component := by
  exact congrArg Subtype.val
    ((sixVertexOrientedDisagreementDartEquivEdge
      (base.source positive hmiddle_pos hmiddle_lt).1.2.1
      (base.source positive hmiddle_pos hmiddle_lt).2.2.1
      (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)).apply_symm_apply
        ⟨base.componentRepresentativeEdge component, by
          change sixVertexTorusEdgeDisagrees
            (sixVertexTorusSwitchFirst (base.mask positive)
              base.first base.second)
            (sixVertexTorusSwitchSecond (base.mask positive)
              base.first base.second)
            (base.componentRepresentativeEdge component)
          rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
          exact base.componentRepresentativeEdge_disagrees component⟩)



theorem sourceComponentSeed_strandMask
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (component : SixVertexDisagreementComponent base.first base.second) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
      (base.source positive hmiddle_pos hmiddle_lt).1.2.1
      (base.source positive hmiddle_pos hmiddle_lt).2.2.1
      (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)
      (base.sourceComponentSeed positive hmiddle_pos hmiddle_lt component)).mask =
    sixVertexDisagreementComponentSetMask base.first base.second
      {component} := by
  apply sixVertexDegreeTwoStrand_mask_eq_reference_component
    (base.source positive hmiddle_pos hmiddle_lt).1.2.1
    (base.source positive hmiddle_pos hmiddle_lt).2.2.1
    (base.source_degreeTwo positive hmiddle_pos hmiddle_lt)
    (sixVertexTorusDisagreementGraph_pairSwitch
      (base.mask positive) base.first base.second)
    component
  rw [base.sourceComponentSeed_edge positive hmiddle_pos hmiddle_lt component]
  exact base.componentRepresentativeEdge_component component



theorem physicalRelated_of_related
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (hrelated : booleanMiddleLayerDownRelation source target) :
    SixVertexDegreeTwoUnitStrandPhysicalRelated
      (base.sourceEmbedding hmiddle_pos hmiddle_lt source)
      (base.targetEmbedding target) := by
  let component := booleanMiddleLayerAddedElement target source
  let sourcePhysical := base.source source hmiddle_pos hmiddle_lt
  let targetPhysical := base.target target
  let hdegree := base.source_degreeTwo source hmiddle_pos hmiddle_lt
  let seed := base.sourceComponentSeed source hmiddle_pos hmiddle_lt component
  let componentMask := sixVertexDisagreementComponentSetMask
    base.first base.second {component}
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed).mask
  have hstrandMask : strandMask = componentMask := by
    exact base.sourceComponentSeed_strandMask source hmiddle_pos hmiddle_lt
      component
  have htargetMask : base.mask target =
      sixVertexTorusMaskXor (base.mask source) componentMask := by
    exact base.target_mask_eq_xor_of_related source target hrelated
  have hsupport : forall edge,
      sixVertexTorusMaskSelects componentMask edge = true →
      sixVertexTorusEdgeDisagrees sourcePhysical.1.1
        sourcePhysical.2.1 edge := by
    intro edge hselected
    change sixVertexTorusEdgeDisagrees
      (sixVertexTorusSwitchFirst (base.mask source)
        base.first base.second)
      (sixVertexTorusSwitchSecond (base.mask source)
        base.first base.second) edge
    rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact sixVertexDisagreementComponentSetMask_selects_only_disagreement
      base.first base.second {component} edge hselected
  have hfirstArrows : sixVertexTorusFlip strandMask sourcePhysical.1.1 =
      targetPhysical.1.1 := by
    rw [hstrandMask]
    rw [← sixVertexTorusSwitchFirst_eq_flip_of_disagrees hsupport]
    change sixVertexTorusSwitchFirst componentMask
        (sixVertexTorusSwitchFirst (base.mask source)
          base.first base.second)
        (sixVertexTorusSwitchSecond (base.mask source)
          base.first base.second) =
      sixVertexTorusSwitchFirst (base.mask target) base.first base.second
    rw [sixVertexTorusSwitchFirst_pairSwitch, htargetMask]
  have hsecondArrows : sixVertexTorusFlip strandMask sourcePhysical.2.1 =
      targetPhysical.2.1 := by
    rw [hstrandMask]
    rw [← sixVertexTorusSwitchSecond_eq_flip_of_disagrees hsupport]
    change sixVertexTorusSwitchSecond componentMask
        (sixVertexTorusSwitchFirst (base.mask source)
          base.first base.second)
        (sixVertexTorusSwitchSecond (base.mask source)
          base.first base.second) =
      sixVertexTorusSwitchSecond (base.mask target) base.first base.second
    rw [sixVertexTorusSwitchSecond_pairSwitch, htargetMask]
  have hdelta :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum
      sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed
  have hdeltaOne : sixVertexTorusFlipSeamDelta strandMask
      sourcePhysical.1.1 = 1 := by
    have hcount := sixVertexTorusFlip_upCount strandMask sourcePhysical.1.1
    rw [hfirstArrows, targetPhysical.1.2.2,
      sourcePhysical.1.2.2] at hcount
    simp only [Fin.val_mk] at hcount
    have hmpos := hmiddle_pos
    omega
  have hunit : (sixVertexDegreeTwoStrandSeamWord
      sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed).sum = 1 :=
    hdelta.symm.trans hdeltaOne
  refine ⟨hdegree, seed, hunit, ?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact hfirstArrows.symm
  · exact hsecondArrows.symm



theorem related_of_physicalRelated
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k)
    (hphysical : SixVertexDegreeTwoUnitStrandPhysicalRelated
      (base.sourceEmbedding hmiddle_pos hmiddle_lt source)
      (base.targetEmbedding target)) :
    booleanMiddleLayerDownRelation source target := by
  obtain ⟨hdegree, seed, hunit, htarget⟩ := hphysical
  let sourcePhysical := base.source source hmiddle_pos hmiddle_lt
  let targetPhysical := base.target target
  let edge := sixVertexDegreeTwoOrientedComponentEdge hdegree seed
  have hedgeSource : sixVertexTorusEdgeDisagrees
      sourcePhysical.1.1 sourcePhysical.2.1 edge := by
    exact (sixVertexDegreeTwoLocalMate hdegree seed.1).2
  have hedgeBase : sixVertexTorusEdgeDisagrees base.first base.second edge := by
    rw [← sixVertexTorusEdgeDisagrees_pairSwitch_iff
      (base.mask source) base.first base.second edge]
    exact hedgeSource
  let component : SixVertexDisagreementComponent base.first base.second :=
    ⟨(sixVertexTorusDisagreementGraph base.first base.second).connectedComponentMk
        edge,
      ⟨edge, hedgeBase, rfl⟩⟩
  let componentMask := sixVertexDisagreementComponentSetMask
    base.first base.second {component}
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree seed).mask
  have hstrandMask : strandMask = componentMask := by
    apply sixVertexDegreeTwoStrand_mask_eq_reference_component
      sourcePhysical.1.2.1 sourcePhysical.2.2.1 hdegree
      (sixVertexTorusDisagreementGraph_pairSwitch
        (base.mask source) base.first base.second)
      component seed
    rfl
  have hsupport : forall selectedEdge,
      sixVertexTorusMaskSelects componentMask selectedEdge = true →
      sixVertexTorusEdgeDisagrees sourcePhysical.1.1
        sourcePhysical.2.1 selectedEdge := by
    intro selectedEdge hselected
    change sixVertexTorusEdgeDisagrees
      (sixVertexTorusSwitchFirst (base.mask source)
        base.first base.second)
      (sixVertexTorusSwitchSecond (base.mask source)
        base.first base.second) selectedEdge
    rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact sixVertexDisagreementComponentSetMask_selects_only_disagreement
      base.first base.second {component} selectedEdge hselected
  have htargetFirst : targetPhysical.1.1 =
      sixVertexTorusFlip strandMask sourcePhysical.1.1 := by
    have harrows := congrArg (fun physical => physical.1.1) htarget
    change targetPhysical.1.1 =
      sixVertexTorusFlip strandMask sourcePhysical.1.1 at harrows
    exact harrows
  have hfirstSwitch :
      sixVertexTorusSwitchFirst (base.mask target)
          base.first base.second =
        sixVertexTorusSwitchFirst
          (sixVertexTorusMaskXor (base.mask source) componentMask)
          base.first base.second := by
    calc
      sixVertexTorusSwitchFirst (base.mask target)
          base.first base.second = targetPhysical.1.1 := rfl
      _ = sixVertexTorusFlip strandMask sourcePhysical.1.1 := htargetFirst
      _ = sixVertexTorusFlip componentMask sourcePhysical.1.1 := by
        rw [hstrandMask]
      _ = sixVertexTorusSwitchFirst componentMask
          sourcePhysical.1.1 sourcePhysical.2.1 :=
        (sixVertexTorusSwitchFirst_eq_flip_of_disagrees hsupport).symm
      _ = sixVertexTorusSwitchFirst
          (sixVertexTorusMaskXor (base.mask source) componentMask)
          base.first base.second := by
        exact sixVertexTorusSwitchFirst_pairSwitch
          (base.mask source) componentMask base.first base.second
  let toggled := base.negativeComponents source ∆ {component}
  have htoggledMask :
      sixVertexDisagreementComponentSetMask base.first base.second toggled =
        sixVertexTorusMaskXor (base.mask source) componentMask := by
    exact sixVertexDisagreementComponentSetMask_symmDiff
      base.first base.second (base.negativeComponents source) {component}
  have hmaskSet : base.mask target =
      sixVertexDisagreementComponentSetMask base.first base.second toggled := by
    apply sixVertexTorusSwitchFirst_injective_on_fullMasks
      (base.mask_full target)
      (sixVertexDisagreementComponentSetMask_full
        base.first base.second toggled)
    rw [htoggledMask]
    exact hfirstSwitch
  apply base.related_of_target_mask_eq_xor source target component
  exact hmaskSet.trans htoggledMask


theorem physicalRelated_iff
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (target : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k) :
    SixVertexDegreeTwoUnitStrandPhysicalRelated
        (base.sourceEmbedding hmiddle_pos hmiddle_lt source)
        (base.targetEmbedding target) ↔
      booleanMiddleLayerDownRelation source target :=
  ⟨base.related_of_physicalRelated hmiddle_pos hmiddle_lt source target,
    base.physicalRelated_of_related hmiddle_pos hmiddle_lt source target⟩



def presentation
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexDegreeTwoUnitComponentOrbitPresentation T middle
      hmiddle_pos hmiddle_lt
      (SixVertexDisagreementComponent base.first base.second) k where
  component_card := base.component_card
  sourceEmbedding := base.sourceEmbedding hmiddle_pos hmiddle_lt
  targetEmbedding := base.targetEmbedding
  related_iff := base.physicalRelated_iff hmiddle_pos hmiddle_lt



theorem hall
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    (base.presentation hmiddle_pos hmiddle_lt).Hall :=
  SixVertexDegreeTwoUnitComponentOrbitPresentation.hall
    (base.presentation hmiddle_pos hmiddle_lt)

end SixVertexPositiveUnitComponentOrbitBase



structure SixVertexPositiveUnitComponentOrbitData
    (T : EvenTorus) (middle : Fin (T.width + 1)) where
  k : Nat
  base : SixVertexPositiveUnitComponentOrbitBase T middle k

namespace SixVertexPositiveUnitComponentOrbitData

variable {T : EvenTorus} {middle : Fin (T.width + 1)}

abbrev Component (data : SixVertexPositiveUnitComponentOrbitData T middle) :=
  SixVertexDisagreementComponent data.base.first data.base.second

abbrev SourceLayer (data : SixVertexPositiveUnitComponentOrbitData T middle) :=
  BooleanLayer data.Component (data.k + 1)

abbrev TargetLayer (data : SixVertexPositiveUnitComponentOrbitData T middle) :=
  BooleanLayer data.Component data.k

end SixVertexPositiveUnitComponentOrbitData





structure SixVertexPositiveUnitComponentOrbitCover
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (Source : Type*) [Fintype Source] where
  sourcePhysical : Source ↪
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt
  Orbit : Type
  data : Orbit → SixVertexPositiveUnitComponentOrbitData T middle
  sourceCover : Source ≃ Σ index, (data index).SourceLayer
  sourceCover_physical : ∀ source,
    (data (sourceCover source).1).base.sourceEmbedding
        hmiddle_pos hmiddle_lt (sourceCover source).2 =
      sourcePhysical source
  targetEmbedding : (Σ index, (data index).TargetLayer) ↪
    SixVertexConfigurationPhysicalTarget T middle
  targetEmbedding_physical : ∀ index target,
    targetEmbedding ⟨index, target⟩ =
      (data index).base.targetEmbedding target

namespace SixVertexPositiveUnitComponentOrbitCover

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {Source : Type*} [Fintype Source]



noncomputable def toAtlas
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) :
    SixVertexDegreeTwoUnitComponentOrbitAtlas T middle
      hmiddle_pos hmiddle_lt Source where
  sourcePhysical := cover.sourcePhysical
  Orbit := cover.Orbit
  SourceOrbit := fun index => (cover.data index).SourceLayer
  TargetOrbit := fun index => (cover.data index).TargetLayer
  sourceOrbitPhysical := fun index source =>
    (cover.data index).base.sourceEmbedding hmiddle_pos hmiddle_lt source
  targetOrbitPhysical := fun index target =>
    (cover.data index).base.targetEmbedding target
  localMatching := fun index =>
    ((cover.data index).base.presentation
      hmiddle_pos hmiddle_lt).booleanMatching
  localMatching_related := fun index source =>
    ((cover.data index).base.presentation
      hmiddle_pos hmiddle_lt).booleanMatching_related source
  sourceCover := cover.sourceCover
  sourceCover_physical := cover.sourceCover_physical
  targetEmbedding := cover.targetEmbedding
  targetEmbedding_physical := cover.targetEmbedding_physical


noncomputable def matching
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) :
    Source ↪ SixVertexConfigurationPhysicalTarget T middle :=
  cover.toAtlas.matching


theorem matching_related
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    (cover.toAtlas).Related source (cover.matching source) :=
  (cover.toAtlas).matching_related source


theorem matching_fineRelated
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((cover.sourcePhysical source).1.1,
        (cover.sourcePhysical source).2.1)
      ((cover.matching source).1.1, (cover.matching source).2.1) :=
  (cover.matching_related source).fineRelated


theorem matching_layers_ne
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    (cover.matching source).1 ≠ (cover.matching source).2 :=
  SixVertexDegreeTwoUnitStrandPhysicalRelated.layers_ne
    (cover.matching_related source)


theorem matching_totalC
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) (source : Source) :
    sixVertexConfigurationPairTotalCPhysical (cover.sourcePhysical source) =
      sixVertexConfigurationPairTotalCPhysical (cover.matching source) := by
  exact sixVertexPairAtMostTwoCycleFineRelated_totalC
    (cover.matching_fineRelated source)



theorem hall
    (cover : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt Source) :
    ∀ sources : Finset Source,
      sources.card ≤
        (Finset.univ.filter fun target :
            SixVertexConfigurationPhysicalTarget T middle =>
          ∃ source ∈ sources,
            (cover.toAtlas).Related source target).card :=
  cover.toAtlas.hall

end SixVertexPositiveUnitComponentOrbitCover

end

end StatMech.FrontierD
