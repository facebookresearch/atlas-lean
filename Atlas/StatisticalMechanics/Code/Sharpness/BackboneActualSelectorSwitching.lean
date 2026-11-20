/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















import Code.Sharpness.BackboneExplorationSelectorAdmissible

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

local instance (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _






structure shb_CurrentDynamicSelector where
  sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  select : (d : shb_ExplorationDomain V) ->
    (d.graph.edgeFinset -> Nat) -> List (shb_ExplorationSegment V)
  sourceClass_nil : forall d, sourceClass d [] = ∅
  sources_eq_sourceClass_of_select : forall d m word,
    select d m = word ->
      sources d.graph (ofEdgeFun d.graph m) = sourceClass d word
  select_nil_of_sources_empty : forall d m,
    sources d.graph (ofEdgeFun d.graph m) = ∅ -> select d m = []
  select_ne_cons_of_not_active : forall d s ss m,
    s ∉ d.active -> select d m ≠ s :: ss


def shb_CurrentDynamicSelector.Fiber
    (S : shb_CurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) : Prop :=
  sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d word /\
    S.select d m = word

noncomputable instance shb_CurrentDynamicSelector.fiberDecidable
    (S : shb_CurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) :
    DecidablePred (S.Fiber d word) :=
  Classical.decPred _



noncomputable def shb_CurrentDynamicSelector.actualMass
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) : shb_ExplorationFiberMass V :=
  shb_actualExplorationFiberMass beta J S.sourceClass
    (fun d word m => S.select d m = word)


theorem shb_CurrentDynamicSelector.actualMass_eq_fiberTsum
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) :
    S.actualMass beta J d word =
      ∑' m : d.graph.edgeFinset -> Nat,
        if S.Fiber d word m then weight d.graph beta J (ofEdgeFun d.graph m)
        else 0 := by
  unfold shb_CurrentDynamicSelector.actualMass
    shb_actualExplorationFiberMass shb_CurrentDynamicSelector.Fiber
  apply tsum_congr
  intro m
  by_cases h :
      sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d word /\
        S.select d m = word <;> simp [h]


noncomputable def shb_explorationCoordinateWeight
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) : Real :=
  weight d.graph beta J (ofEdgeFun d.graph m)


def shb_ActiveSegmentFiber
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (m : d.graph.edgeFinset -> Nat) : Prop :=
  sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} /\
    shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
      some (s.toPath d.graph (d.active_supported s hs))

noncomputable instance shb_ActiveSegmentFiber_decidable
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) : DecidablePred (shb_ActiveSegmentFiber d s hs) :=
  Classical.decPred _


theorem shb_summable_explorationFiberIndicator
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V)
    (P : (d.graph.edgeFinset -> Nat) -> Prop) [DecidablePred P] :
    Summable (fun m => if P m then
      shb_explorationCoordinateWeight beta J d m else 0) := by
  let f := fun m : d.graph.edgeFinset -> Nat =>
    shb_explorationCoordinateWeight beta J d m
  have hf : Summable f := shb_summable_weight d.graph beta J
  have heq : (fun m => if P m then f m else 0) =
      Set.indicator {m | P m} f := by
    funext m
    by_cases hm : P m <;> simp [Set.indicator, hm]
  rw [heq]
  exact hf.indicator _



theorem shb_activeSegmentFiberMass_eq_segmentNum
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) :
    (∑' m : d.graph.edgeFinset -> Nat,
      if shb_ActiveSegmentFiber d s hs m then
        shb_explorationCoordinateWeight beta J d m else 0) =
      shb_segmentNum beta J d s := by
  unfold shb_segmentNum
  rw [dif_pos hs]
  unfold shb_backboneNumSupport shb_ActiveSegmentFiber
    shb_explorationCoordinateWeight
  apply tsum_congr
  intro m
  by_cases h :
      sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} /\
        shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
          some (s.toPath d.graph (d.active_supported s hs)) <;> simp [h]



abbrev shb_SelectorSwitchPair (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) :=
  (d.graph.edgeFinset -> Nat) ×
    ((shb_BackboneExplorationDomain.advance d s).graph.edgeFinset -> Nat)



noncomputable def shb_selectorSwitchLeftTerm
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (mr : shb_SelectorSwitchPair d s) : Real :=
  if S.Fiber d (s :: ss) mr.1 /\
      sources (shb_BackboneExplorationDomain.advance d s).graph
        (ofEdgeFun (shb_BackboneExplorationDomain.advance d s).graph mr.2) = ∅
  then
    shb_explorationCoordinateWeight beta J d mr.1 *
      shb_explorationCoordinateWeight beta J
        (shb_BackboneExplorationDomain.advance d s) mr.2
  else 0



noncomputable def shb_selectorSwitchRightTerm
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (mr : shb_SelectorSwitchPair d s) : Real :=
  if shb_ActiveSegmentFiber d s hs mr.1 /\
      S.Fiber (shb_BackboneExplorationDomain.advance d s) ss mr.2
  then
    shb_explorationCoordinateWeight beta J d mr.1 *
      shb_explorationCoordinateWeight beta J
        (shb_BackboneExplorationDomain.advance d s) mr.2
  else 0





def shb_CurrentDynamicSelector.SwitchingLaw
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) : Prop :=
  forall d s ss (hs : s ∈ d.active),
    exists switch : shb_SelectorSwitchPair d s ≃ shb_SelectorSwitchPair d s,
      forall mr,
        shb_selectorSwitchLeftTerm S beta J d s ss mr =
          shb_selectorSwitchRightTerm S beta J d s ss hs (switch mr)



theorem shb_currentDynamicSelector_actualMass_nil
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) (d : shb_ExplorationDomain V) :
    S.actualMass beta J d [] = currentSum d.graph beta J ∅ := by
  unfold shb_CurrentDynamicSelector.actualMass
    shb_actualExplorationFiberMass currentSum
  apply tsum_congr
  intro m
  have hiff :
      (sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d [] /\
          S.select d m = []) <->
        sources d.graph (ofEdgeFun d.graph m) = ∅ := by
    rw [S.sourceClass_nil d]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, S.select_nil_of_sources_empty d m h⟩
  by_cases h : sources d.graph (ofEdgeFun d.graph m) = ∅
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]


theorem shb_currentDynamicSelector_actualMass_inactive
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∉ d.active) :
    S.actualMass beta J d (s :: ss) = 0 := by
  unfold shb_CurrentDynamicSelector.actualMass
    shb_actualExplorationFiberMass
  rw [show (fun m : d.graph.edgeFinset -> Nat =>
      if sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d (s :: ss) /\
          S.select d m = s :: ss then
        weight d.graph beta J (ofEdgeFun d.graph m) else 0) =
      (fun _ => 0) by
    funext m
    rw [if_neg]
    intro h
    exact S.select_ne_cons_of_not_active d s ss m hs h.2]
  exact tsum_zero



theorem shb_currentDynamicSelector_actualMass_active
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (hswitch : S.SwitchingLaw beta J)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  let d' := shb_BackboneExplorationDomain.advance d s
  obtain ⟨switch, hswitchTerm⟩ := hswitch d s ss hs
  have hfull : Summable (fun m : d.graph.edgeFinset -> Nat =>
      if S.Fiber d (s :: ss) m then
        shb_explorationCoordinateWeight beta J d m else 0) :=
    shb_summable_explorationFiberIndicator beta J d _
  have hvac : Summable (fun r : d'.graph.edgeFinset -> Nat =>
      if sources d'.graph (ofEdgeFun d'.graph r) = ∅ then
        shb_explorationCoordinateWeight beta J d' r else 0) :=
    shb_summable_explorationFiberIndicator beta J d' _
  have hstep : Summable (fun m : d.graph.edgeFinset -> Nat =>
      if shb_ActiveSegmentFiber d s hs m then
        shb_explorationCoordinateWeight beta J d m else 0) :=
    shb_summable_explorationFiberIndicator beta J d _
  have hsuffix : Summable (fun r : d'.graph.edgeFinset -> Nat =>
      if S.Fiber d' ss r then
        shb_explorationCoordinateWeight beta J d' r else 0) :=
    shb_summable_explorationFiberIndicator beta J d' _
  have hleft :
      (∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchLeftTerm S beta J d s ss mr) =
        S.actualMass beta J d (s :: ss) * currentSum d'.graph beta J ∅ := by
    rw [show (∑' mr : shb_SelectorSwitchPair d s,
        shb_selectorSwitchLeftTerm S beta J d s ss mr) =
      (∑' mr : (d.graph.edgeFinset -> Nat) × (d'.graph.edgeFinset -> Nat),
        (if S.Fiber d (s :: ss) mr.1 then
            shb_explorationCoordinateWeight beta J d mr.1 else 0) *
          (if sources d'.graph (ofEdgeFun d'.graph mr.2) = ∅ then
            shb_explorationCoordinateWeight beta J d' mr.2 else 0)) by
      apply tsum_congr
      intro mr
      unfold shb_selectorSwitchLeftTerm
      by_cases h₁ : S.Fiber d (s :: ss) mr.1 <;>
        by_cases h₂ : sources d'.graph (ofEdgeFun d'.graph mr.2) = ∅ <;>
        simp [h₁, h₂, d']]
    rw [shb_tsum_prod_factor _ _ hfull hvac]
    unfold shb_explorationCoordinateWeight
    rw [← S.actualMass_eq_fiberTsum beta J d (s :: ss)]
    unfold currentSum
    rfl
  have hright :
      (∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchRightTerm S beta J d s ss hs mr) =
        shb_segmentNum beta J d s * S.actualMass beta J d' ss := by
    rw [show (∑' mr : shb_SelectorSwitchPair d s,
        shb_selectorSwitchRightTerm S beta J d s ss hs mr) =
      (∑' mr : (d.graph.edgeFinset -> Nat) × (d'.graph.edgeFinset -> Nat),
        (if shb_ActiveSegmentFiber d s hs mr.1 then
            shb_explorationCoordinateWeight beta J d mr.1 else 0) *
          (if S.Fiber d' ss mr.2 then
            shb_explorationCoordinateWeight beta J d' mr.2 else 0)) by
      apply tsum_congr
      intro mr
      unfold shb_selectorSwitchRightTerm
      by_cases h₁ : shb_ActiveSegmentFiber d s hs mr.1 <;>
        by_cases h₂ : S.Fiber d' ss mr.2 <;> simp [h₁, h₂, d']]
    rw [shb_tsum_prod_factor _ _ hstep hsuffix,
      shb_activeSegmentFiberMass_eq_segmentNum beta J d s hs]
    unfold shb_explorationCoordinateWeight
    rw [← S.actualMass_eq_fiberTsum beta J d' ss]
  rw [← hleft, ← hright]
  calc
    (∑' mr : shb_SelectorSwitchPair d s,
        shb_selectorSwitchLeftTerm S beta J d s ss mr) =
        ∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchRightTerm S beta J d s ss hs (switch mr) :=
      tsum_congr hswitchTerm
    _ = ∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchRightTerm S beta J d s ss hs mr :=
      switch.tsum_eq _



theorem shb_CurrentDynamicSelector.actualFiberRealizes
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (hswitch : S.SwitchingLaw beta J) :
    shb_ActualExplorationFiberRealizes beta J (S.actualMass beta J) := by
  refine ⟨shb_currentDynamicSelector_actualMass_nil S beta J, ?_, ?_⟩
  · intro d s ss hs
    exact shb_currentDynamicSelector_actualMass_active S beta J
      hswitch d s ss hs
  · intro d s ss hs
    exact shb_currentDynamicSelector_actualMass_inactive S beta J d s ss hs



theorem shb_CurrentDynamicSelector.actualMass_eq_generated
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (hswitch : S.SwitchingLaw beta J) :
    S.actualMass beta J = shb_generatedExplorationFiberMass beta J := by
  exact shb_actualExplorationFiberMass_eq_generated beta J S.sourceClass
    (fun d word m => S.select d m = word)
    (S.actualFiberRealizes beta J hswitch)

end

end StatMech.Sharpness
