/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateToggleObstruction

/-!
# Bondwise segment programs and coordinate certificates

Partial current dynamic selectors built from a bondwise scanning program, and certificates that
turn bondwise suffix events into the coordinate toggle data of `P2CoordinateToggleObstruction`.

## i. Overview

First, two negative remarks: a selector fiber cannot coincide with a bondwise suffix event along
the empty word for currents with sources
(`no_nilFiber_iff_bondwiseSuffixEvent_of_sources_ne_empty`), and no decoding of bond lists into
words makes all fibers equal to suffix events once two different words are decoded from satisfied
events (`no_functional_fiber_bridge_of_nonempty_event`).

A bondwise segment program scans bonds with a dynamic edge exploration, encodes words of segments
as bond lists, reads bonds off a flux through a bit map, and has a terminal condition. Its complete
event for a word is "the encoded word is selected by the scan and the terminal condition holds".
A complete bondwise selector specification (functionality of complete events, sources determined
by the word, the empty word iff no sources, active first segment) yields a partial current dynamic
selector whose fibers are the complete events (`CompleteBondwiseSelectorSpec.toPartialSelector`,
`fiber_iff_completeEvent`). Under freshness and a locality hypothesis on the terminal event, its
fibers are events outside the determined cut.

A bondwise coordinate certificate packages two fresh suffixes, a contributing-path selector in the
determined cut with the right sources, and normal forms of both pair fibers as products of suffix
events; it yields coordinate toggle data (`BondwiseCoordinateCertificate.toCoordinateToggleData`).

Headline fidelity:
- `CompleteBondwiseSelectorSpec.toPartialSelector`, `fiber_iff_completeEvent` are proved from the
  structure fields of `CompleteBondwiseSelectorSpec` (instances are constructed in
  `ConcreteBondProgram` and `MultiStepBondProgram`).
- `completeEvent_fluxEventOutsideCut`, `fiber_fluxEventOutsideCut` are conditional on `hstate`,
  `hfresh` and the locality hypothesis `hterminal`.
- `BondwiseCoordinateCertificate.toCoordinateToggleData` takes a certificate, which is empty when
  the selector's actual mass on `s :: ss` is nonzero and the toggle source is nonempty
  (`bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero`,
  `ConcreteSelectorObstruction`).

## ii. Key results

- `no_functional_fiber_bridge_of_nonempty_event` : fibers are not functional suffix events
- `BondwiseSegmentProgram` : bondwise scanning programs
- `CompleteBondwiseSelectorSpec.toPartialSelector` : the partial selector of a complete
  specification
- `BondwiseCoordinateCertificate.toCoordinateToggleData` : coordinate toggle data from a
  certificate (certificates are empty in the relevant case, see above)

## iii. Table of contents

- A. Suffix events and selector fibers
- B. Bondwise segment programs
- C. Complete bondwise selector specifications
- D. Bondwise coordinate certificates

## iv. References

None beyond those in the imported modules.

-/

@[expose] public section

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Classical decidability of adjacency, used throughout this file. -/
noncomputable local instance candidateDecidableAdj (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open BackboneP2CoordinateToggleObstruction
open FluxEdgeCopy

variable {D : Type*}

/-! ## A. Suffix events and selector fibers -/

@[simp] lemma bondwiseSuffixEvent_nil
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : Nat -> Bool) (m : G.edgeFinset -> Nat) :
    BondwiseSuffixEvent G X x [] bit m := by
  simp [BondwiseSuffixEvent]

/-- For a current with sources, the fiber of the empty word is not the (always true) empty suffix
event. -/
lemma no_nilFiber_iff_bondwiseSuffixEvent_of_sources_ne_empty
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : Nat -> Bool)
    (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) :
    ¬(S.Fiber d [] m ↔ BondwiseSuffixEvent d.graph X x [] bit m) := by
  intro hbridge
  have hfiber : S.Fiber d [] m := hbridge.mpr (bondwiseSuffixEvent_nil _ _ _ _ _)
  exact hsrc ((S.select?_eq_some_nil_iff d m).mp hfiber)

/-- No decoding of bond lists into words makes every fiber equal to the corresponding suffix event,
if a satisfied event decodes to a word different from the decoding of the empty list. -/
lemma no_functional_fiber_bridge_of_nonempty_event
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : Nat -> Bool) (bonds : List (Sym2 V))
    (decode : List (Sym2 V) -> List (shb_ExplorationSegment V))
    (hdecode : decode [] ≠ decode bonds)
    (hbonds : BondwiseSuffixEvent d.graph X x bonds bit m)
    (hbridge : forall bs,
      S.Fiber d (decode bs) m <->
        BondwiseSuffixEvent d.graph X x bs bit m) : False := by
  have hnil : S.select? d m = some (decode []) :=
    (hbridge []).mpr (bondwiseSuffixEvent_nil _ _ _ _ _)
  have hword : S.select? d m = some (decode bonds) :=
    (hbridge bonds).mpr hbonds
  apply hdecode
  exact Option.some.inj (hnil.symm.trans hword)

/-! ## B. Bondwise segment programs -/

/-- A bondwise segment program: a scanning exploration on bonds, an initial state for each domain,
an encoding of words of segments as bond lists, a bit map reading bonds off a flux, and a terminal
condition. -/
structure BondwiseSegmentProgram (V : Type*) [Fintype V] [DecidableEq V] where
  State : Type*
  scan : shb_DynamicEdgeExploration State (Sym2 V)
  initial : shb_ExplorationDomain V -> State
  encode : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  bit : Nat -> Bool
  terminal : State -> (Sym2 V -> Bool) -> Prop

/-- The terminal condition holds at the state reached after scanning the encoded word. -/
def BondwiseSegmentProgram.TerminalEvent
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) : Prop :=
  P.terminal (P.scan.residual (P.initial d) (P.encode d word))
    (fluxBitConfig d.graph P.bit m)

/-- The complete event of a word: the encoded word is selected by the scan and the terminal
condition holds. -/
def BondwiseSegmentProgram.CompleteEvent
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) : Prop :=
  BondwiseSuffixEvent d.graph P.scan (P.initial d) (P.encode d word) P.bit m /\
    P.TerminalEvent d word m

/-- Classical decidability of complete events. -/
noncomputable instance completeEventDecidable
    (P : BondwiseSegmentProgram V) (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) :
    DecidablePred (P.CompleteEvent d word) := Classical.decPred _

/-- Classical decidability of terminal events. -/
noncomputable instance terminalEventDecidable
    (P : BondwiseSegmentProgram V) (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) :
    DecidablePred (P.TerminalEvent d word) := Classical.decPred _

/-- Under freshness and locality of the terminal event, the complete event is an event outside the
determined cut. -/
lemma completeEvent_fluxEventOutsideCut
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V))
    (x : P.State) (accepted : Sym2 V)
    (hstate : P.initial d = P.scan.advance x accepted)
    (hfresh : SuffixFresh P.scan x accepted (P.encode d word))
    (m : d.graph.edgeFinset -> Nat)
    (hterminal : FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.TerminalEvent d word)) :
    FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.CompleteEvent d word) := by
  intro T U hout
  have hevent := bondwiseSuffixEvent_fluxEventOutsideCut d.graph P.scan x
    accepted (P.encode d word) hfresh P.bit m T U hout
  have hterminalEvent := hterminal T U hout
  constructor
  · rintro ⟨hselect, hterminal⟩
    refine ⟨?_, hterminalEvent.mp hterminal⟩
    have hresult := hevent.mp (by simpa [hstate] using hselect)
    simpa [hstate] using hresult
  · rintro ⟨hselect, hterminal⟩
    refine ⟨?_, hterminalEvent.mpr hterminal⟩
    have hresult := hevent.mpr (by simpa [hstate] using hselect)
    simpa [hstate] using hresult

/-! ## C. Complete bondwise selector specifications -/

/-- A complete bondwise selector specification: a source class with empty class for the empty word,
such that complete events are functional in the word, determine the sources, hold for the empty
word exactly for sourceless currents, and start with an active segment. -/
structure CompleteBondwiseSelectorSpec (P : BondwiseSegmentProgram V) where
  sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  sourceClass_nil : ∀ d, sourceClass d [] = ∅
  complete_functional : ∀ d m word word',
    P.CompleteEvent d word m -> P.CompleteEvent d word' m -> word = word'
  sources_eq_sourceClass_of_complete : ∀ d m word,
    P.CompleteEvent d word m ->
      sources d.graph (ofEdgeFun d.graph m) = sourceClass d word
  complete_nil_iff : ∀ d m,
    P.CompleteEvent d [] m ↔
      sources d.graph (ofEdgeFun d.graph m) = ∅
  head_active_of_complete : ∀ d m s ss,
    P.CompleteEvent d (s :: ss) m -> s ∈ d.active

/-- The word whose complete event holds, if any. -/
noncomputable def CompleteBondwiseSelectorSpec.select?
    {P : BondwiseSegmentProgram V} (_R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    Option (List (shb_ExplorationSegment V)) := by
  classical
  exact if h : ∃ word, P.CompleteEvent d word m then some (Classical.choose h)
    else none

/-- The partial current dynamic selector of a complete specification. -/
noncomputable def CompleteBondwiseSelectorSpec.toPartialSelector
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P) :
    shb_PartialCurrentDynamicSelector (V := V) where
  sourceClass := R.sourceClass
  select? := R.select?
  sourceClass_nil := R.sourceClass_nil
  sources_eq_sourceClass_of_select := by
    intro d m word hword
    unfold CompleteBondwiseSelectorSpec.select? at hword
    split at hword
    · rename_i hex
      have hchosen : Classical.choose hex = word := Option.some.inj hword
      exact R.sources_eq_sourceClass_of_complete d m word
        (hchosen ▸ Classical.choose_spec hex)
    · simp at hword
  select?_eq_some_nil_iff := by
    intro d m
    constructor
    · intro hselect
      unfold CompleteBondwiseSelectorSpec.select? at hselect
      split at hselect
      · rename_i hex
        have hchosen : Classical.choose hex = [] := Option.some.inj hselect
        exact (R.complete_nil_iff d m).mp
          (hchosen ▸ Classical.choose_spec hex)
      · simp at hselect
    · intro hsrc
      have hnil : P.CompleteEvent d [] m := (R.complete_nil_iff d m).mpr hsrc
      let hex : ∃ word, P.CompleteEvent d word m := ⟨[], hnil⟩
      unfold CompleteBondwiseSelectorSpec.select?
      rw [dite_eq_left hex]
      apply congrArg some
      exact R.complete_functional d m (Classical.choose hex) []
        (Classical.choose_spec hex) hnil
  head_active_of_select := by
    intro d m s ss hselect
    unfold CompleteBondwiseSelectorSpec.select? at hselect
    split at hselect
    · rename_i hex
      have hchosen : Classical.choose hex = s :: ss := Option.some.inj hselect
      exact R.head_active_of_complete d m s ss
        (hchosen ▸ Classical.choose_spec hex)
    · simp at hselect

/-- The fibers of the partial selector are the complete events. -/
lemma CompleteBondwiseSelectorSpec.fiber_iff_completeEvent
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    R.toPartialSelector.Fiber d word m <-> P.CompleteEvent d word m := by
  constructor
  · intro hfiber
    unfold shb_PartialCurrentDynamicSelector.Fiber at hfiber
    change R.select? d m = some word at hfiber
    unfold CompleteBondwiseSelectorSpec.select? at hfiber
    split at hfiber
    · rename_i hex
      have hchosen : Classical.choose hex = word := Option.some.inj hfiber
      exact hchosen ▸ Classical.choose_spec hex
    · simp at hfiber
  · intro hcomplete
    let hex : ∃ candidate, P.CompleteEvent d candidate m := ⟨word, hcomplete⟩
    unfold shb_PartialCurrentDynamicSelector.Fiber
    change R.select? d m = some word
    unfold CompleteBondwiseSelectorSpec.select?
    rw [dite_eq_left hex]
    apply congrArg some
    exact R.complete_functional d m
      (Classical.choose hex) word (Classical.choose_spec hex) hcomplete

/-- Where the terminal event holds, the fiber of a word is the suffix event of its encoding. -/
lemma CompleteBondwiseSelectorSpec.fiber_iff_bondwiseSuffixEvent
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat)
    (hterminal : P.TerminalEvent d word m) :
    R.toPartialSelector.Fiber d word m ↔
      BondwiseSuffixEvent d.graph P.scan (P.initial d)
        (P.encode d word) P.bit m := by
  rw [R.fiber_iff_completeEvent]
  simp [BondwiseSegmentProgram.CompleteEvent, hterminal]

/-- Under freshness and locality of the terminal event, fibers are events outside the determined
cut. -/
lemma CompleteBondwiseSelectorSpec.fiber_fluxEventOutsideCut
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (x : P.State) (accepted : Sym2 V)
    (hstate : P.initial d = P.scan.advance x accepted)
    (hfresh : SuffixFresh P.scan x accepted (P.encode d word))
    (m : d.graph.edgeFinset -> Nat)
    (hterminal : FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.TerminalEvent d word)) :
    FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (R.toPartialSelector.Fiber d word) := by
  intro T U hout
  rw [R.fiber_iff_completeEvent, R.fiber_iff_completeEvent]
  exact completeEvent_fluxEventOutsideCut P d word x accepted hstate hfresh
    m hterminal T U hout

/-! ## D. Bondwise coordinate certificates -/

/-- A flux contributes to one of the two pair masses of the active cut resummation identity. -/
abbrev CoordinatePairContributes
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (m : d.graph.edgeFinset -> Nat) : Prop :=
  PairContributes d.graph beta J m
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)

/-- A bondwise coordinate certificate: two fresh suffixes, a contributing-path selector in the
determined cut with sources `stepToggleSource`, and normal forms of both pair fibers as products of
the two suffix events. Empty when the actual mass is nonzero and the toggle source nonempty
(`bondwiseCoordinateCertificate_isEmpty_of_actualMass_ne_zero`). -/
structure BondwiseCoordinateCertificate
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix₁ suffix₂ : List (Sym2 V))
    (bit₁ bit₂ : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) where
  fresh₁ : SuffixFresh X x accepted suffix₁
  fresh₂ : SuffixFresh X x accepted suffix₂
  path : ContributingPathSelector d.graph beta J
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
  path_sources : ∀ m hm,
    RandomCurrent.sources (endsM d.graph m) (path m hm) =
      stepToggleSource S d s ss
  path_supported : ∀ m hm,
    SupportedInCut d.graph m
      ((X.bondwiseOrdered.tests x).determinedCut accepted) (path m hm)
  left_normal_form : ∀ m
      (_hm : CoordinatePairContributes S beta J d s ss hs m) T,
    (S.Fiber d (s :: ss) (profileFlux d.graph m T) ∧
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) ↔
      (BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₁ bit₁ (profileFlux d.graph m T) ∧
        BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₂ bit₂ (profileFlux d.graph m (univ \ T)))
  right_normal_form : ∀ m
      (_hm : CoordinatePairContributes S beta J d s ss hs m) T,
    (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) ∧
        liftedResidualFiber S d s ss
          (profileFlux d.graph m (univ \ T))) ↔
      (BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₁ bit₁ (profileFlux d.graph m T) ∧
        BondwiseSuffixEvent d.graph X (X.advance x accepted)
          suffix₂ bit₂ (profileFlux d.graph m (univ \ T)))

/-- Coordinate toggle data from a bondwise coordinate certificate. -/
noncomputable def BondwiseCoordinateCertificate.toCoordinateToggleData
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V)
    (suffix₁ suffix₂ : List (Sym2 V))
    (bit₁ bit₂ : Nat -> Bool)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (R : BondwiseCoordinateCertificate X x accepted suffix₁ suffix₂
      bit₁ bit₂ S beta J d s ss hs) :
    CoordinateToggleData S beta J d s ss hs where
  path := R.path
  path_sources := R.path_sources
  transport := by
    intro m hm T
    let Q : (d.graph.edgeFinset -> Nat) -> Prop :=
      BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix₁ bit₁
    let U : (d.graph.edgeFinset -> Nat) -> Prop :=
      BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix₂ bit₂
    have hQ : FluxEventOutsideCut d.graph m
        ((X.bondwiseOrdered.tests x).determinedCut accepted) Q :=
      bondwiseSuffixEvent_fluxEventOutsideCut d.graph X x accepted suffix₁
        R.fresh₁ bit₁ m
    have hU : FluxEventOutsideCut d.graph m
        ((X.bondwiseOrdered.tests x).determinedCut accepted) U :=
      bondwiseSuffixEvent_fluxEventOutsideCut d.graph X x accepted suffix₂
        R.fresh₂ bit₂ m
    exact (R.left_normal_form m hm T).trans
      ((pairTransport_of_fluxEventsOutsideCut d.graph m
        ((X.bondwiseOrdered.tests x).determinedCut accepted) Q U hQ hU
        (R.path m hm) (R.path_supported m hm) T).trans
          (R.right_normal_form m hm (T ∆ R.path m hm)).symm)

end BackboneConcreteSelector

end

end StatMech.Sharpness
