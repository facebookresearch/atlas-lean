/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteSelectorObstruction

/-!
# Asymmetric bondwise coordinate certificates

Coordinate certificates in which the two sides of the active cut resummation identity are put in
normal form by possibly different bondwise run specifications, and the canonical certificate of a
complete bondwise selector specification. The canonical certificate exists exactly when a
canonical toggle exists, and several obstructions to such toggles are proved.

## i. Overview

A bondwise run specification is a scanning exploration with a state, a suffix of bonds, a bit map
and a terminal condition on the flux; its event is "the suffix is selected and the terminal
condition holds". Every predicate on fluxes is the event of some run specification
(`BondwiseRunSpec.ofPredicate`). A pair event asks the two parts of a labeled split to satisfy two
run events, and toggle covariance of two run specifications along a path says that toggling the
path carries one event to the other; covariance in each component gives a pair toggle.

An asymmetric bondwise coordinate certificate gives a contributing-path selector with sources
`stepToggleSource`, normal forms of the left and right pair fibers as pair events, and a pair
toggle between them; it yields coordinate toggle data and hence the active cut resummation
identity (`AsymmetricBondwiseCoordinateCertificate.actualMass_active`). For a complete bondwise
selector specification there are canonical run specifications for the four fibers, and the
canonical certificate exists iff the canonical toggle exists
(`nonempty_canonicalCertificate_iff_toggleExists`).

Headline fidelity:
- `AsymmetricBondwiseCoordinateCertificate.actualMass_active` is conditional on a certificate.
- `CompleteBondwiseSelectorSpec.nonempty_canonicalCertificate_iff_toggleExists` and
  `path_sources_of_canonical_toggle` (the source condition is automatic for a canonical toggle)
  are proved for every `CompleteBondwiseSelectorSpec`.
- The canonical toggle cannot exist when the active identity fails
  (`not_toggleExists_of_clearedP2_ne`), and it forces an empty toggle source when the right pair
  event is toggle invariant (`stepToggleSource_eq_empty_of_right_invariant`) or when the active
  head event is local outside the cut (`stepToggleSource_eq_empty_of_activeHead_outsideCut`,
  `not_activeHead_outsideCut_of_toggleSource_ne_empty`). No canonical toggle is constructed for
  any selector; it is a form of the backbone chain rule (P2).

## ii. Key results

- `BondwiseRunSpec` : bondwise run specifications and their events
- `BondwisePairEvent.toggle_iff_of_componentwise` : componentwise covariance gives a pair toggle
- `AsymmetricBondwiseCoordinateCertificate.actualMass_active` : the active identity from a
  certificate (conditional)
- `CompleteBondwiseSelectorSpec.nonempty_canonicalCertificate_iff_toggleExists` : canonical
  certificates exist iff canonical toggles exist
- `CompleteBondwiseSelectorSpec.not_toggleExists_of_clearedP2_ne`,
  `CompleteBondwiseSelectorSpec.not_activeHead_outsideCut_of_toggleSource_ne_empty` :
  obstructions to canonical toggles

## iii. Table of contents

- A. Suffix and run specifications
- B. Pair events and toggle covariance
- C. Asymmetric coordinate certificates
- D. Run specifications of a segment program
- E. Canonical certificates
- F. Obstructions to canonical toggles
- G. Existence of canonical toggles

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
noncomputable local instance asymmetricCertificateDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open BackboneP2CoordinateToggleObstruction
open FluxEdgeCopy

variable {D : Type*}

/-! ## A. Suffix and run specifications -/

/-- A bondwise suffix specification: a scanning exploration with a state, a suffix of bonds and a
bit map reading bonds off a flux. -/
structure BondwiseSuffixSpec (V : Type*) [Fintype V] [DecidableEq V] where
  State : Type*
  scan : shb_DynamicEdgeExploration State (Sym2 V)
  state : State
  suffix : List (Sym2 V)
  bit : Nat -> Bool

/-- The suffix event of a suffix specification. -/
def BondwiseSuffixSpec.Event
    (E : BondwiseSuffixSpec V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) : Prop :=
  BondwiseSuffixEvent G E.scan E.state E.suffix E.bit m

/-- Classical decidability of suffix events. -/
noncomputable instance BondwiseSuffixSpec.eventDecidable
    (E : BondwiseSuffixSpec V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidablePred (E.Event G) := Classical.decPred _

/-- A bondwise run specification: a suffix specification together with a terminal condition on the
state reached and the flux. -/
structure BondwiseRunSpec (V : Type*) [Fintype V] [DecidableEq V] where
  State : Type*
  scan : shb_DynamicEdgeExploration State (Sym2 V)
  state : State
  suffix : List (Sym2 V)
  bit : Nat -> Bool
  terminal : State -> (Sym2 V -> Option Nat) -> Prop

/-- The flux as an optional value on unordered pairs (`none` off the graph). -/
noncomputable def fluxOptionConfig
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) : Sym2 V -> Option Nat :=
  fun e => if h : e ∈ G.edgeFinset then some (m ⟨e, h⟩) else none

/-- The terminal condition holds at the state reached after scanning the suffix. -/
def BondwiseRunSpec.TerminalEvent
    (E : BondwiseRunSpec V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) : Prop :=
  E.terminal (E.scan.residual E.state E.suffix) (fluxOptionConfig G m)

/-- The run event: the suffix is selected and the terminal condition holds. -/
def BondwiseRunSpec.Event
    (E : BondwiseRunSpec V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) : Prop :=
  BondwiseSuffixEvent G E.scan E.state E.suffix E.bit m /\
    E.TerminalEvent G m

/-- Classical decidability of run events. -/
noncomputable instance BondwiseRunSpec.eventDecidable
    (E : BondwiseRunSpec V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidablePred (E.Event G) := Classical.decPred _

/-- A suffix specification as a run specification with trivial terminal condition. -/
def BondwiseSuffixSpec.toRunSpec
    (E : BondwiseSuffixSpec V) : BondwiseRunSpec V where
  State := E.State
  scan := E.scan
  state := E.state
  suffix := E.suffix
  bit := E.bit
  terminal := fun _ _ => True

@[simp] lemma BondwiseSuffixSpec.toRunSpec_event
    (E : BondwiseSuffixSpec V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) :
    E.toRunSpec.Event G m <-> E.Event G m := by
  cases E
  simp [BondwiseRunSpec.Event, BondwiseRunSpec.TerminalEvent,
    BondwiseSuffixSpec.Event, BondwiseSuffixSpec.toRunSpec]

/-- The run specification whose event is a given predicate on fluxes (empty scan, the predicate as
terminal condition). -/
noncomputable def BondwiseRunSpec.ofPredicate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : (G.edgeFinset -> Nat) -> Prop) : BondwiseRunSpec V where
  State := Unit
  scan :=
    { edgeOrder := fun _ => []
      edgeOrder_nodup := by simp
      advance := fun _ _ => () }
  state := ()
  suffix := []
  bit := fun _ => false
  terminal := fun _ omega => Q (fun e => (omega e.1).getD 0)

@[simp] lemma BondwiseRunSpec.ofPredicate_event
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : (G.edgeFinset -> Nat) -> Prop)
    (m : G.edgeFinset -> Nat) :
    (BondwiseRunSpec.ofPredicate G Q).Event G m <-> Q m := by
  have hread :
      (fun e : G.edgeFinset => (fluxOptionConfig G m e.1).getD 0) = m := by
    funext e
    simp [fluxOptionConfig, e.2]
  simp [BondwiseRunSpec.ofPredicate, BondwiseRunSpec.Event,
    BondwiseRunSpec.TerminalEvent, BondwiseSuffixEvent, hread]

/-! ## B. Pair events and toggle covariance -/

/-- The pair event: the two parts of a labeled split satisfy the two run events. -/
def BondwisePairEvent
    (E₁ E₂ : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat)
    (T : Finset (Copy G m)) : Prop :=
  E₁.Event G (profileFlux G m T) /\
    E₂.Event G (profileFlux G m (univ \ T))

/-- Toggling `path` carries the event of `E` to the event of `F`. -/
def BondwiseRunToggleCovariance
    (E F : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (path : Finset (Copy G m)) : Prop :=
  ∀ T, E.Event G (profileFlux G m T) <->
    F.Event G (profileFlux G m (T ∆ path))

lemma BondwiseRunToggleCovariance.refl_of_outsideCut
    (E : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (path : Finset (Copy G m))
    (hpath : SupportedInCut G m cut path)
    (hE : FluxEventOutsideCut G m cut (E.Event G)) :
    BondwiseRunToggleCovariance E E G m path := by
  intro T
  exact fluxEvent_toggle_iff G m cut (E.Event G) hE T path hpath

/-- Toggle covariance in each component gives a toggle of pair events. -/
lemma BondwisePairEvent.toggle_iff_of_componentwise
    (left₁ left₂ right₁ right₂ : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (path : Finset (Copy G m))
    (h₁ : BondwiseRunToggleCovariance left₁ right₁ G m path)
    (h₂ : BondwiseRunToggleCovariance left₂ right₂ G m path)
    (T : Finset (Copy G m)) :
    BondwisePairEvent left₁ left₂ G m T <->
      BondwisePairEvent right₁ right₂ G m (T ∆ path) := by
  have hcompl : univ \ (T ∆ path) = (univ \ T) ∆ path :=
    compl_symmDiff G m T path
  constructor
  · rintro ⟨hleft₁, hleft₂⟩
    exact ⟨(h₁ T).mp hleft₁, by
      rw [hcompl]
      exact (h₂ (univ \ T)).mp hleft₂⟩
  · rintro ⟨hright₁, hright₂⟩
    exact ⟨(h₁ T).mpr hright₁, (h₂ (univ \ T)).mpr (by
      rw [hcompl] at hright₂
      exact hright₂)⟩

/-- Pair events of events outside a cut are invariant under toggles in the cut. -/
lemma BondwisePairEvent.toggle_iff_of_outsideCut
    (E₁ E₂ : BondwiseRunSpec V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (path : Finset (Copy G m))
    (hpath : SupportedInCut G m cut path)
    (h₁ : FluxEventOutsideCut G m cut (E₁.Event G))
    (h₂ : FluxEventOutsideCut G m cut (E₂.Event G))
    (T : Finset (Copy G m)) :
    BondwisePairEvent E₁ E₂ G m T <->
      BondwisePairEvent E₁ E₂ G m (T ∆ path) :=
  BondwisePairEvent.toggle_iff_of_componentwise E₁ E₂ E₁ E₂
    G m path
      (BondwiseRunToggleCovariance.refl_of_outsideCut
        E₁ G m cut path hpath h₁)
      (BondwiseRunToggleCovariance.refl_of_outsideCut
        E₂ G m cut path hpath h₂) T

/-! ## C. Asymmetric coordinate certificates -/

/-- An asymmetric bondwise coordinate certificate: a contributing-path selector with sources
`stepToggleSource`, normal forms of the left and right pair fibers as pair events of possibly
different run specifications, and a pair toggle between them. -/
structure AsymmetricBondwiseCoordinateCertificate
    (left₁ left₂ right₁ right₂ : BondwiseRunSpec V)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) where
  path : ContributingPathSelector d.graph beta J
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
  path_sources : ∀ m hm,
    RandomCurrent.sources (endsM d.graph m) (path m hm) =
      stepToggleSource S d s ss
  left_normal_form : ∀ m
      (_hm : CoordinatePairContributes S beta J d s ss hs m) T,
    (S.Fiber d (s :: ss) (profileFlux d.graph m T) /\
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) <->
      BondwisePairEvent left₁ left₂ d.graph m T
  right_normal_form : ∀ m
      (_hm : CoordinatePairContributes S beta J d s ss hs m) T,
    (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) /\
        liftedResidualFiber S d s ss
          (profileFlux d.graph m (univ \ T))) <->
      BondwisePairEvent right₁ right₂ d.graph m T
  bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes S beta J d s ss hs m) T,
    BondwisePairEvent left₁ left₂ d.graph m T <->
      BondwisePairEvent right₁ right₂ d.graph m (T ∆ path m hm)

/-- Coordinate toggle data from an asymmetric certificate. -/
noncomputable def AsymmetricBondwiseCoordinateCertificate.toCoordinateToggleData
    (left₁ left₂ right₁ right₂ : BondwiseRunSpec V)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (R : AsymmetricBondwiseCoordinateCertificate
      left₁ left₂ right₁ right₂ S beta J d s ss hs) :
    CoordinateToggleData S beta J d s ss hs where
  path := R.path
  path_sources := R.path_sources
  transport := by
    intro m hm T
    exact (R.left_normal_form m hm T).trans
      ((R.bondwise_toggle m hm T).trans
        (R.right_normal_form m hm (T ∆ R.path m hm)).symm)

/-- An asymmetric certificate gives the active cut resummation identity. -/
lemma AsymmetricBondwiseCoordinateCertificate.actualMass_active
    (left₁ left₂ right₁ right₂ : BondwiseRunSpec V)
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (R : AsymmetricBondwiseCoordinateCertificate
      left₁ left₂ right₁ right₂ S beta J d s ss hs) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  exact actualMass_active_of_data S beta J d s ss hs
    (R.toCoordinateToggleData left₁ left₂ right₁ right₂
      S beta J d s ss hs)

/-! ## D. Run specifications of a segment program -/

/-- The suffix specification of the encoding of a word. -/
def BondwiseSegmentProgram.suffixSpec
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) : BondwiseSuffixSpec V where
  State := P.State
  scan := P.scan
  state := P.initial d
  suffix := P.encode d word
  bit := P.bit

@[simp] lemma BondwiseSegmentProgram.suffixSpec_event
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    (P.suffixSpec d word).Event d.graph m =
      BondwiseSuffixEvent d.graph P.scan (P.initial d)
        (P.encode d word) P.bit m := rfl

/-- The run specification of the encoding of a word, with the program's terminal condition. -/
def BondwiseSegmentProgram.runSpec
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) : BondwiseRunSpec V where
  State := P.State
  scan := P.scan
  state := P.initial d
  suffix := P.encode d word
  bit := P.bit
  terminal := fun state omega =>
    P.terminal state (fun e => (omega e).map P.bit |>.getD false)

/-- The run event of a word is its complete event. -/
@[simp] lemma BondwiseSegmentProgram.runSpec_event
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    (P.runSpec d word).Event d.graph m <-> P.CompleteEvent d word m := by
  apply and_congr Iff.rfl
  change P.terminal
      (P.scan.residual (P.initial d) (P.encode d word))
        (fun e => ((fluxOptionConfig d.graph m e).map P.bit).getD false) <->
    P.terminal (P.scan.residual (P.initial d) (P.encode d word))
      (fluxBitConfig d.graph P.bit m)
  apply iff_of_eq
  congr 1
  funext e
  by_cases he : e ∈ d.graph.edgeFinset <;>
    simp [fluxOptionConfig, fluxBitConfig, he]

lemma CompleteBondwiseSelectorSpec.fiber_iff_runSpec_event
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    R.toPartialSelector.Fiber d word m <->
      (P.runSpec d word).Event d.graph m := by
  exact (R.fiber_iff_completeEvent d word m).trans
    (P.runSpec_event d word m).symm

/-- The complete event of a word in the residual domain, lifted to fluxes of the domain graph. -/
def BondwiseSegmentProgram.LiftedRunEvent
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V)) :
    (d.graph.edgeFinset -> Nat) -> Prop :=
  LiftedPredicate (d.graph.deleteEdges_le s.edgeSet)
    ((P.runSpec (shb_BackboneExplorationDomain.advance d s) word).Event
      (shb_BackboneExplorationDomain.advance d s).graph)

/-- The run specification of the lifted residual vacuum predicate. -/
noncomputable def residualVacuumRunSpec
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    BondwiseRunSpec V :=
  BondwiseRunSpec.ofPredicate d.graph (liftedResidualVacuum d s)

/-- The run specification of the active segment fiber. -/
noncomputable def activeSegmentRunSpec
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) : BondwiseRunSpec V :=
  BondwiseRunSpec.ofPredicate d.graph (shb_ActiveSegmentFiber d s hs)

/-- The run specification of the lifted residual run event. -/
noncomputable def BondwiseSegmentProgram.liftedResidualRunSpec
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V)) : BondwiseRunSpec V :=
  BondwiseRunSpec.ofPredicate d.graph (P.LiftedRunEvent d s word)

@[simp] lemma residualVacuumRunSpec_event
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    (residualVacuumRunSpec d s).Event d.graph m <->
      liftedResidualVacuum d s m := by
  exact BondwiseRunSpec.ofPredicate_event d.graph _ m

@[simp] lemma activeSegmentRunSpec_event
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (m : d.graph.edgeFinset -> Nat) :
    (activeSegmentRunSpec d s hs).Event d.graph m <->
      shb_ActiveSegmentFiber d s hs m := by
  exact BondwiseRunSpec.ofPredicate_event d.graph _ m

@[simp] lemma BondwiseSegmentProgram.liftedResidualRunSpec_event
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    (P.liftedResidualRunSpec d s word).Event d.graph m <->
      P.LiftedRunEvent d s word m := by
  exact BondwiseRunSpec.ofPredicate_event d.graph _ m

/-- Classical decidability of lifted run events. -/
noncomputable instance BondwiseSegmentProgram.liftedRunEventDecidable
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V)) :
    DecidablePred (P.LiftedRunEvent d s word) := Classical.decPred _

lemma CompleteBondwiseSelectorSpec.liftedResidualFiber_iff_liftedRunEvent
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V))
    (q : d.graph.edgeFinset -> Nat) :
    liftedResidualFiber R.toPartialSelector d s word q <->
      P.LiftedRunEvent d s word q := by
  constructor
  · rintro ⟨r, hr, hfiber⟩
    exact ⟨r, hr, (R.fiber_iff_runSpec_event
      (shb_BackboneExplorationDomain.advance d s) word r).mp hfiber⟩
  · rintro ⟨r, hr, hrun⟩
    exact ⟨r, hr, (R.fiber_iff_runSpec_event
      (shb_BackboneExplorationDomain.advance d s) word r).mpr hrun⟩

lemma CompleteBondwiseSelectorSpec.leftPairNormalForm
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (vacuum : BondwiseRunSpec V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) (T : Finset (Copy d.graph m))
    (hvacuum :
      liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T)) <->
        vacuum.Event d.graph (profileFlux d.graph m (univ \ T))) :
    (R.toPartialSelector.Fiber d (s :: ss)
          (profileFlux d.graph m T) /\
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) <->
      BondwisePairEvent (P.runSpec d (s :: ss)) vacuum d.graph m T := by
  exact and_congr
    (R.fiber_iff_runSpec_event d (s :: ss) (profileFlux d.graph m T))
    hvacuum

lemma CompleteBondwiseSelectorSpec.rightPairNormalForm
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (head residual : BondwiseRunSpec V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (m : d.graph.edgeFinset -> Nat) (T : Finset (Copy d.graph m))
    (hhead :
      shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) <->
        head.Event d.graph (profileFlux d.graph m T))
    (hresidual :
      P.LiftedRunEvent d s ss (profileFlux d.graph m (univ \ T)) <->
        residual.Event d.graph (profileFlux d.graph m (univ \ T))) :
    (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) /\
        liftedResidualFiber R.toPartialSelector d s ss
          (profileFlux d.graph m (univ \ T))) <->
      BondwisePairEvent head residual d.graph m T := by
  exact and_congr hhead
    ((R.liftedResidualFiber_iff_liftedRunEvent d s ss
      (profileFlux d.graph m (univ \ T))).trans hresidual)

/-! ## E. Canonical certificates -/

/-- An asymmetric certificate for the partial selector of a complete specification, from a vacuum
normal form, a right normal form and a pair toggle. -/
noncomputable def CompleteBondwiseSelectorSpec.toAsymmetricCertificate
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (vacuum right₁ right₂ : BondwiseRunSpec V)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
        stepToggleSource R.toPartialSelector d s ss)
    (vacuum_normal_form : ∀ m
      (_hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T)) <->
        vacuum.Event d.graph (profileFlux d.graph m (univ \ T)))
    (right_normal_form : ∀ m
      (_hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) /\
          liftedResidualFiber R.toPartialSelector d s ss
            (profileFlux d.graph m (univ \ T))) <->
        BondwisePairEvent right₁ right₂ d.graph m T)
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss)) vacuum d.graph m T <->
        BondwisePairEvent right₁ right₂ d.graph m (T ∆ path m hm)) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) vacuum right₁ right₂
      R.toPartialSelector beta J d s ss hs where
  path := path
  path_sources := path_sources
  left_normal_form := by
    intro m hm T
    exact R.leftPairNormalForm vacuum d s ss m T
      (vacuum_normal_form m hm T)
  right_normal_form := right_normal_form
  bondwise_toggle := bondwise_toggle

set_option maxHeartbeats 800000 in
-- the `change` and labeled-split unfolding in this proof needs extra elaboration time
/-- For the canonical run specifications, a pair toggle forces the path to have sources
`stepToggleSource`. -/
lemma CompleteBondwiseSelectorSpec.path_sources_of_canonical_toggle
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
    ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
        stepToggleSource R.toPartialSelector d s ss := by
  intro m hm
  change PairContributes d.graph beta J m
    (R.toPartialSelector.sourceClass d (s :: ss))
    (stepToggleSource R.toPartialSelector d s ss)
    (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs)
    (liftedResidualFiber R.toPartialSelector d s ss) at hm
  rcases hm with hleft | hright
  · obtain ⟨T, hTsrc, hfull, hvacuum⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss))
          (R.toPartialSelector.Fiber d (s :: ss))
          (liftedResidualVacuum d s) hleft
    have hleftPair : BondwisePairEvent (P.runSpec d (s :: ss))
        (residualVacuumRunSpec d s) d.graph m T :=
      ⟨(R.fiber_iff_runSpec_event d (s :: ss)
          (profileFlux d.graph m T)).mp hfull,
        (residualVacuumRunSpec_event d s
          (profileFlux d.graph m (univ \ T))).mpr hvacuum⟩
    have hrightPair := (bondwise_toggle m (Or.inl hleft) T).mp hleftPair
    have hhead : shb_ActiveSegmentFiber d s hs
        (profileFlux d.graph m (T ∆ path m (Or.inl hleft))) :=
      (activeSegmentRunSpec_event d s hs _).mp hrightPair.1
    have htoggleSrc :
        RandomCurrent.sources (endsM d.graph m)
            (T ∆ path m (Or.inl hleft)) = {s.1, s.2.1} :=
      (FluxEdgeCopy.sources_eq d.graph m _).trans hhead.1
    rw [RandomCurrent.sources_symmDiff, hTsrc] at htoggleSrc
    change RandomCurrent.sources (endsM d.graph m)
        (path m (Or.inl hleft)) =
      R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1}
    calc
      RandomCurrent.sources (endsM d.graph m) (path m (Or.inl hleft)) =
          R.toPartialSelector.sourceClass d (s :: ss) ∆
            (R.toPartialSelector.sourceClass d (s :: ss) ∆
              RandomCurrent.sources (endsM d.graph m)
                (path m (Or.inl hleft))) := by simp
      _ = R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1} :=
        congrArg (fun U =>
          R.toPartialSelector.sourceClass d (s :: ss) ∆ U) htoggleSrc
  · obtain ⟨T, hTsrc, hhead, hresidual⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss) ∆
            stepToggleSource R.toPartialSelector d s ss)
          (shb_ActiveSegmentFiber d s hs)
          (liftedResidualFiber R.toPartialSelector d s ss) hright
    let hmRight : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m := Or.inr hright
    let togglePath : Finset (Copy d.graph m) := path m hmRight
    have hrightPair : BondwisePairEvent (activeSegmentRunSpec d s hs)
        (P.liftedResidualRunSpec d s ss) d.graph m T :=
      ⟨(activeSegmentRunSpec_event d s hs
          (profileFlux d.graph m T)).mpr hhead,
        (P.liftedResidualRunSpec_event d s ss
          (profileFlux d.graph m (univ \ T))).mpr
            ((R.liftedResidualFiber_iff_liftedRunEvent d s ss _).mp
              hresidual)⟩
    have hleftPair : BondwisePairEvent (P.runSpec d (s :: ss))
        (residualVacuumRunSpec d s) d.graph m
          (T ∆ togglePath) := by
      have htoggle :=
        (bondwise_toggle m hmRight (T ∆ togglePath)).mpr
      have hcancel : T ∆ togglePath ∆ path m hmRight = T := by
        simp only [togglePath, symmDiff_symmDiff_cancel_right]
      rw [hcancel] at htoggle
      exact htoggle hrightPair
    have hfull : R.toPartialSelector.Fiber d (s :: ss)
        (profileFlux d.graph m (T ∆ togglePath)) :=
      (R.fiber_iff_runSpec_event d (s :: ss) _).mpr hleftPair.1
    have htoggleSrc :
        RandomCurrent.sources (endsM d.graph m)
            (T ∆ togglePath) =
          R.toPartialSelector.sourceClass d (s :: ss) :=
      (FluxEdgeCopy.sources_eq d.graph m _).trans
        (R.toPartialSelector.sources_eq_sourceClass_of_select d _ _ hfull)
    have hTsrc' : RandomCurrent.sources (endsM d.graph m) T =
        {s.1, s.2.1} := by
      simpa [stepToggleSource, symmDiff_assoc] using hTsrc
    rw [RandomCurrent.sources_symmDiff, hTsrc'] at htoggleSrc
    change RandomCurrent.sources (endsM d.graph m) togglePath =
      R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1}
    calc
      RandomCurrent.sources (endsM d.graph m) togglePath =
          {s.1, s.2.1} ∆
            ({s.1, s.2.1} ∆ RandomCurrent.sources (endsM d.graph m)
              togglePath) := by simp
      _ = {s.1, s.2.1} ∆
          R.toPartialSelector.sourceClass d (s :: ss) :=
        congrArg (fun U => ({s.1, s.2.1} : Finset V) ∆ U) htoggleSrc
      _ = R.toPartialSelector.sourceClass d (s :: ss) ∆ {s.1, s.2.1} :=
        symmDiff_comm _ _

/-! ## F. Obstructions to canonical toggles -/

/-- At a contributing flux, the canonical right pair event holds for some labeled split. -/
lemma CompleteBondwiseSelectorSpec.exists_canonical_rightPair_of_contributes
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m) :
    ∃ T, BondwisePairEvent (activeSegmentRunSpec d s hs)
      (P.liftedResidualRunSpec d s ss) d.graph m T := by
  change PairContributes d.graph beta J m
    (R.toPartialSelector.sourceClass d (s :: ss))
    (stepToggleSource R.toPartialSelector d s ss)
    (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs)
    (liftedResidualFiber R.toPartialSelector d s ss) at hm
  rcases hm with hleft | hright
  · obtain ⟨T, _, hfull, hvacuum⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss))
          (R.toPartialSelector.Fiber d (s :: ss))
          (liftedResidualVacuum d s) hleft
    have hleftPair : BondwisePairEvent (P.runSpec d (s :: ss))
        (residualVacuumRunSpec d s) d.graph m T :=
      ⟨(R.fiber_iff_runSpec_event d (s :: ss)
          (profileFlux d.graph m T)).mp hfull,
        (residualVacuumRunSpec_event d s
          (profileFlux d.graph m (univ \ T))).mpr hvacuum⟩
    exact ⟨T ∆ path m (Or.inl hleft),
      (bondwise_toggle m (Or.inl hleft) T).mp hleftPair⟩
  · obtain ⟨T, _, hhead, hresidual⟩ :=
      exists_labeled_split_of_rawSourcePairFiberMass_ne_zero
        d.graph beta J m
          (R.toPartialSelector.sourceClass d (s :: ss) ∆
            stepToggleSource R.toPartialSelector d s ss)
          (shb_ActiveSegmentFiber d s hs)
          (liftedResidualFiber R.toPartialSelector d s ss) hright
    refine ⟨T, ?_⟩
    exact ⟨(activeSegmentRunSpec_event d s hs
        (profileFlux d.graph m T)).mpr hhead,
      (P.liftedResidualRunSpec_event d s ss
        (profileFlux d.graph m (univ \ T))).mpr
          ((R.liftedResidualFiber_iff_liftedRunEvent d s ss _).mp
            hresidual)⟩

/-- If the canonical right pair event is invariant under the toggle, the toggle source is empty. -/
lemma CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_right_invariant
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m)
    (right_invariant : ∀ T,
      BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
    stepToggleSource R.toPartialSelector d s ss = ∅ := by
  obtain ⟨T, hright⟩ := R.exists_canonical_rightPair_of_contributes
    beta J d s ss hs path bondwise_toggle m hm
  have hrightToggle := (right_invariant T).mp hright
  have hsrc : RandomCurrent.sources (endsM d.graph m) T = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m T).trans
      ((activeSegmentRunSpec_event d s hs _).mp hright.1).1
  have hsrcToggle : RandomCurrent.sources (endsM d.graph m)
      (T ∆ path m hm) = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m _).trans
      ((activeSegmentRunSpec_event d s hs _).mp hrightToggle.1).1
  rw [RandomCurrent.sources_symmDiff, hsrc] at hsrcToggle
  have hpathEmpty :
      RandomCurrent.sources (endsM d.graph m) (path m hm) = ∅ := by
    calc
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
          {s.1, s.2.1} ∆
            ({s.1, s.2.1} ∆
              RandomCurrent.sources (endsM d.graph m) (path m hm)) := by simp
      _ = {s.1, s.2.1} ∆ {s.1, s.2.1} :=
        congrArg (fun U => ({s.1, s.2.1} : Finset V) ∆ U) hsrcToggle
      _ = ∅ := symmDiff_self _
  exact (R.path_sources_of_canonical_toggle
    beta J d s ss hs path bondwise_toggle m hm).symm.trans hpathEmpty

/-- If the active head event is outside a cut containing the path, the toggle source is empty. -/
lemma CompleteBondwiseSelectorSpec.stepToggleSource_eq_empty_of_activeHead_outsideCut
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m)
    (cut : Set (Sym2 V))
    (hpath : SupportedInCut d.graph m cut (path m hm))
    (hhead : FluxEventOutsideCut d.graph m cut
      ((activeSegmentRunSpec d s hs).Event d.graph)) :
    stepToggleSource R.toPartialSelector d s ss = ∅ := by
  obtain ⟨T, hright⟩ := R.exists_canonical_rightPair_of_contributes
    beta J d s ss hs path bondwise_toggle m hm
  have hheadToggle := (fluxEvent_toggle_iff d.graph m cut
    ((activeSegmentRunSpec d s hs).Event d.graph) hhead
      T (path m hm) hpath).mp hright.1
  have hsrc : RandomCurrent.sources (endsM d.graph m) T = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m T).trans
      ((activeSegmentRunSpec_event d s hs _).mp hright.1).1
  have hsrcToggle : RandomCurrent.sources (endsM d.graph m)
      (T ∆ path m hm) = {s.1, s.2.1} :=
    (FluxEdgeCopy.sources_eq d.graph m _).trans
      ((activeSegmentRunSpec_event d s hs _).mp hheadToggle).1
  rw [RandomCurrent.sources_symmDiff, hsrc] at hsrcToggle
  have hpathEmpty :
      RandomCurrent.sources (endsM d.graph m) (path m hm) = ∅ := by
    calc
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
          {s.1, s.2.1} ∆
            ({s.1, s.2.1} ∆
              RandomCurrent.sources (endsM d.graph m) (path m hm)) := by simp
      _ = {s.1, s.2.1} ∆ {s.1, s.2.1} :=
        congrArg (fun U => ({s.1, s.2.1} : Finset V) ∆ U) hsrcToggle
      _ = ∅ := symmDiff_self _
  exact (R.path_sources_of_canonical_toggle
    beta J d s ss hs path bondwise_toggle m hm).symm.trans hpathEmpty

/-- For a nonempty toggle source, the active head event is not outside any cut containing the path.
-/
lemma CompleteBondwiseSelectorSpec.not_activeHead_outsideCut_of_toggleSource_ne_empty
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm))
    (m : d.graph.edgeFinset -> Nat)
    (hm : CoordinatePairContributes R.toPartialSelector
      beta J d s ss hs m)
    (cut : Set (Sym2 V))
    (hpath : SupportedInCut d.graph m cut (path m hm))
    (hsource : stepToggleSource R.toPartialSelector d s ss ≠ ∅) :
    ¬ FluxEventOutsideCut d.graph m cut
      ((activeSegmentRunSpec d s hs).Event d.graph) := by
  intro hhead
  exact hsource (R.stepToggleSource_eq_empty_of_activeHead_outsideCut
    beta J d s ss hs path bondwise_toggle m hm cut hpath hhead)

/-- The canonical asymmetric certificate of a complete specification, from a canonical pair toggle.
-/
noncomputable def CompleteBondwiseSelectorSpec.toCanonicalAsymmetricCertificate
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs :=
  R.toAsymmetricCertificate
    (residualVacuumRunSpec d s) (activeSegmentRunSpec d s hs)
    (P.liftedResidualRunSpec d s ss) beta J d s ss hs path
    (R.path_sources_of_canonical_toggle beta J d s ss hs path bondwise_toggle)
    (by
      intro m _ T
      exact (residualVacuumRunSpec_event d s
        (profileFlux d.graph m (univ \ T))).symm)
    (by
      intro m _ T
      exact R.rightPairNormalForm
        (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
        d s ss hs m T
        (activeSegmentRunSpec_event d s hs
          (profileFlux d.graph m T)).symm
        (P.liftedResidualRunSpec_event d s ss
          (profileFlux d.graph m (univ \ T))).symm)
    bondwise_toggle

/-! ## G. Existence of canonical toggles -/

/-- A canonical pair toggle exists at every contributing flux. -/
def CompleteBondwiseSelectorSpec.CanonicalBondwiseToggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) : Prop :=
  ∀ m,
    CoordinatePairContributes R.toPartialSelector beta J d s ss hs m ->
      ∃ path : Finset (Copy d.graph m), ∀ T,
        BondwisePairEvent (P.runSpec d (s :: ss))
            (residualVacuumRunSpec d s) d.graph m T <->
          BondwisePairEvent (activeSegmentRunSpec d s hs)
            (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path)

/-- A path with componentwise toggle covariance of the canonical run specifications exists at every
contributing flux. -/
def CompleteBondwiseSelectorSpec.CanonicalComponentwiseToggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) : Prop :=
  ∀ m,
    CoordinatePairContributes R.toPartialSelector beta J d s ss hs m ->
      ∃ path : Finset (Copy d.graph m),
        BondwiseRunToggleCovariance (P.runSpec d (s :: ss))
            (activeSegmentRunSpec d s hs) d.graph m path /\
          BondwiseRunToggleCovariance (residualVacuumRunSpec d s)
            (P.liftedResidualRunSpec d s ss) d.graph m path

/-- Componentwise toggles give canonical pair toggles. -/
lemma CompleteBondwiseSelectorSpec.canonicalToggleExists_of_componentwise
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : R.CanonicalComponentwiseToggleExists beta J d s ss hs) :
    R.CanonicalBondwiseToggleExists beta J d s ss hs := by
  intro m hm
  obtain ⟨path, hhead, hresidual⟩ := h m hm
  exact ⟨path, BondwisePairEvent.toggle_iff_of_componentwise
    (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
    (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
    d.graph m path hhead hresidual⟩

/-- The canonical asymmetric certificate from the existence of canonical pair toggles. -/
noncomputable def
    CompleteBondwiseSelectorSpec.toCanonicalAsymmetricCertificate_of_toggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : R.CanonicalBondwiseToggleExists beta J d s ss hs) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs := by
  let path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss) :=
    fun m hm => Classical.choose (h m hm)
  apply R.toCanonicalAsymmetricCertificate beta J d s ss hs path
  intro m hm T
  simpa only [path] using (Classical.choose_spec (h m hm) T)

/-- The canonical asymmetric certificate from componentwise canonical toggles. -/
noncomputable def
    CompleteBondwiseSelectorSpec.toCanonicalAsymmetricCertificate_of_componentwise
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : R.CanonicalComponentwiseToggleExists beta J d s ss hs) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs :=
  R.toCanonicalAsymmetricCertificate_of_toggleExists beta J d s ss hs
    (R.canonicalToggleExists_of_componentwise beta J d s ss hs h)

/-- A canonical asymmetric certificate exists iff a canonical pair toggle exists. -/
theorem CompleteBondwiseSelectorSpec.nonempty_canonicalCertificate_iff_toggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    Nonempty (AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs) <->
      R.CanonicalBondwiseToggleExists beta J d s ss hs := by
  constructor
  · rintro ⟨C⟩ m hm
    exact ⟨C.path m hm, C.bondwise_toggle m hm⟩
  · intro h
    exact ⟨R.toCanonicalAsymmetricCertificate_of_toggleExists
      beta J d s ss hs h⟩

/-- If the active cut resummation identity fails, no canonical pair toggle exists. -/
lemma CompleteBondwiseSelectorSpec.not_toggleExists_of_clearedP2_ne
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (hne : R.toPartialSelector.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ ≠
        shb_segmentNum beta J d s *
          R.toPartialSelector.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss) :
    ¬ R.CanonicalBondwiseToggleExists beta J d s ss hs := by
  intro h
  let C := R.toCanonicalAsymmetricCertificate_of_toggleExists
    beta J d s ss hs h
  exact hne (C.actualMass_active
    (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
    (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
    R.toPartialSelector beta J d s ss hs)

/-- Coordinate toggle data from an asymmetric certificate for a complete specification. -/
noncomputable def CompleteBondwiseSelectorSpec.toCoordinateToggleData_of_asymmetric
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (vacuum right₁ right₂ : BondwiseRunSpec V)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (C : AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) vacuum right₁ right₂
      R.toPartialSelector beta J d s ss hs) :
    CoordinateToggleData R.toPartialSelector beta J d s ss hs :=
  C.toCoordinateToggleData

end BackboneConcreteSelector

end

end StatMech.Sharpness
