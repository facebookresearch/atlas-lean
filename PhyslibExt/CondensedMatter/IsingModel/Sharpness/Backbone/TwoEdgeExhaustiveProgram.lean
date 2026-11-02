/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCycleObstruction

/-!
# The exhaustive two-edge bondwise program

A variant of the two-edge program whose two-edge runs additionally require that no further edge
carries odd multiplicity. It has the same selector structure and the same toggle on two-unit
fluxes, and it excludes the current `01 + 12 + triangle` of the path-plus-triangle domain.

## i. Overview

`BackboneTwoEdgeExhaustiveProgram.program` uses the scan and encoding of the two-edge program, with
the terminal condition strengthened by `NoFurtherOdd` for two accepted edges: every other edge of
the domain graph has even multiplicity. Completion is still functional, so the program defines a
complete selector specification, and on two-unit fluxes the copy toggle of the second edge is again
a componentwise covariance (`twoUnit_componentwise_covariance`, `twoUnit_pair_toggle`). On the
domain of `TwoEdgeCycleObstruction`, the current `oddTrianglePairFlux` (one unit on each path edge
and on each triangle edge) has odd triangle edges, so it does not complete the exhaustive program
(`not_selectorSpec_fiber_oddTrianglePair`).

Headline fidelity: all results are proved unconditionally; the toggle results are stated under the
explicit geometric hypotheses on `e`, `f` (`hne`, `hfirst`, `hactiveE`, `hactiveF`, `hpath`).
They concern two-unit fluxes and do not give the chain rule (P2) for the program in general.

## ii. Key results

- `BackboneTwoEdgeExhaustiveProgram.program` : the exhaustive two-edge program
- `BackboneTwoEdgeExhaustiveProgram.selectorSpec` : its complete selector specification
- `BackboneTwoEdgeExhaustiveProgram.twoUnit_pair_toggle` : the pair-event toggle on two-unit
  fluxes (unconditional, under the geometric hypotheses)
- `BackboneTwoEdgeExhaustiveProgram.Cycle.not_selectorSpec_fiber_oddTrianglePair` : the
  path-plus-odd-triangle current is not selected

## iii. Table of contents

- A. The program
- B. Complete runs and the selector specification
- C. Two-unit fluxes
- D. Covariance and the pair toggle
- E. The odd triangle is excluded

## iv. References

None beyond those in the imported modules.
-/
@[expose] public section

open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeExhaustiveProgram

open BackboneConcreteBondProgram
open BackboneConcreteSelector
open BackboneDeterminedCutSwitching
open BackboneLabeledSwitching
open BackboneP2CoordinateReindex
open FluxEdgeCopy

/-- Adjacency is decided classically in this file. -/
noncomputable local instance exhaustiveDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

/-! ## A. The program -/

/-- Every edge of the domain graph other than `e` and `f` has bit `false` in `ω`. -/
def NoFurtherOdd (st : BackboneTwoEdgeBondProgram.State V) (e f : Sym2 V)
    (omega : Sym2 V -> Bool) : Prop :=
  forall g, g ∈ st.domain.graph.edgeFinset -> g ≠ e -> g ≠ f ->
    omega g = false

/-- The terminal condition of the two-edge program, with `NoFurtherOdd` added for two accepted
edges. -/
def terminal (st : BackboneTwoEdgeBondProgram.State V)
    (omega : Sym2 V -> Bool) : Prop :=
  BackboneTwoEdgeBondProgram.terminal st omega /\
    match st.accepted with
    | [e, f] => NoFurtherOdd st e f omega
    | _ => True

/-- The exhaustive two-edge bondwise segment program. -/
noncomputable def program : BondwiseSegmentProgram V where
  State := BackboneTwoEdgeBondProgram.State V
  scan := BackboneTwoEdgeBondProgram.scan
  initial := fun d => ⟨d, []⟩
  encode := BackboneTwoEdgeBondProgram.encode
  bit := oddBit
  terminal := terminal

/-! ## B. Complete runs and the selector specification -/
lemma complete_implies_base
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat)
    (h : program.CompleteEvent d word m) :
    BackboneTwoEdgeBondProgram.program.CompleteEvent d word m := by
  unfold BondwiseSegmentProgram.CompleteEvent at h ⊢
  constructor
  · simpa [program, BackboneTwoEdgeBondProgram.program] using h.1
  · exact h.2.1

lemma program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  constructor
  · exact fun h => (BackboneTwoEdgeBondProgram.program_complete_nil_iff d m).mp
      (complete_implies_base d [] m h)
  · intro hsource
    have hbase :=
      (BackboneTwoEdgeBondProgram.program_complete_nil_iff d m).mpr hsource
    unfold BondwiseSegmentProgram.CompleteEvent
      BondwiseSegmentProgram.TerminalEvent at hbase ⊢
    constructor
    · simpa [program, BackboneTwoEdgeBondProgram.program] using hbase.1
    · exact ⟨hbase.2, trivial⟩

lemma program_complete_singleton_iff_base
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [s] m <->
      BackboneTwoEdgeBondProgram.program.CompleteEvent d [s] m := by
  constructor
  · exact complete_implies_base d [s] m
  · intro hbase
    unfold BondwiseSegmentProgram.CompleteEvent
      BondwiseSegmentProgram.TerminalEvent at hbase ⊢
    constructor
    · simpa [program, BackboneTwoEdgeBondProgram.program] using hbase.1
    · cases hedge : edgeOfSegment? d s <;>
        simpa [program, BackboneTwoEdgeBondProgram.program,
          BackboneTwoEdgeBondProgram.encode, hedge,
          BackboneTwoEdgeBondProgram.scan, terminal] using
          And.intro hbase.2 trivial

lemma program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) : word = word' :=
  BackboneTwoEdgeBondProgram.program_complete_functional d m word word'
    (complete_implies_base d word m hword)
    (complete_implies_base d word' m hword')

lemma sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) =
      BackboneTwoEdgeBondProgram.sourceClass d word :=
  BackboneTwoEdgeBondProgram.sources_eq_sourceClass_of_program_complete
    d m word (complete_implies_base d word m h)

lemma head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) : s ∈ d.active :=
  BackboneTwoEdgeBondProgram.head_active_of_program_complete d m s ss
    (complete_implies_base d (s :: ss) m h)

/-- The complete bondwise selector specification defined by the exhaustive program. -/
noncomputable def selectorSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) where
  sourceClass := BackboneTwoEdgeBondProgram.sourceClass (V := V)
  sourceClass_nil := BackboneTwoEdgeBondProgram.sourceClass_nil
  complete_functional := program_complete_functional
  sources_eq_sourceClass_of_complete :=
    sources_eq_sourceClass_of_program_complete
  complete_nil_iff := program_complete_nil_iff
  head_active_of_complete := head_active_of_program_complete

/-! ## C. Two-unit fluxes -/
lemma noFurtherOdd_twoUnit
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) :
    NoFurtherOdd ⟨d, [e.1, f.1]⟩ e.1 f.1
      (fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)) := by
  intro g hg hge hgf
  have hsube : (⟨g, hg⟩ : d.graph.edgeFinset) ≠ e := by
    intro h
    exact hge (congrArg Subtype.val h)
  have hsubf : (⟨g, hg⟩ : d.graph.edgeFinset) ≠ f := by
    intro h
    exact hgf (congrArg Subtype.val h)
  simp [fluxBitConfig, hg, oddBit,
    BackboneTwoEdgeBondProgram.twoUnitFlux, unitFlux, hsube, hsubf]

lemma program_complete_canonical_pair_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) := by
  have hbase :=
    BackboneTwoEdgeBondProgram.program_complete_canonical_pair_twoUnitFlux
      d e f hne hfirst hactiveE hactiveF hpath
  have hbaseTerminal := hbase.2
  unfold BondwiseSegmentProgram.CompleteEvent at hbase ⊢
  constructor
  · simpa [program, BackboneTwoEdgeBondProgram.program] using hbase.1
  · unfold BondwiseSegmentProgram.TerminalEvent at hbaseTerminal ⊢
    have hstate :
        program.scan.residual (program.initial d)
            (program.encode d
              [canonicalEdgeSegment d.graph e,
                canonicalEdgeSegment d.graph f]) =
          (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) := by
      simp [program, BackboneTwoEdgeBondProgram.encode,
        edgeOfSegment?_canonicalEdgeSegment,
        BackboneTwoEdgeBondProgram.scan]
    have hbaseState :
        BackboneTwoEdgeBondProgram.program.scan.residual
            (BackboneTwoEdgeBondProgram.program.initial d)
            (BackboneTwoEdgeBondProgram.program.encode d
              [canonicalEdgeSegment d.graph e,
                canonicalEdgeSegment d.graph f]) =
          (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) := by
      simp [BackboneTwoEdgeBondProgram.program,
        BackboneTwoEdgeBondProgram.encode,
        edgeOfSegment?_canonicalEdgeSegment,
        BackboneTwoEdgeBondProgram.scan]
    rw [hstate]
    rw [hbaseState] at hbaseTerminal
    exact ⟨hbaseTerminal, noFurtherOdd_twoUnit d e f⟩

lemma selectorSpec_fiber_canonical_pair_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    (selectorSpec (V := V)).toPartialSelector.Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
    hactiveE hactiveF hpath

lemma noFurtherOdd_of_complete_canonical_pair
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (m : d.graph.edgeFinset -> Nat)
    (h : program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] m) :
    NoFurtherOdd
      (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) e.1 f.1
      (fluxBitConfig d.graph oddBit m) := by
  have hterminal := h.2
  unfold BondwiseSegmentProgram.TerminalEvent at hterminal
  have hstate :
      program.scan.residual (program.initial d)
          (program.encode d
            [canonicalEdgeSegment d.graph e,
              canonicalEdgeSegment d.graph f]) =
        (⟨d, [e.1, f.1]⟩ : BackboneTwoEdgeBondProgram.State V) := by
    simp [program, BackboneTwoEdgeBondProgram.encode,
      edgeOfSegment?_canonicalEdgeSegment,
      BackboneTwoEdgeBondProgram.scan]
  rw [hstate] at hterminal
  simpa [program, terminal] using hterminal.2

/-! ## D. Covariance and the pair toggle -/
lemma runSpec_singleton_event_iff_base
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    ((program (V := V)).runSpec d [s]).Event d.graph m <->
      ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [s]).Event
        d.graph m := by
  rw [(program (V := V)).runSpec_event,
    (BackboneTwoEdgeBondProgram.program (V := V)).runSpec_event]
  exact program_complete_singleton_iff_base d s m

lemma liftedResidualRunSpec_singleton_event_iff_base
    (d : shb_ExplorationDomain V) (s t : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    ((program (V := V)).liftedResidualRunSpec d s [t]).Event d.graph m <->
      ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec
        d s [t]).Event d.graph m := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event,
    BondwiseSegmentProgram.liftedResidualRunSpec_event]
  unfold BondwiseSegmentProgram.LiftedRunEvent LiftedPredicate
  constructor
  · rintro ⟨r, hr, hrun⟩
    exact ⟨r, hr, (runSpec_singleton_event_iff_base
      (shb_BackboneExplorationDomain.advance d s) t r).mp hrun⟩
  · rintro ⟨r, hr, hrun⟩
    exact ⟨r, hr, (runSpec_singleton_event_iff_base
      (shb_BackboneExplorationDomain.advance d s) t r).mpr hrun⟩

lemma fullRun_activeHead_twoUnit_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    BondwiseRunToggleCovariance
      ((program (V := V)).runSpec d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
      (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
      d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
      {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
  rw [BackboneTwoEdgeBondToggle.bondwiseRunToggleCovariance_twoUnit_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      have hc := ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (0 : d.graph.edgeFinset -> Nat)).mp h
      exact (BackboneTwoEdgeBondToggle.program_pair_zero_false d e f hpath
        (complete_implies_base d _ _ hc)).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (unitFlux d.graph f)).mp h
      exact (BackboneTwoEdgeBondToggle.activeSegmentFiber_second_unitFlux_false
        d e f hactiveE hpath ha).elim
  · constructor
    · intro h
      have hc := ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (unitFlux d.graph e)).mp h
      exact (BackboneTwoEdgeBondToggle.program_pair_unitFlux_first_false
        d e f hpath (complete_implies_base d _ _ hc)).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)).mp h
      exact (BackboneTwoEdgeBondToggle.activeSegmentFiber_twoUnitFlux_false
        d e f hactiveE hpath ha).elim
  · constructor
    · intro h
      have hc := ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (unitFlux d.graph f)).mp h
      exact (BackboneTwoEdgeBondToggle.program_pair_unitFlux_second_false
        d e f hpath (complete_implies_base d _ _ hc)).elim
    · intro h
      have ha := (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (0 : d.graph.edgeFinset -> Nat)).mp h
      exact (BackboneTwoEdgeBondToggle.activeSegmentFiber_zero_false
        d e hactiveE ha).elim
  · constructor
    · intro _
      exact (activeSegmentRunSpec_event d
        (canonicalEdgeSegment d.graph e) hactiveE
        (unitFlux d.graph e)).mpr
        (BackboneTwoEdgeBondToggle.activeSegmentFiber_unitFlux
          d e hactiveE)
    · intro _
      exact ((program (V := V)).runSpec_event d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)).mpr
        (program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
          hactiveE hactiveF hpath)

lemma residualVacuum_suffix_twoUnit_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
    BondwiseRunToggleCovariance
      (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
      ((program (V := V)).liftedResidualRunSpec d
        (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
      d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
      {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} := by
  intro T
  have hbase :=
    BackboneTwoEdgeBondToggle.residualVacuum_suffix_twoUnit_covariance
      d e f hne hactiveF T
  constructor
  · intro hvacuum
    apply (liftedResidualRunSpec_singleton_event_iff_base d
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)
      (profileFlux d.graph
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}))).mpr
    exact hbase.mp hvacuum
  · intro hsuffix
    apply hbase.mpr
    exact (liftedResidualRunSpec_singleton_event_iff_base d
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)
      (profileFlux d.graph
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}))).mp
      hsuffix

/-- On a two-unit flux, toggling the copy of the second edge is a componentwise covariance for the
exhaustive program. -/
theorem twoUnit_componentwise_covariance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
    BondwiseRunToggleCovariance
        ((program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} /\
      BondwiseRunToggleCovariance
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        ((program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne} :=
  ⟨fullRun_activeHead_twoUnit_covariance d e f hne hfirst hactiveE
      hactiveF hpath,
    residualVacuum_suffix_twoUnit_covariance d e f hne hactiveF⟩

/-- The pair-event toggle on two-unit fluxes for the exhaustive program. -/
theorem twoUnit_pair_toggle
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit
        (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : BackboneTwoEdgeBondProgram.FormsTwoEdgePath
      (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f))
    (T : Finset (Copy d.graph
      (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f))) :
    BondwisePairEvent
        ((program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f) T <->
      BondwisePairEvent
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
        ((program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
        d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
        (T ∆ {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}) := by
  obtain ⟨hfull, hresidual⟩ := twoUnit_componentwise_covariance d e f hne
    hfirst hactiveE hactiveF hpath
  exact BondwisePairEvent.toggle_iff_of_componentwise
    ((program (V := V)).runSpec d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
    (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
    (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
    ((program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
    d.graph (BackboneTwoEdgeBondProgram.twoUnitFlux d.graph e f)
    {BackboneTwoEdgeBondToggle.secondCopy d.graph e f hne}
    hfull hresidual T

namespace Cycle

open BackboneTwoEdgeCycleObstruction

/-! ## E. The odd triangle is excluded -/

/-- The current with one unit on each path edge and on each triangle edge. -/
def oddTrianglePairFlux : domain.graph.edgeFinset -> Nat := fun g =>
  BackboneTwoEdgeBondProgram.twoUnitFlux domain.graph headEdge suffixEdge g +
    oddCycleFlux g

@[simp] lemma oddTrianglePairFlux_cycle₀ :
    oddTrianglePairFlux cycleEdge₀ = 1 := by
  unfold oddTrianglePairFlux BackboneTwoEdgeBondProgram.twoUnitFlux unitFlux
  rw [oddCycleFlux_cycle₀]
  change ((if cycleEdge₀ = headEdge then 1 else 0) +
    (if cycleEdge₀ = suffixEdge then 1 else 0)) + 1 = 1
  rw [ite_eq_right cycleEdge₀_ne_headEdge, ite_eq_right cycleEdge₀_ne_suffixEdge]

@[simp] lemma oddTrianglePairBit_cycle₀ :
    fluxBitConfig domain.graph oddBit oddTrianglePairFlux cycleEdge₀.1 =
      true := by
  unfold fluxBitConfig
  rw [dite_eq_left (show cycleEdge₀.1 ∈ domain.graph.edgeFinset from cycleEdge₀.2)]
  simp only [Subtype.coe_eta, oddTrianglePairFlux_cycle₀]
  decide

lemma not_noFurtherOdd_oddTrianglePair :
    ¬NoFurtherOdd
      (⟨domain, [headEdge.1, suffixEdge.1]⟩ :
        BackboneTwoEdgeBondProgram.State (Fin 6))
      headEdge.1 suffixEdge.1
      (fluxBitConfig domain.graph oddBit oddTrianglePairFlux) := by
  intro h
  have hfalse := h cycleEdge₀.1 cycleEdge₀.2
    (fun heq => cycleEdge₀_ne_headEdge (Subtype.ext heq))
    (fun heq => cycleEdge₀_ne_suffixEdge (Subtype.ext heq))
  rw [oddTrianglePairBit_cycle₀] at hfalse
  simp at hfalse

lemma not_program_complete_oddTrianglePair :
    ¬program.CompleteEvent domain
      [canonicalEdgeSegment domain.graph headEdge,
        canonicalEdgeSegment domain.graph suffixEdge]
      oddTrianglePairFlux := by
  intro hcomplete
  apply not_noFurtherOdd_oddTrianglePair
  exact noFurtherOdd_of_complete_canonical_pair domain headEdge suffixEdge
    oddTrianglePairFlux hcomplete

/-- The current `01 + 12 + triangle` on the path-plus-triangle domain is not in the two-segment
fiber of the exhaustive selector. -/
theorem not_selectorSpec_fiber_oddTrianglePair :
    ¬(selectorSpec (V := Fin 6)).toPartialSelector.Fiber domain
      [canonicalEdgeSegment domain.graph headEdge,
        canonicalEdgeSegment domain.graph suffixEdge]
      oddTrianglePairFlux := by
  rw [(selectorSpec (V := Fin 6)).fiber_iff_completeEvent]
  exact not_program_complete_oddTrianglePair

end Cycle

end BackboneTwoEdgeExhaustiveProgram

end

end StatMech.Sharpness
