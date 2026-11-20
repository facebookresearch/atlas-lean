/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Sharpness.BackboneConcreteBondProgram

open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneMultiStepBondProgram

open BackboneConcreteSelector
open BackboneConcreteBondProgram
open BackboneDeterminedCutSwitching

noncomputable local instance multiStepDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _


def segmentEnds (s : shb_ExplorationSegment V) : Finset V :=
  {s.1, s.2.1}



def pairSourceClass (s t : shb_ExplorationSegment V) : Finset V :=
  segmentEnds s ∆ segmentEnds t


def sourceClass (_d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> Finset V
  | [] => ∅
  | [s, t] => pairSourceClass s t
  | _ => ∅

@[simp] theorem sourceClass_nil (d : shb_ExplorationDomain V) :
    sourceClass d [] = ∅ := rfl

@[simp] theorem sourceClass_pair
    (d : shb_ExplorationDomain V) (s t : shb_ExplorationSegment V) :
    sourceClass d [s, t] = pairSourceClass s t := rfl



structure State (V : Type*) [Fintype V] [DecidableEq V] where
  domain : shb_ExplorationDomain V
  accepted : List (Sym2 V)




noncomputable def scan :
    shb_DynamicEdgeExploration (State V) (Sym2 V) where
  edgeOrder := fun st =>
    match st.accepted with
    | [] => st.domain.graph.edgeFinset.1.toList.take 1
    | [e] => (st.domain.graph.edgeFinset.1.toList.erase e).take 1
    | _ => []
  edgeOrder_nodup := by
    intro st
    rcases st with ⟨d, accepted⟩
    cases accepted with
    | nil => exact (Finset.nodup_toList d.graph.edgeFinset).take
    | cons e rest =>
        cases rest with
        | nil =>
            exact ((Finset.nodup_toList d.graph.edgeFinset).erase e).take
        | cons f rest => simp
  advance := fun st e =>
    match st.accepted with
    | [] => ⟨st.domain, [e]⟩
    | [first] => ⟨st.domain, [first, e]⟩
    | _ => st



def IsDesignatedPair (d : shb_ExplorationDomain V)
    (e f : d.graph.edgeFinset) : Prop :=
  ∃ tail, d.graph.edgeFinset.1.toList = e.1 :: f.1 :: tail

theorem IsDesignatedPair.ne
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (h : IsDesignatedPair d e f) : e.1 ≠ f.1 := by
  rcases h with ⟨tail, horder⟩
  have hnodup := Finset.nodup_toList d.graph.edgeFinset
  change d.graph.edgeFinset.1.toList.Nodup at hnodup
  rw [horder] at hnodup
  intro hef
  exact (List.nodup_cons.mp hnodup).1 (by simp [hef])

theorem scan_edgeOrder_initial_of_designated
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (h : IsDesignatedPair d e f) :
    scan.edgeOrder ⟨d, []⟩ = [e.1] := by
  rcases h with ⟨tail, horder⟩
  simp [scan, horder]

theorem scan_edgeOrder_second_of_designated
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (h : IsDesignatedPair d e f) :
    scan.edgeOrder (scan.advance ⟨d, []⟩ e.1) = [f.1] := by
  rcases h with ⟨tail, horder⟩
  simp [scan, horder]




noncomputable def encode
    (d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  | [] => []
  | [s, t] =>
      match edgeOfSegment? d s, edgeOfSegment? d t with
      | some e, some f =>
          if e.1 = f.1 then [s(s.1, s.1)] else [e.1, f.1]
      | _, _ => [s(s.1, s.1)]
  | s :: _ => [s(s.1, s.1)]


def boolSources (st : State V) (omega : Sym2 V -> Bool) : Finset V :=
  sources st.domain.graph (boolCurrent omega)



def terminal (st : State V) (omega : Sym2 V -> Bool) : Prop :=
  match st.accepted with
  | [] => boolSources st omega = ∅
  | [e, f] =>
      if he : e ∈ st.domain.graph.edgeFinset then
        if hf : f ∈ st.domain.graph.edgeFinset then
          let se := canonicalEdgeSegment st.domain.graph ⟨e, he⟩
          let sf := canonicalEdgeSegment st.domain.graph ⟨f, hf⟩
          e ≠ f ∧ se ∈ st.domain.active ∧ sf ∈ st.domain.active ∧
            boolSources st omega = pairSourceClass se sf ∧
            boolSources st omega ≠ ∅
        else False
      else False
  | _ => False


noncomputable def program : BondwiseSegmentProgram V where
  State := State V
  scan := scan
  initial := fun d => ⟨d, []⟩
  encode := encode
  bit := oddBit
  terminal := terminal


def twoUnitFlux (G : SimpleGraph V) (e f : G.edgeFinset) :
    G.edgeFinset -> Nat := fun g => unitFlux G e g + unitFlux G f g

theorem sources_twoUnitFlux (G : SimpleGraph V) (e f : G.edgeFinset) :
    sources G (ofEdgeFun G (twoUnitFlux G e f)) =
      pairSourceClass (canonicalEdgeSegment G e)
        (canonicalEdgeSegment G f) := by
  change sources G
      (ofEdgeFun G (fun g => unitFlux G e g + unitFlux G f g)) = _
  rw [← ofEdgeFun_add, sources_add, sources_unitFlux, sources_unitFlux]
  rfl

theorem segmentEnds_canonicalEdgeSegment
    (G : SimpleGraph V) (e : G.edgeFinset) :
    segmentEnds (canonicalEdgeSegment G e) = e.1.toFinset := by
  change {e.1.out.1, e.1.out.2} = e.1.toFinset
  rw [← Sym2.toFinset_mk_eq]
  exact congrArg Sym2.toFinset e.1.out_eq

theorem pairSourceClass_canonicalEdgeSegment_ne_empty
    (G : SimpleGraph V) (e f : G.edgeFinset) (hne : e.1 ≠ f.1) :
    pairSourceClass (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f) ≠ ∅ := by
  intro hempty
  rw [pairSourceClass, segmentEnds_canonicalEdgeSegment,
    segmentEnds_canonicalEdgeSegment] at hempty
  have hfin : e.1.toFinset = f.1.toFinset :=
    Finset.symmDiff_eq_empty.mp hempty
  apply hne
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hfin]



theorem scan_selects_twoUnitFlux
    {d : shb_ExplorationDomain V} {e f : d.graph.edgeFinset}
    (hpair : IsDesignatedPair d e f) :
    scan.Selects
      (fun _ g => fluxBitConfig d.graph oddBit
        (twoUnitFlux d.graph e f) g)
      ⟨d, []⟩ [e.1, f.1] := by
  have hef : e ≠ f := fun h => hpair.ne (congrArg Subtype.val h)
  have hfe : f ≠ e := Ne.symm hef
  have heedge : e.1 ∈ d.graph.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
  have hfedge : f.1 ∈ d.graph.edgeSet := SimpleGraph.mem_edgeFinset.mp f.2
  constructor
  · unfold shb_DynamicEdgeExploration.firstAdmissible
    rw [scan_edgeOrder_initial_of_designated hpair]
    simp [fluxBitConfig, heedge, oddBit, twoUnitFlux, unitFlux, hef]
  · constructor
    · unfold shb_DynamicEdgeExploration.firstAdmissible
      rw [scan_edgeOrder_second_of_designated hpair]
      simp [fluxBitConfig, hfedge, oddBit, twoUnitFlux, unitFlux, hfe]
    · trivial

@[simp] theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  change (True ∧ sources d.graph
    (boolCurrent (fluxBitConfig d.graph oddBit m)) = ∅) <-> _
  rw [sources_boolCurrent_oddBit]
  simp


theorem scan_firstAdmissible_ne_diagonal_initial
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool) (x : V) :
    scan.firstAdmissible (fun _ e => omega e) ⟨d, []⟩ ≠ some s(x, x) := by
  intro h
  have hmem := scan.firstAdmissible_mem (fun _ e => omega e)
    ⟨d, []⟩ s(x, x) h
  have hlist : s(x, x) ∈ d.graph.edgeFinset.1.toList :=
    List.mem_of_mem_take hmem
  have hedge : s(x, x) ∈ d.graph.edgeFinset := by
    simpa using hlist
  have hadj : d.graph.Adj x x := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact d.graph.loopless.irrefl x hadj

@[simp] theorem encode_pair_of_edges
    (d : shb_ExplorationDomain V) (s t : shb_ExplorationSegment V)
    (e f : d.graph.edgeFinset)
    (hs : edgeOfSegment? d s = some e)
    (ht : edgeOfSegment? d t = some f)
    (hne : e.1 ≠ f.1) :
    encode d [s, t] = [e.1, f.1] := by
  simp [encode, hs, ht, hne]



theorem program_complete_word_eq_nil_or_pair
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    word = [] ∨ ∃ s t, word = [s, t] := by
  cases word with
  | nil => exact Or.inl rfl
  | cons s rest =>
      cases rest with
      | nil =>
          have hfirst : scan.firstAdmissible
              (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
              some s(s.1, s.1) := by
            simpa [program, encode, BondwiseSuffixEvent] using h.1
          exact (scan_firstAdmissible_ne_diagonal_initial d
            (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
      | cons t tail =>
          cases tail with
          | nil => exact Or.inr ⟨s, t, rfl⟩
          | cons u us =>
              have hfirst : scan.firstAdmissible
                  (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
                  some s(s.1, s.1) := by
                simpa [program, encode, BondwiseSuffixEvent] using h.1
              exact (scan_firstAdmissible_ne_diagonal_initial d
                (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim



theorem edgeOfSegment?_pair_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s, t] m) :
    ∃ e f : d.graph.edgeFinset,
      edgeOfSegment? d s = some e ∧ edgeOfSegment? d t = some f ∧
        e.1 ≠ f.1 := by
  cases hs : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
          some s(s.1, s.1) := by
        simpa [program, encode, hs, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal_initial d
        (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
  | some e =>
      cases ht : edgeOfSegment? d t with
      | none =>
          have hfirst : scan.firstAdmissible
              (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
              some s(s.1, s.1) := by
            simpa [program, encode, hs, ht, BondwiseSuffixEvent] using h.1
          exact (scan_firstAdmissible_ne_diagonal_initial d
            (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
      | some f =>
          by_cases hne : e.1 = f.1
          · have hfirst : scan.firstAdmissible
                (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, []⟩ =
                some s(s.1, s.1) := by
              simpa [program, encode, hs, ht, hne,
                BondwiseSuffixEvent] using h.1
            exact (scan_firstAdmissible_ne_diagonal_initial d
              (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
          · exact ⟨e, f, rfl, rfl, hne⟩



theorem program_complete_pair_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s, t] m) :
    ∃ e f : d.graph.edgeFinset,
      e.1 ≠ f.1 ∧
      scan.firstAdmissible
          (fun _ g => fluxBitConfig d.graph oddBit m g) ⟨d, []⟩ =
        some e.1 ∧
      scan.firstAdmissible
          (fun _ g => fluxBitConfig d.graph oddBit m g)
          (scan.advance ⟨d, []⟩ e.1) = some f.1 ∧
      canonicalEdgeSegment d.graph e = s ∧
      canonicalEdgeSegment d.graph f = t ∧
      canonicalEdgeSegment d.graph e ∈ d.active ∧
      canonicalEdgeSegment d.graph f ∈ d.active ∧
      sources d.graph (ofEdgeFun d.graph m) =
        pairSourceClass (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) ∧
      sources d.graph (ofEdgeFun d.graph m) ≠ ∅ := by
  obtain ⟨e, f, hs, ht, hne⟩ :=
    edgeOfSegment?_pair_of_program_complete d m s t h
  have hselect : scan.Selects
      (fun _ g => fluxBitConfig d.graph oddBit m g)
      ⟨d, []⟩ [e.1, f.1] := by
    simpa [program, encode_pair_of_edges d s t e f hs ht hne,
      BondwiseSuffixEvent] using h.1
  have hterminal :
      e.1 ≠ f.1 ∧
      canonicalEdgeSegment d.graph e ∈ d.active ∧
      canonicalEdgeSegment d.graph f ∈ d.active ∧
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) =
        pairSourceClass (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) ∧
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) ≠ ∅ := by
    simpa [BondwiseSegmentProgram.TerminalEvent, program,
      encode_pair_of_edges d s t e f hs ht hne,
      scan, terminal, boolSources, e.2, f.2, hne] using h.2
  have hsources : sources d.graph (ofEdgeFun d.graph m) =
      pairSourceClass (canonicalEdgeSegment d.graph e)
        (canonicalEdgeSegment d.graph f) := by
    rw [← sources_boolCurrent_oddBit d.graph m]
    exact hterminal.2.2.2.1
  have hnonempty : sources d.graph (ofEdgeFun d.graph m) ≠ ∅ := by
    rw [← sources_boolCurrent_oddBit d.graph m]
    exact hterminal.2.2.2.2
  exact ⟨e, f, hne, hselect.1, hselect.2.1,
    edgeOfSegment?_eq_some_spec d s e hs,
    edgeOfSegment?_eq_some_spec d t f ht,
    hterminal.2.1, hterminal.2.2.1, hsources, hnonempty⟩


theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) :
    word = word' := by
  rcases program_complete_word_eq_nil_or_pair d m word hword with
    rfl | ⟨s, t, rfl⟩
  · rcases program_complete_word_eq_nil_or_pair d m word' hword' with
      rfl | ⟨u, v, rfl⟩
    · rfl
    · have hzero := (program_complete_nil_iff d m).mp hword
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hnonempty⟩ :=
        program_complete_pair_data d m u v hword'
      exact (hnonempty hzero).elim
  · rcases program_complete_word_eq_nil_or_pair d m word' hword' with
      rfl | ⟨u, v, rfl⟩
    · have hzero := (program_complete_nil_iff d m).mp hword'
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hnonempty⟩ :=
        program_complete_pair_data d m s t hword
      exact (hnonempty hzero).elim
    · obtain ⟨e, f, _, hefirst, hfsecond, hse, htf, _, _, _, _⟩ :=
        program_complete_pair_data d m s t hword
      obtain ⟨e', f', _, hefirst', hfsecond', hue', hvf', _, _, _, _⟩ :=
        program_complete_pair_data d m u v hword'
      have heval : e.1 = e'.1 :=
        Option.some.inj (hefirst.symm.trans hefirst')
      have he : e = e' := Subtype.ext heval
      subst e'
      have hfval : f.1 = f'.1 :=
        Option.some.inj (hfsecond.symm.trans hfsecond')
      have hf : f = f' := Subtype.ext hfval
      subst f'
      have hsu : s = u := hse.symm.trans hue'
      have htv : t = v := htf.symm.trans hvf'
      simp [hsu, htv]


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
  rcases program_complete_word_eq_nil_or_pair d m word h with
    rfl | ⟨s, t, rfl⟩
  · exact (program_complete_nil_iff d m).mp h
  · obtain ⟨_, _, _, _, _, hse, htf, _, _, hsources, _⟩ :=
      program_complete_pair_data d m s t h
    simpa [sourceClass, hse, htf] using hsources


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) :
    s ∈ d.active := by
  rcases program_complete_word_eq_nil_or_pair d m (s :: ss) h with
    hnil | ⟨u, v, hpair⟩
  · simp at hnil
  · have hcomplete : program.CompleteEvent d [u, v] m := by
      rw [← hpair]
      exact h
    obtain ⟨_, _, _, _, _, heu, _, heactive, _, _, _⟩ :=
      program_complete_pair_data d m u v hcomplete
    have hsu : s = u := by
      have hheads := congrArg List.head? hpair
      exact Option.some.inj (by simpa using hheads)
    rw [hsu, ← heu]
    exact heactive


noncomputable def selectorSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) where
  sourceClass := sourceClass (V := V)
  sourceClass_nil := sourceClass_nil
  complete_functional := program_complete_functional
  sources_eq_sourceClass_of_complete :=
    sources_eq_sourceClass_of_program_complete
  complete_nil_iff := program_complete_nil_iff
  head_active_of_complete := head_active_of_program_complete



noncomputable def selectorRealization :
    SelectorRealization (program (V := V))
      (selectorSpec (V := V)).toPartialSelector where
  complete_iff_fiber := by
    intro d word m
    exact ((selectorSpec (V := V)).fiber_iff_completeEvent d word m).symm



theorem program_realizes_selectorSpec :
    ProgramRealizes (program (V := V))
      (selectorSpec (V := V)).toPartialSelector :=
  selectorRealization.programRealizes



theorem program_complete_pair_of_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V) (e f : d.graph.edgeFinset)
    (hs : edgeOfSegment? d s = some e)
    (ht : edgeOfSegment? d t = some f)
    (hne : e.1 ≠ f.1)
    (hselect : scan.Selects
      (fun _ g => fluxBitConfig d.graph oddBit m g)
      ⟨d, []⟩ [e.1, f.1])
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active)
    (hsources : sources d.graph (ofEdgeFun d.graph m) =
      pairSourceClass (canonicalEdgeSegment d.graph e)
        (canonicalEdgeSegment d.graph f))
    (hnonempty : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) :
    program.CompleteEvent d [s, t] m := by
  have hboolSources :
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) =
        pairSourceClass (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) := by
    rw [sources_boolCurrent_oddBit]
    exact hsources
  have hboolNonempty :
      sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) ≠ ∅ := by
    rw [sources_boolCurrent_oddBit]
    exact hnonempty
  constructor
  · simpa [program, encode_pair_of_edges d s t e f hs ht hne,
      BondwiseSuffixEvent] using hselect
  · simpa [BondwiseSegmentProgram.TerminalEvent, program,
      encode_pair_of_edges d s t e f hs ht hne,
      scan, terminal, boolSources, e.2, f.2, hne] using
        ⟨heactive, hfactive, hboolSources, hboolNonempty⟩



theorem program_complete_designated_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  exact program_complete_pair_of_data d (twoUnitFlux d.graph e f)
    (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) e f
    (edgeOfSegment?_canonicalEdgeSegment d e)
    (edgeOfSegment?_canonicalEdgeSegment d f)
    hpair.ne (scan_selects_twoUnitFlux hpair) heactive hfactive
    (sources_twoUnitFlux d.graph e f)
    (by
      rw [sources_twoUnitFlux]
      exact pairSourceClass_canonicalEdgeSegment_ne_empty
        d.graph e f hpair.ne)



theorem selectorSpec_fiber_designated_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_designated_twoUnitFlux d e f hpair
    heactive hfactive



theorem selectorSpec_fiber_designated_twoEdgePath
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : (canonicalEdgeSegment d.graph e).2.1 =
      (canonicalEdgeSegment d.graph f).1) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
        (twoUnitFlux d.graph e f) ∧
      (canonicalEdgeSegment d.graph e).2.1 =
        (canonicalEdgeSegment d.graph f).1 :=
  ⟨selectorSpec_fiber_designated_twoUnitFlux d e f hpair
      heactive hfactive, hpath⟩




theorem selectorRealization_designated_pair_fiber
    {S : shb_PartialCurrentDynamicSelector (V := V)}
    (R : SelectorRealization (program (V := V)) S)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    S.Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) :=
  (R.complete_iff_fiber _ _ _).mp
    (program_complete_designated_twoUnitFlux d e f hpair
      heactive hfactive)




theorem intendedOneStepRealization_isEmpty_of_designated_pair
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    IsEmpty (SelectorRealization (program (V := V))
      (shb_oneStepPartialSelector (V := V))) := by
  constructor
  intro R
  have hfiber := selectorRealization_designated_pair_fiber R d e f hpair
    heactive hfactive
  unfold shb_PartialCurrentDynamicSelector.Fiber at hfiber
  change (if sources d.graph
      (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) = ∅ then some []
    else (shb_oneStepChosenSegment d
      (twoUnitFlux d.graph e f)).map (fun s => [s])) =
      some [canonicalEdgeSegment d.graph e,
        canonicalEdgeSegment d.graph f] at hfiber
  by_cases hvac : sources d.graph
      (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) = ∅
  · simp [hvac] at hfiber
  · rw [if_neg hvac] at hfiber
    cases hchosen : shb_oneStepChosenSegment d
        (twoUnitFlux d.graph e f) <;> simp [hchosen] at hfiber

end BackboneMultiStepBondProgram

end

end StatMech.Sharpness
