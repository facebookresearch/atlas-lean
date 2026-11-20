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

namespace BackboneTwoEdgeBondProgram

open BackboneConcreteSelector
open BackboneConcreteBondProgram
open BackboneDeterminedCutSwitching

noncomputable local instance twoEdgeDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _



structure State (V : Type*) [Fintype V] [DecidableEq V] where
  domain : shb_ExplorationDomain V
  accepted : List (Sym2 V)



noncomputable def scan :
    shb_DynamicEdgeExploration (State V) (Sym2 V) where
  edgeOrder := fun st =>
    match st.accepted with
    | [] => st.domain.graph.edgeFinset.1.toList
    | [first] => (st.domain.graph.edgeFinset.erase first).1.toList
    | _ => []
  edgeOrder_nodup := by
    intro st
    cases st.accepted with
    | nil => exact Finset.nodup_toList _
    | cons first rest =>
        cases rest with
        | nil => exact Finset.nodup_toList _
        | cons second tail => simp
  advance := fun st e => ⟨st.domain, st.accepted ++ [e]⟩




noncomputable def encode
    (d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  | [] => []
  | [s] =>
      match edgeOfSegment? d s with
      | some e => [e.1]
      | none => [s(s.1, s.1)]
  | [s, t] =>
      match edgeOfSegment? d s, edgeOfSegment? d t with
      | some e, some f => [e.1, f.1]
      | _, _ => [s(s.1, s.1)]
  | s :: _ :: _ :: _ => [s(s.1, s.1)]



def FormsTwoEdgePath
    (s t : shb_ExplorationSegment V) : Prop :=
  s.2.1 = t.1 /\ s.1 ≠ t.2.1


def boolSources (st : State V) (omega : Sym2 V -> Bool) : Finset V :=
  sources st.domain.graph
    (BackboneConcreteBondProgram.boolCurrent omega)




def terminal (st : State V) (omega : Sym2 V -> Bool) : Prop :=
  match st.accepted with
  | [] => boolSources st omega = ∅
  | [e] =>
      if he : e ∈ st.domain.graph.edgeFinset then
        let s := canonicalEdgeSegment st.domain.graph ⟨e, he⟩
        s ∈ st.domain.active /\
          boolSources st omega = {s.1, s.2.1} /\
          scan.firstAdmissible (fun _ b => omega b) st = none
      else False
  | [e, f] =>
      if he : e ∈ st.domain.graph.edgeFinset then
        if hf : f ∈ st.domain.graph.edgeFinset then
          let s := canonicalEdgeSegment st.domain.graph ⟨e, he⟩
          let t := canonicalEdgeSegment st.domain.graph ⟨f, hf⟩
          e ≠ f /\ s ∈ st.domain.active /\ t ∈ st.domain.active /\
            FormsTwoEdgePath s t /\
            boolSources st omega = {s.1, s.2.1} ∆ {t.1, t.2.1}
        else False
      else False
  | _ => False


noncomputable def program : BondwiseSegmentProgram V where
  State := State V
  scan := scan
  initial := fun d => ⟨d, []⟩
  encode := encode
  bit := BackboneConcreteBondProgram.oddBit
  terminal := terminal

@[simp] theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  change (True /\ sources d.graph
    (BackboneConcreteBondProgram.boolCurrent
      (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)) = ∅) <-> _
  rw [BackboneConcreteBondProgram.sources_boolCurrent_oddBit]
  simp


theorem scan_firstAdmissible_ne_diagonal
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool) (x : V) :
    scan.firstAdmissible (fun _ e => omega e) ⟨d, []⟩ ≠ some s(x, x) := by
  intro h
  have hmem := scan.firstAdmissible_mem (fun _ e => omega e)
    ⟨d, []⟩ s(x, x) h
  have hedge : s(x, x) ∈ d.graph.edgeFinset := by
    simpa [scan] using hmem
  have hadj : d.graph.Adj x x := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact d.graph.loopless.irrefl x hadj





theorem program_complete_singleton_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some e.1 /\
      canonicalEdgeSegment d.graph e ∈ d.active /\
      sources d.graph (ofEdgeFun d.graph m) =
        {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, [e.1]⟩ = none := by
  unfold BondwiseSegmentProgram.CompleteEvent at h
  cases hedge : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
        s.1 hfirst).elim
  | some e =>
      have hfirst : scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some e.1 := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      have hsegment : canonicalEdgeSegment d.graph e = s :=
        edgeOfSegment?_eq_some_spec d s e hedge
      have hterminal :
          canonicalEdgeSegment d.graph e ∈ d.active /\
          sources d.graph
              (BackboneConcreteBondProgram.boolCurrent
                (fluxBitConfig d.graph
                  BackboneConcreteBondProgram.oddBit m)) =
            {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} /\
          scan.firstAdmissible
              (fun _ b => fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m b)
              ⟨d, [e.1]⟩ = none := by
        simpa [program, encode, hedge,
          BondwiseSegmentProgram.TerminalEvent, scan, terminal, boolSources,
          e.2] using h.2
      refine ⟨e, hsegment, hfirst, hterminal.1, ?_, hterminal.2.2⟩
      rw [← BackboneConcreteBondProgram.sources_boolCurrent_oddBit
        d.graph m]
      exact hterminal.2.1



theorem program_complete_pair_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s, t] m) :
    ∃ e f : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s /\
      canonicalEdgeSegment d.graph f = t /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some e.1 /\
      scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, [e.1]⟩ = some f.1 /\
      e.1 ≠ f.1 /\
      canonicalEdgeSegment d.graph e ∈ d.active /\
      canonicalEdgeSegment d.graph f ∈ d.active /\
      FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
        (canonicalEdgeSegment d.graph f) /\
      sources d.graph (ofEdgeFun d.graph m) =
        {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1} := by
  unfold BondwiseSegmentProgram.CompleteEvent at h
  cases hedgeS : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ b => fluxBitConfig d.graph
            BackboneConcreteBondProgram.oddBit m b)
          ⟨d, []⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedgeS, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
        s.1 hfirst).elim
  | some e =>
      cases hedgeT : edgeOfSegment? d t with
      | none =>
          have hfirst : scan.firstAdmissible
              (fun _ b => fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m b)
              ⟨d, []⟩ = some s(s.1, s.1) := by
            simpa [program, encode, hedgeS, hedgeT, BondwiseSuffixEvent]
              using h.1
          exact (scan_firstAdmissible_ne_diagonal d
            (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
            s.1 hfirst).elim
      | some f =>
          have hselect : scan.Selects
              (fun _ b => fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m b)
              ⟨d, []⟩ [e.1, f.1] := by
            simpa [program, encode, hedgeS, hedgeT, BondwiseSuffixEvent]
              using h.1
          have hsegmentS : canonicalEdgeSegment d.graph e = s :=
            edgeOfSegment?_eq_some_spec d s e hedgeS
          have hsegmentT : canonicalEdgeSegment d.graph f = t :=
            edgeOfSegment?_eq_some_spec d t f hedgeT
          have hterminal :
              e.1 ≠ f.1 /\
              canonicalEdgeSegment d.graph e ∈ d.active /\
              canonicalEdgeSegment d.graph f ∈ d.active /\
              FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
                (canonicalEdgeSegment d.graph f) /\
              sources d.graph
                  (BackboneConcreteBondProgram.boolCurrent
                    (fluxBitConfig d.graph
                      BackboneConcreteBondProgram.oddBit m)) =
                {(canonicalEdgeSegment d.graph e).1,
                  (canonicalEdgeSegment d.graph e).2.1} ∆
                {(canonicalEdgeSegment d.graph f).1,
                  (canonicalEdgeSegment d.graph f).2.1} := by
            simpa [program, encode, hedgeS, hedgeT,
              BondwiseSegmentProgram.TerminalEvent, scan, terminal,
              boolSources, e.2, f.2] using h.2
          refine ⟨e, f, hsegmentS, hsegmentT, hselect.1,
            hselect.2.1, hterminal.1, hterminal.2.1,
            hterminal.2.2.1, hterminal.2.2.2.1, ?_⟩
          rw [← BackboneConcreteBondProgram.sources_boolCurrent_oddBit
            d.graph m]
          exact hterminal.2.2.2.2


theorem program_complete_three_cons_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t u : shb_ExplorationSegment V)
    (rest : List (shb_ExplorationSegment V)) :
    ¬program.CompleteEvent d (s :: t :: u :: rest) m := by
  intro h
  unfold BondwiseSegmentProgram.CompleteEvent at h
  have hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b)
      ⟨d, []⟩ = some s(s.1, s.1) := by
    simpa [program, encode, BondwiseSuffixEvent] using h.1
  exact scan_firstAdmissible_ne_diagonal d
    (fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit m)
    s.1 hfirst


theorem program_complete_word_shape
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    word = [] \/ (∃ s, word = [s]) \/ (∃ s t, word = [s, t]) := by
  cases word with
  | nil => exact Or.inl rfl
  | cons s rest =>
      cases rest with
      | nil => exact Or.inr (Or.inl ⟨s, rfl⟩)
      | cons t rest =>
          cases rest with
          | nil => exact Or.inr (Or.inr ⟨s, t, rfl⟩)
          | cons u rest => exact (program_complete_three_cons_false
              d m s t u rest h).elim


theorem canonicalEdgeSegment_start_ne_end
    (G : SimpleGraph V) (e : G.edgeFinset) :
    (canonicalEdgeSegment G e).1 ≠ (canonicalEdgeSegment G e).2.1 := by
  simp only [canonicalEdgeSegment]
  intro h
  have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
  apply G.not_isDiag_of_mem_edgeSet hedge
  rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
  exact h



theorem canonicalPair_boundary_ne_empty
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    {(canonicalEdgeSegment G e).1,
        (canonicalEdgeSegment G e).2.1} ∆
      {(canonicalEdgeSegment G f).1,
        (canonicalEdgeSegment G f).2.1} ≠ (∅ : Finset V) := by
  let s := canonicalEdgeSegment G e
  let t := canonicalEdgeSegment G f
  have hsne : s.1 ≠ s.2.1 := canonicalEdgeSegment_start_ne_end G e
  have hnotStart : s.1 ≠ t.1 := by
    intro h
    exact hsne (h.trans hpath.1.symm)
  have houter : s.1 ≠ t.2.1 := hpath.2
  have hmem : s.1 ∈ ({s.1, s.2.1} : Finset V) ∆ {t.1, t.2.1} := by
    rw [Finset.mem_symmDiff]
    exact Or.inl ⟨by simp, by simp [hnotStart, houter]⟩
  intro hempty
  rw [hempty] at hmem
  simp at hmem



noncomputable def canonicalPairPath
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    (⊤ : SimpleGraph V).Path (canonicalEdgeSegment G e).1
      (canonicalEdgeSegment G f).2.1 := by
  change (⊤ : SimpleGraph V).Path e.1.out.1 f.1.out.2
  have hjoin : e.1.out.2 = f.1.out.1 := hpath.1
  have houter : e.1.out.1 ≠ f.1.out.2 := hpath.2
  have hab : e.1.out.1 ≠ e.1.out.2 := by
    simpa only [canonicalEdgeSegment] using
      canonicalEdgeSegment_start_ne_end G e
  have hfc : f.1.out.1 ≠ f.1.out.2 := by
    simpa only [canonicalEdgeSegment] using
      canonicalEdgeSegment_start_ne_end G f
  have hbc : e.1.out.2 ≠ f.1.out.2 := by
    rw [hjoin]
    exact hfc
  let w : (⊤ : SimpleGraph V).Walk e.1.out.1 f.1.out.2 :=
    SimpleGraph.Walk.cons (by simpa using hab)
      (SimpleGraph.Walk.cons (by simpa using hbc)
        SimpleGraph.Walk.nil)
  refine ⟨w, ?_⟩
  simp [w, hab, hbc, houter]


theorem canonicalPairPath_edges
    (G : SimpleGraph V) (e f : G.edgeFinset)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e)
      (canonicalEdgeSegment G f)) :
    (canonicalPairPath G e f hpath).1.edges = [e.1, f.1] := by
  have hjoin : e.1.out.2 = f.1.out.1 := hpath.1
  have hedgeE : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
  have hedgeF : s(f.1.out.1, f.1.out.2) = f.1 := f.1.out_eq
  change [s(e.1.out.1, e.1.out.2),
    s(e.1.out.2, f.1.out.2)] = [e.1, f.1]
  rw [hedgeE, hjoin, hedgeF]


theorem complete_nil_singleton_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (hnil : program.CompleteEvent d [] m)
    (hsingle : program.CompleteEvent d [s] m) : False := by
  have hzero := (program_complete_nil_iff d m).mp hnil
  obtain ⟨e, _, _, _, hsource, _⟩ :=
    program_complete_singleton_data d m s hsingle
  rw [hzero] at hsource
  have hmem : (canonicalEdgeSegment d.graph e).1 ∈ (∅ : Finset V) := by
    rw [hsource]
    simp
  simp at hmem


theorem complete_nil_pair_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (hnil : program.CompleteEvent d [] m)
    (hpair : program.CompleteEvent d [s, t] m) : False := by
  have hzero := (program_complete_nil_iff d m).mp hnil
  obtain ⟨e, f, _, _, _, _, _, _, _, hpath, hsource⟩ :=
    program_complete_pair_data d m s t hpair
  apply canonicalPair_boundary_ne_empty d.graph e f hpath
  exact hsource.symm.trans hzero


theorem complete_singleton_pair_false
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t u : shb_ExplorationSegment V)
    (hsingle : program.CompleteEvent d [s] m)
    (hpair : program.CompleteEvent d [t, u] m) : False := by
  obtain ⟨e, _, hfirst, _, _, hfinished⟩ :=
    program_complete_singleton_data d m s hsingle
  obtain ⟨f, g, _, _, hfirst', hsecond, _, _, _, _, _⟩ :=
    program_complete_pair_data d m t u hpair
  have hef : e.1 = f.1 := Option.some.inj (hfirst.symm.trans hfirst')
  have hef' : e = f := Subtype.ext hef
  subst f
  rw [hfinished] at hsecond
  simp at hsecond


theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) : word = word' := by
  rcases program_complete_word_shape d m word hword with
    hnil | hsingle | hpair
  · subst word
    rcases program_complete_word_shape d m word' hword' with
      hnil' | hsingle' | hpair'
    · exact hnil'.symm
    · obtain ⟨s, rfl⟩ := hsingle'
      exact (complete_nil_singleton_false d m s hword hword').elim
    · obtain ⟨s, t, rfl⟩ := hpair'
      exact (complete_nil_pair_false d m s t hword hword').elim
  · obtain ⟨s, rfl⟩ := hsingle
    rcases program_complete_word_shape d m word' hword' with
      hnil' | hsingle' | hpair'
    · subst word'
      exact (complete_nil_singleton_false d m s hword' hword).elim
    · obtain ⟨t, rfl⟩ := hsingle'
      obtain ⟨e, hse, hfirst, _, _, _⟩ :=
        program_complete_singleton_data d m s hword
      obtain ⟨f, htf, hfirst', _, _, _⟩ :=
        program_complete_singleton_data d m t hword'
      have hef : e.1 = f.1 := Option.some.inj (hfirst.symm.trans hfirst')
      have hef' : e = f := Subtype.ext hef
      subst f
      rw [← hse, ← htf]
    · obtain ⟨t, u, rfl⟩ := hpair'
      exact (complete_singleton_pair_false d m s t u hword hword').elim
  · obtain ⟨s, t, rfl⟩ := hpair
    rcases program_complete_word_shape d m word' hword' with
      hnil' | hsingle' | hpair'
    · subst word'
      exact (complete_nil_pair_false d m s t hword' hword).elim
    · obtain ⟨u, rfl⟩ := hsingle'
      exact (complete_singleton_pair_false d m u s t hword' hword).elim
    · obtain ⟨u, v, rfl⟩ := hpair'
      obtain ⟨e, f, hse, htf, hfirst, hsecond, _, _, _, _, _⟩ :=
        program_complete_pair_data d m s t hword
      obtain ⟨e', f', hue, hvf, hfirst', hsecond', _, _, _, _, _⟩ :=
        program_complete_pair_data d m u v hword'
      have he : e.1 = e'.1 := Option.some.inj (hfirst.symm.trans hfirst')
      have he' : e = e' := Subtype.ext he
      subst e'
      have hf : f.1 = f'.1 := Option.some.inj (hsecond.symm.trans hsecond')
      have hf' : f = f' := Subtype.ext hf
      subst f'
      rw [← hse, ← htf, ← hue, ← hvf]




def sourceClass (_d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> Finset V
  | [] => ∅
  | [s] => {s.1, s.2.1}
  | [s, t] => {s.1, s.2.1} ∆ {t.1, t.2.1}
  | _ => ∅

@[simp] theorem sourceClass_nil (d : shb_ExplorationDomain V) :
    sourceClass d [] = ∅ := rfl


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
  rcases program_complete_word_shape d m word h with
    hnil | hsingle | hpair
  · subst word
    exact (program_complete_nil_iff d m).mp h
  · obtain ⟨s, rfl⟩ := hsingle
    obtain ⟨e, hsegment, _, _, hsource, _⟩ :=
      program_complete_singleton_data d m s h
    change sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1}
    rw [← hsegment]
    exact hsource
  · obtain ⟨s, t, rfl⟩ := hpair
    obtain ⟨e, f, hsegmentS, hsegmentT, _, _, _, _, _, _, hsource⟩ :=
      program_complete_pair_data d m s t h
    change sources d.graph (ofEdgeFun d.graph m) =
      {s.1, s.2.1} ∆ {t.1, t.2.1}
    rw [← hsegmentS, ← hsegmentT]
    exact hsource


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) : s ∈ d.active := by
  cases ss with
  | nil =>
      obtain ⟨e, hsegment, _, hactive, _, _⟩ :=
        program_complete_singleton_data d m s h
      simpa only [← hsegment] using hactive
  | cons t rest =>
      cases rest with
      | nil =>
          obtain ⟨e, f, hsegment, _, _, _, _, hactive, _, _, _⟩ :=
            program_complete_pair_data d m s t h
          simpa only [← hsegment] using hactive
      | cons u rest =>
          exact (program_complete_three_cons_false d m s t u rest h).elim


noncomputable def selectorSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) where
  sourceClass := sourceClass (V := V)
  sourceClass_nil := sourceClass_nil
  complete_functional := program_complete_functional
  sources_eq_sourceClass_of_complete :=
    sources_eq_sourceClass_of_program_complete
  complete_nil_iff := program_complete_nil_iff
  head_active_of_complete := head_active_of_program_complete




theorem program_complete_pair_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V) (e f : d.graph.edgeFinset)
    (hencodeS : edgeOfSegment? d s = some e)
    (hencodeT : edgeOfSegment? d t = some f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1)
    (hsecond : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1)
    (hne : e.1 ≠ f.1)
    (hactiveS : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveT : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f))
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1}) :
    program.CompleteEvent d [s, t] m := by
  constructor
  · have hselect : scan.Selects
        (fun _ b => fluxBitConfig d.graph
          BackboneConcreteBondProgram.oddBit m b)
        ⟨d, []⟩ [e.1, f.1] := ⟨hfirst, hsecond, trivial⟩
    simpa [program, encode, hencodeS, hencodeT, BondwiseSuffixEvent]
      using hselect
  · have hterminal :
        e.1 ≠ f.1 /\
        canonicalEdgeSegment d.graph e ∈ d.active /\
        canonicalEdgeSegment d.graph f ∈ d.active /\
        FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
          (canonicalEdgeSegment d.graph f) /\
        sources d.graph
            (BackboneConcreteBondProgram.boolCurrent
              (fluxBitConfig d.graph
                BackboneConcreteBondProgram.oddBit m)) =
          {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} ∆
            {(canonicalEdgeSegment d.graph f).1,
              (canonicalEdgeSegment d.graph f).2.1} := by
      refine ⟨hne, hactiveS, hactiveT, hpath, ?_⟩
      rw [BackboneConcreteBondProgram.sources_boolCurrent_oddBit]
      exact hsource
    simpa [program, encode, hencodeS, hencodeT,
      BondwiseSegmentProgram.TerminalEvent, scan, terminal, boolSources,
      e.2, f.2] using hterminal


theorem selectorSpec_fiber_pair_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V) (e f : d.graph.edgeFinset)
    (hencodeS : edgeOfSegment? d s = some e)
    (hencodeT : edgeOfSegment? d t = some f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, []⟩ = some e.1)
    (hsecond : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit m b) ⟨d, [e.1]⟩ = some f.1)
    (hne : e.1 ≠ f.1)
    (hactiveS : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveT : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f))
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1}) :
    (selectorSpec (V := V)).toPartialSelector.Fiber d [s, t] m := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_pair_of_scan_data d m s t e f hencodeS hencodeT
    hfirst hsecond hne hactiveS hactiveT hpath hsource




def twoUnitFlux (G : SimpleGraph V) (e f : G.edgeFinset) :
    G.edgeFinset -> Nat := fun g =>
  BackboneConcreteBondProgram.unitFlux G e g +
    BackboneConcreteBondProgram.unitFlux G f g



theorem sources_twoUnitFlux
    (G : SimpleGraph V) (e f : G.edgeFinset) :
    sources G (ofEdgeFun G (twoUnitFlux G e f)) =
      {(canonicalEdgeSegment G e).1,
          (canonicalEdgeSegment G e).2.1} ∆
        {(canonicalEdgeSegment G f).1,
          (canonicalEdgeSegment G f).2.1} := by
  unfold twoUnitFlux
  rw [← ofEdgeFun_add, sources_add,
    BackboneConcreteBondProgram.sources_unitFlux,
    BackboneConcreteBondProgram.sources_unitFlux]



theorem find?_eq_some_of_unique_true_mem
    {A : Type*} [DecidableEq A] (xs : List A) (a : A) (p : A -> Bool)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hp : ∀ x, x ∈ xs -> (p x = true <-> x = a)) :
    xs.find? p = some a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        simp [List.find?, (hp a (by simp)).mpr rfl]
      · have ha' : a ∈ xs := by simpa [Ne.symm hxa] using ha
        cases hpx : p x with
        | false =>
            simp only [List.find?, hpx]
            exact ih hnodup.2 ha' (fun y hy => hp y (by simp [hy]))
        | true => exact (hxa ((hp x (by simp)).mp hpx)).elim



theorem scan_secondAdmissible_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f) :
    scan.firstAdmissible
        (fun _ b => fluxBitConfig d.graph
          BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b)
        ⟨d, [e.1]⟩ = some f.1 := by
  unfold shb_DynamicEdgeExploration.firstAdmissible
  apply find?_eq_some_of_unique_true_mem
  · exact Finset.nodup_toList _
  · have hef : f.1 ≠ e.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    change f.1 ∈ (d.graph.edgeFinset.erase e.1).toList
    exact Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hef, f.2⟩)
  · intro b hb
    change b ∈ (d.graph.edgeFinset.erase e.1).toList at hb
    have hbErase : b ∈ d.graph.edgeFinset.erase e.1 :=
      Finset.mem_toList.mp hb
    have hbne : b ≠ e.1 := (Finset.mem_erase.mp hbErase).1
    have hbG : b ∈ d.graph.edgeFinset := (Finset.mem_erase.mp hbErase).2
    have hsube : (⟨b, hbG⟩ : d.graph.edgeFinset) ≠ e := by
      intro h
      exact hbne (congrArg Subtype.val h)
    constructor
    · intro hbit
      by_cases hsubf : (⟨b, hbG⟩ : d.graph.edgeFinset) = f
      · exact congrArg Subtype.val hsubf
      · change (if h : b ∈ d.graph.edgeFinset then
          BackboneConcreteBondProgram.oddBit
            (twoUnitFlux d.graph e f ⟨b, h⟩) else false) = true at hbit
        simp only [hbG, dite_true] at hbit
        simp [BackboneConcreteBondProgram.oddBit, twoUnitFlux,
          BackboneConcreteBondProgram.unitFlux, hsube, hsubf] at hbit
    · intro hbf
      subst b
      change (if h : f.1 ∈ d.graph.edgeFinset then
        BackboneConcreteBondProgram.oddBit
          (twoUnitFlux d.graph e f ⟨f.1, h⟩) else false) = true
      simp [f.2, BackboneConcreteBondProgram.oddBit, twoUnitFlux,
        BackboneConcreteBondProgram.unitFlux, hne.symm]




theorem program_complete_canonical_pair_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    program.CompleteEvent d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  apply program_complete_pair_of_scan_data d (twoUnitFlux d.graph e f)
    (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) e f
  · exact edgeOfSegment?_canonicalEdgeSegment d e
  · exact edgeOfSegment?_canonicalEdgeSegment d f
  · exact hfirst
  · exact scan_secondAdmissible_twoUnitFlux d e f hne
  · exact fun h => hne (Subtype.ext h)
  · exact hactiveE
  · exact hactiveF
  · exact hpath
  · exact sources_twoUnitFlux d.graph e f


theorem selectorSpec_fiber_canonical_pair_twoUnitFlux
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph
        BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    (selectorSpec (V := V)).toPartialSelector.Fiber d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
      (twoUnitFlux d.graph e f) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_canonical_pair_twoUnitFlux d e f hne hfirst
    hactiveE hactiveF hpath




def fin3PathGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet
    ({s((0 : Fin 3), 1), s((1 : Fin 3), 2)} : Set (Sym2 (Fin 3)))

@[simp] theorem fin3PathGraph_edgeFinset :
    fin3PathGraph.edgeFinset =
      {s((0 : Fin 3), 1), s((1 : Fin 3), 2)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, fin3PathGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    rcases he with rfl | rfl <;> decide


def fin3LeftEdge : fin3PathGraph.edgeFinset :=
  ⟨s((0 : Fin 3), 1), by simp⟩


def fin3RightEdge : fin3PathGraph.edgeFinset :=
  ⟨s((1 : Fin 3), 2), by simp⟩

theorem fin3LeftEdge_ne_rightEdge : fin3LeftEdge ≠ fin3RightEdge := by
  intro h
  have hv := congrArg Subtype.val h
  exact (by decide :
    s((0 : Fin 3), 1) ≠ s((1 : Fin 3), 2)) (by
      simpa [fin3LeftEdge, fin3RightEdge] using hv)



noncomputable def fin3PathDomain : shb_ExplorationDomain (Fin 3) where
  graph := fin3PathGraph
  active :=
    {canonicalEdgeSegment fin3PathGraph fin3LeftEdge,
      canonicalEdgeSegment fin3PathGraph fin3RightEdge}
  active_supported := by
    intro seg hseg edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseg
    rcases hseg with rfl | rfl
    · change edge ∈
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge).edgeSet at hedge
      rw [canonicalEdgeSegment_edgeSet] at hedge
      simp only [Set.mem_singleton_iff] at hedge
      subst edge
      exact SimpleGraph.mem_edgeFinset.mp fin3LeftEdge.2
    · change edge ∈
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge).edgeSet at hedge
      rw [canonicalEdgeSegment_edgeSet] at hedge
      simp only [Set.mem_singleton_iff] at hedge
      subst edge
      exact SimpleGraph.mem_edgeFinset.mp fin3RightEdge.2

@[simp] theorem fin3PathDomain_graph : fin3PathDomain.graph = fin3PathGraph :=
  rfl

@[simp] theorem fin3LeftEdge_active :
    canonicalEdgeSegment fin3PathGraph fin3LeftEdge ∈
      fin3PathDomain.active := by
  simp [fin3PathDomain]

@[simp] theorem fin3RightEdge_active :
    canonicalEdgeSegment fin3PathGraph fin3RightEdge ∈
      fin3PathDomain.active := by
  simp [fin3PathDomain]


def fin3PathFlux : fin3PathDomain.graph.edgeFinset -> Nat :=
  twoUnitFlux fin3PathDomain.graph fin3LeftEdge fin3RightEdge


def fin3LeftFirst : Prop :=
  scan.firstAdmissible
      (fun _ b => fluxBitConfig fin3PathDomain.graph
        BackboneConcreteBondProgram.oddBit fin3PathFlux b)
      ⟨fin3PathDomain, []⟩ = some fin3LeftEdge.1


def fin3RightFirst : Prop :=
  scan.firstAdmissible
      (fun _ b => fluxBitConfig fin3PathDomain.graph
        BackboneConcreteBondProgram.oddBit fin3PathFlux b)
      ⟨fin3PathDomain, []⟩ = some fin3RightEdge.1



theorem fin3_first_scan_cases : fin3LeftFirst ∨ fin3RightFirst := by
  let admissible : State (Fin 3) -> Sym2 (Fin 3) -> Bool :=
    fun _ b => fluxBitConfig fin3PathDomain.graph
      BackboneConcreteBondProgram.oddBit fin3PathFlux b
  cases hresult : scan.firstAdmissible admissible
      ⟨fin3PathDomain, []⟩ with
  | none =>
      have hfind :
          fin3PathDomain.graph.edgeFinset.1.toList.find?
              (admissible ⟨fin3PathDomain, []⟩) = none := by
        simpa [shb_DynamicEdgeExploration.firstAdmissible, scan]
          using hresult
      have hleftMem :
          fin3LeftEdge.1 ∈ fin3PathDomain.graph.edgeFinset.1.toList :=
        Finset.mem_toList.mpr fin3LeftEdge.2
      have hleftTrue :
          admissible ⟨fin3PathDomain, []⟩ fin3LeftEdge.1 = true := by
        unfold admissible fluxBitConfig
        have hmemDomain :
            fin3LeftEdge.1 ∈ fin3PathDomain.graph.edgeFinset :=
          fin3LeftEdge.2
        rw [dif_pos hmemDomain]
        change BackboneConcreteBondProgram.oddBit
          (fin3PathFlux fin3LeftEdge) = true
        rw [BackboneConcreteBondProgram.oddBit_eq_true_iff]
        change Odd
          (BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3LeftEdge fin3LeftEdge +
            BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3RightEdge fin3LeftEdge)
        rw [show BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3LeftEdge fin3LeftEdge = 1 by
            simp [BackboneConcreteBondProgram.unitFlux],
          show BackboneConcreteBondProgram.unitFlux fin3PathGraph
              fin3RightEdge fin3LeftEdge = 0 by
            simp [BackboneConcreteBondProgram.unitFlux,
              fin3LeftEdge_ne_rightEdge]]
        exact odd_one
      exact ((List.find?_eq_none.mp hfind) fin3LeftEdge.1
        hleftMem hleftTrue).elim
  | some edge =>
      have hedgeMem := scan.firstAdmissible_mem admissible
        ⟨fin3PathDomain, []⟩ edge hresult
      have hedgeList :
          edge ∈ fin3PathDomain.graph.edgeFinset.1.toList := by
        simpa [scan] using hedgeMem
      have hedgeGraph : edge ∈ fin3PathGraph.edgeFinset := by
        exact Finset.mem_toList.mp hedgeList
      rw [fin3PathGraph_edgeFinset] at hedgeGraph
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedgeGraph
      rcases hedgeGraph with hedge | hedge
      · left
        unfold fin3LeftFirst
        simpa [admissible, hedge] using hresult
      · right
        unfold fin3RightFirst
        simpa [admissible, hedge] using hresult


theorem fin3_first_scan_exclusive : ¬(fin3LeftFirst ∧ fin3RightFirst) := by
  rintro ⟨hleft, hright⟩
  have hedge : fin3LeftEdge.1 = fin3RightEdge.1 :=
    Option.some.inj (hleft.symm.trans hright)
  exact fin3LeftEdge_ne_rightEdge (Subtype.ext hedge)


theorem fin3LeftEdge_out_cases :
    fin3LeftEdge.1.out = ((0 : Fin 3), 1) ∨
      fin3LeftEdge.1.out = ((1 : Fin 3), 0) := by
  have hout := fin3LeftEdge.1.out_eq
  change s(fin3LeftEdge.1.out.1, fin3LeftEdge.1.out.2) =
    s((0 : Fin 3), 1) at hout
  rw [Sym2.eq, Sym2.rel_iff] at hout
  rcases hout with h | h
  · exact Or.inl (Prod.ext h.1 h.2)
  · exact Or.inr (Prod.ext h.1 h.2)


theorem fin3RightEdge_out_cases :
    fin3RightEdge.1.out = ((1 : Fin 3), 2) ∨
      fin3RightEdge.1.out = ((2 : Fin 3), 1) := by
  have hout := fin3RightEdge.1.out_eq
  change s(fin3RightEdge.1.out.1, fin3RightEdge.1.out.2) =
    s((1 : Fin 3), 2) at hout
  rw [Sym2.eq, Sym2.rel_iff] at hout
  rcases hout with h | h
  · exact Or.inl (Prod.ext h.1 h.2)
  · exact Or.inr (Prod.ext h.1 h.2)



theorem fin3_forward_path_iff :
    FormsTwoEdgePath
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge)
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge) <->
      fin3LeftEdge.1.out = ((0 : Fin 3), 1) /\
        fin3RightEdge.1.out = ((1 : Fin 3), 2) := by
  rcases fin3LeftEdge_out_cases with hleft | hleft <;>
    rcases fin3RightEdge_out_cases with hright | hright <;>
    simp [FormsTwoEdgePath, canonicalEdgeSegment, hleft, hright]



theorem fin3_reverse_path_iff :
    FormsTwoEdgePath
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge)
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) <->
      fin3RightEdge.1.out = ((2 : Fin 3), 1) /\
        fin3LeftEdge.1.out = ((1 : Fin 3), 0) := by
  rcases fin3LeftEdge_out_cases with hleft | hleft <;>
    rcases fin3RightEdge_out_cases with hright | hright <;>
    simp [FormsTwoEdgePath, canonicalEdgeSegment, hleft, hright]




theorem fin3_forward_fiber_iff :
    (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
        [canonicalEdgeSegment fin3PathGraph fin3LeftEdge,
          canonicalEdgeSegment fin3PathGraph fin3RightEdge]
        fin3PathFlux <->
      fin3LeftFirst /\
        FormsTwoEdgePath
          (canonicalEdgeSegment fin3PathGraph fin3LeftEdge)
          (canonicalEdgeSegment fin3PathGraph fin3RightEdge) := by
  constructor
  · intro hfiber
    rw [(selectorSpec (V := Fin 3)).fiber_iff_completeEvent] at hfiber
    obtain ⟨e, f, he, hf, hfirst, _, _, _, _, hpath, _⟩ :=
      program_complete_pair_data fin3PathDomain fin3PathFlux
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge)
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge) hfiber
    have heq : e = fin3LeftEdge :=
      canonicalEdgeSegment_injective fin3PathGraph he
    have hfeq : f = fin3RightEdge :=
      canonicalEdgeSegment_injective fin3PathGraph hf
    subst e
    subst f
    exact ⟨hfirst, hpath⟩
  · rintro ⟨hfirst, hpath⟩
    exact selectorSpec_fiber_canonical_pair_twoUnitFlux
      fin3PathDomain fin3LeftEdge fin3RightEdge
      fin3LeftEdge_ne_rightEdge hfirst fin3LeftEdge_active
      fin3RightEdge_active hpath


theorem fin3_reverse_fiber_iff :
    (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
        [canonicalEdgeSegment fin3PathGraph fin3RightEdge,
          canonicalEdgeSegment fin3PathGraph fin3LeftEdge]
        fin3PathFlux <->
      fin3RightFirst /\
        FormsTwoEdgePath
          (canonicalEdgeSegment fin3PathGraph fin3RightEdge)
          (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) := by
  constructor
  · intro hfiber
    rw [(selectorSpec (V := Fin 3)).fiber_iff_completeEvent] at hfiber
    obtain ⟨e, f, he, hf, hfirst, _, _, _, _, hpath, _⟩ :=
      program_complete_pair_data fin3PathDomain fin3PathFlux
        (canonicalEdgeSegment fin3PathGraph fin3RightEdge)
        (canonicalEdgeSegment fin3PathGraph fin3LeftEdge) hfiber
    have heq : e = fin3RightEdge :=
      canonicalEdgeSegment_injective fin3PathGraph he
    have hfeq : f = fin3LeftEdge :=
      canonicalEdgeSegment_injective fin3PathGraph hf
    subst e
    subst f
    exact ⟨hfirst, hpath⟩
  · rintro ⟨hfirst, hpath⟩
    have hfluxSwap :
        twoUnitFlux fin3PathDomain.graph fin3RightEdge fin3LeftEdge =
          fin3PathFlux := by
      funext g
      simp [fin3PathFlux, twoUnitFlux, Nat.add_comm]
    have hfirst' :
        scan.firstAdmissible
            (fun _ b => fluxBitConfig fin3PathDomain.graph
              BackboneConcreteBondProgram.oddBit
                (twoUnitFlux fin3PathDomain.graph
                  fin3RightEdge fin3LeftEdge) b)
            ⟨fin3PathDomain, []⟩ = some fin3RightEdge.1 := by
      rw [hfluxSwap]
      exact hfirst
    have hfiber := selectorSpec_fiber_canonical_pair_twoUnitFlux
      fin3PathDomain fin3RightEdge fin3LeftEdge
      fin3LeftEdge_ne_rightEdge.symm
      hfirst'
      fin3RightEdge_active fin3LeftEdge_active hpath
    rw [hfluxSwap] at hfiber
    exact hfiber




theorem fin3_twoSegment_fiber_iff_orientation_and_scan :
    ((selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
          [canonicalEdgeSegment fin3PathGraph fin3LeftEdge,
            canonicalEdgeSegment fin3PathGraph fin3RightEdge]
          fin3PathFlux ∨
        (selectorSpec (V := Fin 3)).toPartialSelector.Fiber fin3PathDomain
          [canonicalEdgeSegment fin3PathGraph fin3RightEdge,
            canonicalEdgeSegment fin3PathGraph fin3LeftEdge]
          fin3PathFlux) <->
      (fin3LeftFirst /\
          fin3LeftEdge.1.out = ((0 : Fin 3), 1) /\
          fin3RightEdge.1.out = ((1 : Fin 3), 2)) ∨
        (fin3RightFirst /\
          fin3RightEdge.1.out = ((2 : Fin 3), 1) /\
          fin3LeftEdge.1.out = ((1 : Fin 3), 0)) := by
  rw [fin3_forward_fiber_iff, fin3_reverse_fiber_iff,
    fin3_forward_path_iff, fin3_reverse_path_iff]





theorem program_realizes_selectorSpec :
    ProgramRealizes (program (V := V))
      (selectorSpec (V := V)).toPartialSelector := by
  exact ⟨selectorSpec (V := V), fun _ _ _ => Iff.rfl⟩



theorem selectorSpec_nonempty_canonicalCertificate_iff_toggleExists
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    Nonempty (AsymmetricBondwiseCoordinateCertificate
      ((program (V := V)).runSpec d (s :: ss))
      (residualVacuumRunSpec d s) (activeSegmentRunSpec d s hs)
      ((program (V := V)).liftedResidualRunSpec d s ss)
      (selectorSpec (V := V)).toPartialSelector beta J d s ss hs) <->
      (selectorSpec (V := V)).CanonicalBondwiseToggleExists
        beta J d s ss hs :=
  (selectorSpec (V := V)).nonempty_canonicalCertificate_iff_toggleExists
    beta J d s ss hs



theorem selectorSpec_canonicalToggleExists_of_componentwise
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : (selectorSpec (V := V)).CanonicalComponentwiseToggleExists
      beta J d s ss hs) :
    (selectorSpec (V := V)).CanonicalBondwiseToggleExists
      beta J d s ss hs :=
  (selectorSpec (V := V)).canonicalToggleExists_of_componentwise
    beta J d s ss hs h

end BackboneTwoEdgeBondProgram

end


end StatMech.Sharpness
