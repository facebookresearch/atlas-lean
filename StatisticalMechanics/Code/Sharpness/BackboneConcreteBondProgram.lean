/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.Sharpness.BackboneAsymmetricCoordinateCertificate

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector
open BackboneDeterminedCutSwitching

noncomputable local instance concreteBondDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _





structure SelectorRealization
    (P : BondwiseSegmentProgram V)
    (S : shb_PartialCurrentDynamicSelector (V := V)) where
  complete_iff_fiber : ∀ d word m,
    P.CompleteEvent d word m <-> S.Fiber d word m



noncomputable def SelectorRealization.toCompleteSpec
    {P : BondwiseSegmentProgram V}
    {S : shb_PartialCurrentDynamicSelector (V := V)}
    (R : SelectorRealization P S) : CompleteBondwiseSelectorSpec P where
  sourceClass := S.sourceClass
  sourceClass_nil := S.sourceClass_nil
  complete_functional := by
    intro d m word word' hword hword'
    have hfiber := (R.complete_iff_fiber d word m).mp hword
    have hfiber' := (R.complete_iff_fiber d word' m).mp hword'
    unfold shb_PartialCurrentDynamicSelector.Fiber at hfiber hfiber'
    exact Option.some.inj (hfiber.symm.trans hfiber')
  sources_eq_sourceClass_of_complete := by
    intro d m word hword
    exact S.sources_eq_sourceClass_of_select d m word
      ((R.complete_iff_fiber d word m).mp hword)
  complete_nil_iff := by
    intro d m
    exact (R.complete_iff_fiber d [] m).trans
      (S.select?_eq_some_nil_iff d m)
  head_active_of_complete := by
    intro d m s ss hword
    exact S.head_active_of_select d m s ss
      ((R.complete_iff_fiber d (s :: ss) m).mp hword)


def boolCurrent (omega : Sym2 V -> Bool) : Current V :=
  fun e => if omega e then 1 else 0


def oddBit (n : Nat) : Bool := decide (Odd n)

@[simp] theorem oddBit_eq_true_iff (n : Nat) : oddBit n = true <-> Odd n := by
  simp [oddBit]


theorem sources_boolCurrent_oddBit
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : G.edgeFinset -> Nat) :
    sources G (boolCurrent (fluxBitConfig G oddBit m)) =
      sources G (ofEdgeFun G m) := by
  ext v
  simp only [mem_sources]
  unfold incidentFlux boolCurrent fluxBitConfig
  let E := G.edgeFinset.filter (fun e => v ∈ e)
  have hfilter :
      E.filter (fun e => Odd
        (if (if h : e ∈ G.edgeFinset then oddBit (m ⟨e, h⟩) else false) = true
          then 1 else 0)) =
        E.filter (fun e => Odd (ofEdgeFun G m e)) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨heE, heodd⟩
      refine ⟨heE, ?_⟩
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp heE).1
      by_cases ho : Odd (m ⟨e, heG⟩)
      · simpa [ofEdgeFun, heG] using ho
      · simp [heG, oddBit, ofEdgeFun, ho] at heodd
    · rintro ⟨heE, heodd⟩
      refine ⟨heE, ?_⟩
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp heE).1
      have ho : Odd (m ⟨e, heG⟩) := by
        simpa [heG, ofEdgeFun] using heodd
      simp [heG, oddBit, ofEdgeFun, ho]
  rw [Finset.odd_sum_iff_odd_card_odd,
    Finset.odd_sum_iff_odd_card_odd]
  apply iff_of_eq
  simpa only [E] using congrArg Odd (congrArg Finset.card hfilter)



structure State (V : Type*) [Fintype V] [DecidableEq V] where
  domain : shb_ExplorationDomain V
  accepted : Option (Sym2 V)



noncomputable def canonicalEdgeSegment
    (G : SimpleGraph V)
    (e : G.edgeFinset) : shb_ExplorationSegment V := by
  let a := e.1.out.1
  let b := e.1.out.2
  have hab : s(a, b) = e.1 := e.1.out_eq
  have habne : a ≠ b := by
    intro h
    have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
    apply G.not_isDiag_of_mem_edgeSet hedge
    rw [← hab, Sym2.mk_isDiag_iff]
    exact h
  let w : (⊤ : SimpleGraph V).Walk a b :=
    SimpleGraph.Walk.cons (by simpa using habne) SimpleGraph.Walk.nil
  exact ⟨a, b, ⟨w, by simpa [w] using habne⟩⟩


theorem canonicalEdgeSegment_edgeSet
    (G : SimpleGraph V)
    (e : G.edgeFinset) :
    (canonicalEdgeSegment G e).edgeSet = {e.1} := by
  simp only [canonicalEdgeSegment]
  ext f
  simp only [shb_AmbientSegment.edgeSet, Set.mem_setOf_eq,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.mem_singleton, Set.mem_singleton_iff]
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
  rw [hout]


noncomputable def edgeOfSegment?
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    Option d.graph.edgeFinset :=
  if h : ∃ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s then
    some (Classical.choose h)
  else none

theorem edgeOfSegment?_eq_some_spec
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (e : d.graph.edgeFinset)
    (h : edgeOfSegment? d s = some e) :
    canonicalEdgeSegment d.graph e = s := by
  unfold edgeOfSegment? at h
  split at h
  · rename_i hex
    have he : Classical.choose hex = e := Option.some.inj h
    simpa [he] using Classical.choose_spec hex
  · simp at h



noncomputable def encode
    (d : shb_ExplorationDomain V) :
    List (shb_ExplorationSegment V) -> List (Sym2 V)
  | [] => []
  | [s] =>
      match edgeOfSegment? d s with
      | some e => [e.1]
      | none => [s(s.1, s.1)]
  | s :: _ :: _ => [s(s.1, s.1)]


noncomputable def scan :
    shb_DynamicEdgeExploration (State V) (Sym2 V) where
  edgeOrder := fun st =>
    match st.accepted with
    | none => st.domain.graph.edgeFinset.1.toList
    | some _ => []
  edgeOrder_nodup := by
    intro st
    cases st.accepted
    · exact Finset.nodup_toList _
    · simp
  advance := fun st e => ⟨st.domain, some e⟩


def boolSources (st : State V) (omega : Sym2 V -> Bool) : Finset V :=
  sources st.domain.graph (boolCurrent omega)


def terminal (st : State V) (omega : Sym2 V -> Bool) : Prop :=
  match st.accepted with
  | none => boolSources st omega = ∅
  | some e =>
      if he : e ∈ st.domain.graph.edgeFinset then
        canonicalEdgeSegment st.domain.graph ⟨e, he⟩ ∈ st.domain.active /\
          boolSources st omega =
            {(canonicalEdgeSegment st.domain.graph ⟨e, he⟩).1,
              (canonicalEdgeSegment st.domain.graph ⟨e, he⟩).2.1}
      else False


noncomputable def program : BondwiseSegmentProgram V where
  State := State V
  scan := scan
  initial := fun d => ⟨d, none⟩
  encode := encode
  bit := oddBit
  terminal := terminal

@[simp] theorem program_complete_nil_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    program.CompleteEvent d [] m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  change (True /\ sources d.graph
    (boolCurrent (fluxBitConfig d.graph oddBit m)) = ∅) <-> _
  rw [sources_boolCurrent_oddBit]
  simp


theorem scan_firstAdmissible_ne_diagonal
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool) (x : V) :
    scan.firstAdmissible (fun _ e => omega e) ⟨d, none⟩ ≠ some s(x, x) := by
  intro h
  have hmem := scan.firstAdmissible_mem (fun _ e => omega e)
    ⟨d, none⟩ s(x, x) h
  have hedge : s(x, x) ∈ d.graph.edgeFinset := by
    simpa [scan] using hmem
  have hadj : d.graph.Adj x x := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  exact d.graph.loopless.irrefl x hadj



theorem find?_eq_some_of_unique_true
    {A : Type*} [DecidableEq A] (xs : List A) (a : A) (p : A -> Bool)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hp : ∀ x, p x = true <-> x = a) :
    xs.find? p = some a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        simp [List.find?, (hp a).mpr rfl]
      · have ha' : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | ha'
          · exact (hxa hax.symm).elim
          · exact ha'
        cases hpx : p x with
        | false => simpa [List.find?, hpx] using ih hnodup.2 ha'
        | true => exact (hxa ((hp x).mp hpx)).elim


def unitFlux (G : SimpleGraph V) (e : G.edgeFinset) :
    G.edgeFinset -> Nat := fun f => if f = e then 1 else 0


theorem scan_firstAdmissible_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    scan.firstAdmissible
        (fun _ f => fluxBitConfig d.graph oddBit (unitFlux d.graph e) f)
        ⟨d, none⟩ = some e.1 := by
  unfold shb_DynamicEdgeExploration.firstAdmissible
  apply find?_eq_some_of_unique_true
  · exact Finset.nodup_toList _
  · simpa [scan] using e.2
  · intro f
    constructor
    · intro hf
      change fluxBitConfig d.graph oddBit (unitFlux d.graph e) f = true at hf
      unfold fluxBitConfig at hf
      split at hf
      · rename_i hfg
        have heq : (⟨f, hfg⟩ : d.graph.edgeFinset) = e := by
          by_contra hne
          simp [oddBit, unitFlux, hne] at hf
        exact congrArg Subtype.val heq
      · simp at hf
    · intro hfe
      subst f
      change fluxBitConfig d.graph oddBit (unitFlux d.graph e) e.1 = true
      simp [fluxBitConfig, e.2, oddBit, unitFlux]



theorem sources_unitFlux
    (G : SimpleGraph V) (e : G.edgeFinset) :
    sources G (ofEdgeFun G (unitFlux G e)) =
      {(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} := by
  ext v
  rw [mem_sources]
  have hcurrent :
      ofEdgeFun G (unitFlux G e) = fun f => if f = e.1 then 1 else 0 := by
    funext f
    unfold ofEdgeFun unitFlux
    split
    · rename_i hf
      by_cases hfe : f = e.1
      · subst f
        simp
      · have hsub : (⟨f, hf⟩ : G.edgeFinset) ≠ e := by
          intro h
          exact hfe (congrArg Subtype.val h)
        simp [hfe, hsub]
    · rename_i hf
      have hfe : f ≠ e.1 := by
        intro h
        subst f
        exact hf e.2
      simp [hfe]
  rw [hcurrent]
  have hflux :
      incidentFlux G (fun f => if f = e.1 then 1 else 0) v =
        if v ∈ e.1 then 1 else 0 := by
    unfold incidentFlux
    by_cases hv : v ∈ e.1
    · rw [if_pos hv]
      simp [hv, e.2]
    · rw [if_neg hv]
      apply Finset.sum_eq_zero
      intro f hf
      have hfe : f ≠ e.1 := by
        intro h
        subst f
        exact hv (Finset.mem_filter.mp hf).2
      simp [hfe]
  rw [hflux]
  have hviff : v ∈ e.1 <-> v = e.1.out.1 ∨ v = e.1.out.2 := by
    calc
      v ∈ e.1 <-> v ∈ s(e.1.out.1, e.1.out.2) :=
        iff_of_eq (congrArg (fun z : Sym2 V => v ∈ z) e.1.out_eq).symm
      _ <-> v = e.1.out.1 ∨ v = e.1.out.2 := Sym2.mem_iff
  simp only [canonicalEdgeSegment, Finset.mem_insert, Finset.mem_singleton]
  by_cases hv : v ∈ e.1
  · rw [if_pos hv]
    exact ⟨fun _ => hviff.mp hv, fun _ => odd_one⟩
  · rw [if_neg hv]
    exact ⟨fun hodd => (by simp at hodd), fun hends => (hv (hviff.mpr hends)).elim⟩


theorem canonicalEdgeSegment_injective (G : SimpleGraph V) :
    Function.Injective (canonicalEdgeSegment G) := by
  intro e f hsegment
  have hedges := congrArg shb_AmbientSegment.edgeSet hsegment
  rw [canonicalEdgeSegment_edgeSet, canonicalEdgeSegment_edgeSet] at hedges
  exact Subtype.ext (Set.singleton_eq_singleton_iff.mp hedges)


@[simp] theorem edgeOfSegment?_canonicalEdgeSegment
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    edgeOfSegment? d (canonicalEdgeSegment d.graph e) = some e := by
  unfold edgeOfSegment?
  split
  · rename_i hex
    have hchosen := Classical.choose_spec hex
    have heq : Classical.choose hex = e :=
      canonicalEdgeSegment_injective d.graph hchosen
    simp [heq]
  · rename_i hnone
    exact (hnone ⟨e, rfl⟩).elim


@[simp] theorem edgeOfSegment?_canonical
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    edgeOfSegment? d (canonicalEdgeSegment d.graph e) = some e :=
  edgeOfSegment?_canonicalEdgeSegment d e



theorem program_complete_singleton_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e = s /\
        canonicalEdgeSegment d.graph e ∈ d.active /\
          sources d.graph (ofEdgeFun d.graph m) =
            {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} := by
  unfold BondwiseSegmentProgram.CompleteEvent at h
  cases hedge : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e)
          ⟨d, none⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
  | some e =>
      have hspec : canonicalEdgeSegment d.graph e = s :=
        edgeOfSegment?_eq_some_spec d s e hedge
      have hterminal :
          canonicalEdgeSegment d.graph e ∈ d.active /\
            sources d.graph
                (boolCurrent (fluxBitConfig d.graph oddBit m)) =
              {(canonicalEdgeSegment d.graph e).1,
                (canonicalEdgeSegment d.graph e).2.1} := by
        simpa [program, encode, hedge, BondwiseSegmentProgram.TerminalEvent,
          scan, terminal, boolSources, e.2] using h.2
      refine ⟨e, hspec, hterminal.1, ?_⟩
      rw [← sources_boolCurrent_oddBit d.graph m]
      exact hterminal.2




theorem program_complete_singleton_data_with_scan
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset,
      scan.firstAdmissible
          (fun _ f => fluxBitConfig d.graph oddBit m f) ⟨d, none⟩ =
          some e.1 /\
        canonicalEdgeSegment d.graph e = s /\
          canonicalEdgeSegment d.graph e ∈ d.active /\
            sources d.graph (ofEdgeFun d.graph m) =
              {(canonicalEdgeSegment d.graph e).1,
                (canonicalEdgeSegment d.graph e).2.1} := by
  obtain ⟨e, hsegment, hactive, hsources⟩ :=
    program_complete_singleton_data d m s h
  have hencode : edgeOfSegment? d s = some e := by
    rw [← hsegment]
    exact edgeOfSegment?_canonicalEdgeSegment d e
  have hfirst : scan.firstAdmissible
      (fun _ f => fluxBitConfig d.graph oddBit m f) ⟨d, none⟩ =
      some e.1 := by
    simpa [program, encode, hencode, BondwiseSuffixEvent] using h.1
  exact ⟨e, hfirst, hsegment, hactive, hsources⟩





theorem scan_selects_length_le_one
    (d : shb_ExplorationDomain V) (omega : Sym2 V -> Bool)
    (bonds : List (Sym2 V))
    (hselect : scan.Selects (fun _ e => omega e) ⟨d, none⟩ bonds) :
    bonds.length <= 1 := by
  cases bonds with
  | nil => simp
  | cons accepted rest =>
      cases rest with
      | nil => simp
      | cons next tail =>
          have hnext := hselect.2.1
          simp [scan, shb_DynamicEdgeExploration.firstAdmissible] at hnext


theorem program_complete_word_eq_nil_or_singleton
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    word = [] \/ ∃ s, word = [s] := by
  cases word with
  | nil => exact Or.inl rfl
  | cons s rest =>
      cases rest with
      | nil => exact Or.inr ⟨s, rfl⟩
      | cons t tail =>
          have hfirst : scan.firstAdmissible
              (fun _ e => fluxBitConfig d.graph oddBit m e)
              ⟨d, none⟩ = some s(s.1, s.1) := by
            simpa [program, encode, BondwiseSuffixEvent] using h.1
          exact (scan_firstAdmissible_ne_diagonal d
            (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim


theorem program_complete_cons_tail_eq_nil
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) : ss = [] := by
  rcases program_complete_word_eq_nil_or_singleton d m (s :: ss) h with
    hnil | ⟨t, hsingleton⟩
  · simp at hnil
  · simpa using congrArg List.tail hsingleton



theorem edgeOfSegment?_eq_some_of_program_complete_singleton
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : program.CompleteEvent d [s] m) :
    ∃ e : d.graph.edgeFinset, edgeOfSegment? d s = some e := by
  cases hedge : edgeOfSegment? d s with
  | none =>
      have hfirst : scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e)
          ⟨d, none⟩ = some s(s.1, s.1) := by
        simpa [program, encode, hedge, BondwiseSuffixEvent] using h.1
      exact (scan_firstAdmissible_ne_diagonal d
        (fluxBitConfig d.graph oddBit m) s.1 hfirst).elim
  | some e => exact ⟨e, rfl⟩


theorem program_complete_singleton_injective
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (hs : program.CompleteEvent d [s] m)
    (ht : program.CompleteEvent d [t] m) :
    s = t := by
  obtain ⟨es, hedgeS⟩ :=
    edgeOfSegment?_eq_some_of_program_complete_singleton d m s hs
  obtain ⟨et, hedgeT⟩ :=
    edgeOfSegment?_eq_some_of_program_complete_singleton d m t ht
  have hses := edgeOfSegment?_eq_some_spec d s es hedgeS
  have htet := edgeOfSegment?_eq_some_spec d t et hedgeT
  have hselectS :
      scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, none⟩ =
        some es.1 := by
    simpa [program, encode, hedgeS, BondwiseSuffixEvent] using hs.1
  have hselectT :
      scan.firstAdmissible
          (fun _ e => fluxBitConfig d.graph oddBit m e) ⟨d, none⟩ =
        some et.1 := by
    simpa [program, encode, hedgeT, BondwiseSuffixEvent] using ht.1
  have he : es.1 = et.1 := Option.some.inj (hselectS.symm.trans hselectT)
  have hesub : es = et := Subtype.ext he
  exact hses.symm.trans (hesub ▸ htet)


def sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  | _, [s] => {s.1, s.2.1}
  | _, _ => ∅

@[simp] theorem sourceClass_nil (d : shb_ExplorationDomain V) :
    sourceClass d [] = ∅ := rfl

@[simp] theorem sourceClass_singleton
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    sourceClass d [s] = {s.1, s.2.1} := rfl



theorem program_complete_functional
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word word' : List (shb_ExplorationSegment V))
    (hword : program.CompleteEvent d word m)
    (hword' : program.CompleteEvent d word' m) :
    word = word' := by
  rcases program_complete_word_eq_nil_or_singleton d m word hword with
    rfl | ⟨s, rfl⟩
  · rcases program_complete_word_eq_nil_or_singleton d m word' hword' with
      rfl | ⟨t, rfl⟩
    · rfl
    · have hnil := (program_complete_nil_iff d m).mp hword
      obtain ⟨e, _, _, hsrc⟩ := program_complete_singleton_data d m t hword'
      rw [hnil] at hsrc
      have hmem := congrArg
        (fun U : Finset V => (canonicalEdgeSegment d.graph e).1 ∈ U) hsrc
      simp at hmem
  · rcases program_complete_word_eq_nil_or_singleton d m word' hword' with
      rfl | ⟨t, rfl⟩
    · have hnil := (program_complete_nil_iff d m).mp hword'
      obtain ⟨e, _, _, hsrc⟩ := program_complete_singleton_data d m s hword
      rw [hnil] at hsrc
      have hmem := congrArg
        (fun U : Finset V => (canonicalEdgeSegment d.graph e).1 ∈ U) hsrc
      simp at hmem
    · simpa [program_complete_singleton_injective d m s t hword hword']


theorem sources_eq_sourceClass_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) :
    sources d.graph (ofEdgeFun d.graph m) = sourceClass d word := by
  rcases program_complete_word_eq_nil_or_singleton d m word h with
    rfl | ⟨s, rfl⟩
  · exact (program_complete_nil_iff d m).mp h
  · obtain ⟨e, hes, _, hsrc⟩ :=
      program_complete_singleton_data d m s h
    subst s
    exact hsrc


theorem head_active_of_program_complete
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d (s :: ss) m) :
    s ∈ d.active := by
  rcases program_complete_word_eq_nil_or_singleton d m (s :: ss) h with
    hnil | ⟨t, hsingleton⟩
  · simp at hnil
  · have htail : ss = [] := by simpa using congrArg List.tail hsingleton
    subst ss
    obtain ⟨e, hes, hactive, _⟩ :=
      program_complete_singleton_data d m s h
    simpa only [hes] using hactive





noncomputable def selectorSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) where
  sourceClass := sourceClass (V := V)
  sourceClass_nil := sourceClass_nil
  complete_functional := program_complete_functional
  sources_eq_sourceClass_of_complete :=
    sources_eq_sourceClass_of_program_complete
  complete_nil_iff := program_complete_nil_iff
  head_active_of_complete := head_active_of_program_complete


noncomputable abbrev completeSpec :
    CompleteBondwiseSelectorSpec (V := V) (program (V := V)) :=
  selectorSpec (V := V)




theorem program_complete_singleton_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (e : d.graph.edgeFinset)
    (hencode : edgeOfSegment? d s = some e)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit m b) ⟨d, none⟩ = some e.1)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1}) :
    program.CompleteEvent d [s] m := by
  constructor
  · simpa [program, encode, hencode, BondwiseSuffixEvent] using hfirst
  · have hterminal :
        canonicalEdgeSegment d.graph e ∈ d.active /\
          sources d.graph (boolCurrent (fluxBitConfig d.graph oddBit m)) =
            {(canonicalEdgeSegment d.graph e).1,
              (canonicalEdgeSegment d.graph e).2.1} := by
      refine ⟨hactive, ?_⟩
      rw [sources_boolCurrent_oddBit]
      exact hsource
    simpa [program, encode, hencode, BondwiseSegmentProgram.TerminalEvent,
      scan, terminal, boolSources, e.2] using hterminal



theorem selectorSpec_fiber_singleton_of_scan_data
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) (e : d.graph.edgeFinset)
    (hencode : edgeOfSegment? d s = some e)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit m b) ⟨d, none⟩ = some e.1)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hsource : sources d.graph (ofEdgeFun d.graph m) =
      {(canonicalEdgeSegment d.graph e).1,
        (canonicalEdgeSegment d.graph e).2.1}) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d [s] m := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_singleton_of_scan_data d m s e hencode hfirst
    hactive hsource



theorem program_complete_canonical_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    program.CompleteEvent d [canonicalEdgeSegment d.graph e]
      (unitFlux d.graph e) := by
  exact program_complete_singleton_of_scan_data d (unitFlux d.graph e)
    (canonicalEdgeSegment d.graph e) e
    (edgeOfSegment?_canonicalEdgeSegment d e)
    (scan_firstAdmissible_unitFlux d e) hactive
    (sources_unitFlux d.graph e)


theorem program_complete_canonicalEdge
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    program.CompleteEvent d [canonicalEdgeSegment d.graph e]
      (unitFlux d.graph e) :=
  program_complete_canonical_unitFlux d e hactive



theorem selectorSpec_fiber_canonical_unitFlux
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    ((selectorSpec (V := V)).toPartialSelector).Fiber d
      [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
  rw [(selectorSpec (V := V)).fiber_iff_completeEvent]
  exact program_complete_canonical_unitFlux d e hactive


theorem concrete_selector_fiber_canonicalEdge
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
    ((completeSpec (V := V)).toPartialSelector).Fiber d
      [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) :=
  selectorSpec_fiber_canonical_unitFlux d e hactive




theorem selectorSpec_fiber_nonempty_is_singleton
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (h : ((selectorSpec (V := V)).toPartialSelector).Fiber
      d (s :: ss) m) :
    ss = [] := by
  have hcomplete :=
    ((selectorSpec (V := V)).fiber_iff_completeEvent d (s :: ss) m).mp h
  rcases program_complete_word_eq_nil_or_singleton d m (s :: ss) hcomplete with
    hnil | ⟨t, hsingleton⟩
  · simp at hnil
  · simpa using congrArg List.tail hsingleton





noncomputable def completeSpecRealization :
    SelectorRealization (program (V := V))
      (completeSpec (V := V)).toPartialSelector where
  complete_iff_fiber := by
    intro d word m
    exact ((completeSpec (V := V)).fiber_iff_completeEvent d word m).symm




abbrev IntendedOneStepRealization :=
  SelectorRealization (program (V := V))
    (shb_oneStepPartialSelector (V := V))




theorem intendedOneStepRealization_isEmpty_of_noncanonical_chosen
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅)
    (hchosen : shb_oneStepChosenSegment d m = some s)
    (hnoncanonical : ∀ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e ≠ s) :
    IsEmpty (IntendedOneStepRealization (V := V)) := by
  constructor
  intro R
  have hfiber : shb_oneStepPartialSelector.Fiber d [s] m := by
    unfold shb_PartialCurrentDynamicSelector.Fiber
    change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
      else (shb_oneStepChosenSegment d m).map (fun t => [t])) = some [s]
    rw [if_neg hsrc, hchosen]
    rfl
  have hcomplete := (R.complete_iff_fiber d [s] m).mpr hfiber
  obtain ⟨e, hsegment, _, _⟩ :=
    program_complete_singleton_data d m s hcomplete
  exact hnoncanonical e hsegment





def ProgramRealizes
    (P : BondwiseSegmentProgram V)
    (S : shb_PartialCurrentDynamicSelector (V := V)) : Prop :=
  ∃ R : CompleteBondwiseSelectorSpec P,
    ∀ (d : shb_ExplorationDomain V)
      (word : List (shb_ExplorationSegment V))
      (m : d.graph.edgeFinset -> Nat),
      R.toPartialSelector.Fiber d word m <-> S.Fiber d word m



theorem SelectorRealization.programRealizes
    {P : BondwiseSegmentProgram V}
    {S : shb_PartialCurrentDynamicSelector (V := V)}
    (R : SelectorRealization P S) : ProgramRealizes P S := by
  refine ⟨R.toCompleteSpec, ?_⟩
  intro d word m
  exact (R.toCompleteSpec.fiber_iff_completeEvent d word m).trans
    (R.complete_iff_fiber d word m)




theorem nonempty_selectorRealization_iff_programRealizes
    (P : BondwiseSegmentProgram V)
    (S : shb_PartialCurrentDynamicSelector (V := V)) :
    Nonempty (SelectorRealization P S) <-> ProgramRealizes P S := by
  constructor
  · rintro ⟨R⟩
    exact R.programRealizes
  · rintro ⟨R, hrealizes⟩
    refine ⟨⟨?_⟩⟩
    intro d word m
    exact (R.fiber_iff_completeEvent d word m).symm.trans
      (hrealizes d word m)


theorem program_realizes_selectorSpec :
    ProgramRealizes (program (V := V))
      (selectorSpec (V := V)).toPartialSelector := by
  exact ⟨selectorSpec (V := V), fun _ _ _ => Iff.rfl⟩






theorem program_not_realizes_of_two_segment_fiber
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s t : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (hfiber : S.Fiber d (s :: t :: ss) m) :
    ¬ProgramRealizes (program (V := V)) S := by
  rintro ⟨R, hrealizes⟩
  have hcomplete : program.CompleteEvent d (s :: t :: ss) m :=
    (R.fiber_iff_completeEvent d (s :: t :: ss) m).mp
      ((hrealizes d (s :: t :: ss) m).mpr hfiber)
  rcases program_complete_word_eq_nil_or_singleton d m (s :: t :: ss)
      hcomplete with hnil | ⟨u, hsingleton⟩
  · simp at hnil
  · simp at hsingleton





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

end BackboneConcreteBondProgram

end

end StatMech.Sharpness
