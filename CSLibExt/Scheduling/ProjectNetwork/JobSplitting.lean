/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetworkCriticalPath
public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import Mathlib.Combinatorics.Digraph.Basic

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Scheduling.ProjectNetwork

open MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Job splitting: a precedence table as an activity-on-arc network

A finite job type `J`, durations `d : J → ℕ` in ticks (zero allowed: a milestone) and a
precedence digraph `G : Digraph J`, where `G.Adj i j` means job `i` must finish before job `j`
starts (finish-to-start, zero lag). Start ticks `s : J → ℕ` are precedence-feasible when
`s i + d i ≤ s j` whenever `G.Adj i j`; job `j` finishes at `s j + d j`, and resources are
unlimited. The project finish is the latest job finish, `Finset.univ.sup fun j => s j + d j`,
which is `0` for an empty job type. A start job has no predecessor and a finish job has no
successor; an isolated job is both. Read `J` as a construction table's jobs for the example.

The split network has the events `source`, `sink`, `input j` and `output j`. Its arcs are the
duration arc of each job `j`, from `input j` to `output j` with duration `d j`; for each
`G.Adj i j` a precedence arc from `output i` to `input j`; for each start job `j` a source arc
from `source` to `input j`; for each finish job `j` a sink arc from `output j` to `sink`; and
the declared source-to-sink arc, present for every table. Every arc other than a duration arc
has duration `0`. Job `j` starts at its input event and finishes at its output event. The job
sequence of an arc list is the list of jobs of its duration arcs in traversal order,
`l.filterMap SplitArc.job?`. Because the declared arc is always present, a critical path may
be the declared arc, with the empty job sequence, exactly when the longest start-to-finish
chain has duration `0`, nonempty tables included; for an empty job type it is the only
source-to-sink walk and the project finish is `0`.

This module proves that finish times and path durations agree between the table and the split
network in both directions, transports the owner critical-path lower bound to job schedules,
and discharges the owner premises for the split network of a finite acyclic table, so
`exists_isFeasibleSchedule_eq_sum` applies to it directly.

References: J. J. Moder, C. R. Phillips and E. W. Davis, *Project Management with CPM, PERT
and Precedence Diagramming*, 3rd edition, Van Nostrand Reinhold, 1983 (activity-on-arrow
networks and dummy activities); J. E. Kelley Jr. and M. R. Walker, Critical-path planning and
scheduling, *Proceedings of the Eastern Joint Computer Conference*, 1959, pp. 160-173.
-/

/-- Events of the job-splitting network of a job table with jobs `J`. -/
inductive SplitEvent (J : Type*) where
  /-- The project source event. -/
  | source
  /-- The project sink event. -/
  | sink
  /-- The input event of job `j`, where the job starts. -/
  | input (j : J)
  /-- The output event of job `j`, where the job has finished. -/
  | output (j : J)
/-- Arcs of the job-splitting network of the precedence digraph `G` on jobs `J`. -/
inductive SplitArc {J : Type*} (G : Digraph J) where
  /-- The duration arc of job `j`, from its input event to its output event. -/
  | job (j : J)
  /-- The zero-lag precedence arc from the output event of `i` to the input event of `j`. -/
  | precedence (i j : J) (h : G.Adj i j)
  /-- The zero-lag source arc into the input event of a start job `j`. -/
  | fromSource (j : J) (h : ∀ i, ¬ G.Adj i j)
  /-- The zero-lag sink arc out of the output event of a finish job `j`. -/
  | toSink (j : J) (h : ∀ k, ¬ G.Adj j k)
  /-- The declared zero-lag source-to-sink arc, present for every table. -/
  | sourceSink
/-- Tail event of an arc of the split network. -/
def splitTail {J : Type*} (G : Digraph J) : SplitArc G → SplitEvent J
  | .job j => .input j
  | .precedence i _ _ => .output i
  | .fromSource _ _ => .source
  | .toSink j _ => .output j
  | .sourceSink => .source
/-- Head event of an arc of the split network. -/
def splitHead {J : Type*} (G : Digraph J) : SplitArc G → SplitEvent J
  | .job j => .output j
  | .precedence _ j _ => .input j
  | .fromSource j _ => .input j
  | .toSink _ _ => .sink
  | .sourceSink => .sink
/-- Duration of an arc of the split network in ticks: `d j` on the duration arc of job `j`,
and `0` on every precedence, source, sink and source-to-sink arc. -/
def splitDuration {J : Type*} (G : Digraph J) (d : J → ℕ) : SplitArc G → ℕ
  | .job j => d j
  | _ => 0
/-- The job of a duration arc; `none` on every zero-lag arc. -/
def SplitArc.job? {J : Type*} {G : Digraph J} : SplitArc G → Option J
  | .job j => some j
  | _ => none
/-- Start ticks `s` are precedence-feasible for the digraph `G` and durations `d`: whenever job
`i` precedes job `j`, job `j` starts no earlier than job `i` finishes (finish-to-start, zero
lag). -/
def IsPrecedenceFeasible {J : Type*} (G : Digraph J) (d s : J → ℕ) : Prop :=
  ∀ ⦃i j⦄, G.Adj i j → s i + d i ≤ s j
/-- Project finish of the start ticks `s` with durations `d`: the latest job finish
`s j + d j`, and `0` for an empty job type. -/
def projectFinish {J : Type*} [Fintype J] (d s : J → ℕ) : ℕ :=
  Finset.univ.sup fun j => s j + d j
/-- Event schedule of the split network induced by start ticks `s`: the source at tick `0`, the
input and output events of each job at its start and finish, and the sink at the project
finish. -/
def embedSchedule {J : Type*} [Fintype J] (d s : J → ℕ) : SplitEvent J → ℕ
  | .source => 0
  | .sink => projectFinish d s
  | .input j => s j
  | .output j => s j + d j
/-- Finish times agree, table to network: precedence-feasible start ticks embed as a feasible
event schedule of the split network, with the source at tick `0`, each job's input and output
events at its start and finish, and the sink at the project finish. -/
theorem isFeasibleSchedule_embedSchedule {J : Type*} [Fintype J] {G : Digraph J}
    {d s : J → ℕ} (hs : IsPrecedenceFeasible G d s) :
    IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) (embedSchedule d s) := by
  intro e
  cases e with
  | job j =>
      show s j + d j ≤ s j + d j
      exact le_refl _
  | precedence i j h =>
      show s i + d i + 0 ≤ s j
      have hle := hs h
      omega
  | fromSource j h =>
      show 0 + 0 ≤ s j
      omega
  | toSink j h =>
      show s j + d j + 0 ≤ projectFinish d s
      have hle : s j + d j ≤ projectFinish d s :=
        Finset.le_sup (s := Finset.univ) (f := fun j => s j + d j) (Finset.mem_univ j)
      omega
  | sourceSink =>
      show 0 + 0 ≤ projectFinish d s
      omega
/-- Finish times agree, network to table, precedence part: the input event times of every
feasible event schedule of the split network are precedence-feasible start ticks. -/
theorem isPrecedenceFeasible_input {J : Type*} {G : Digraph J} {d : J → ℕ}
    {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ) :
    IsPrecedenceFeasible G d fun j => τ (.input j) := by
  intro i j h
  have h1 : τ (.input i) + d i ≤ τ (.output i) := hτ (.job i)
  have h2 : τ (.output i) + 0 ≤ τ (.input j) := hτ (.precedence i j h)
  show τ (.input i) + d i ≤ τ (.input j)
  omega
/-- Finish times agree, network to table, finish part: for a finite acyclic table, the project
finish of the start ticks read off the input events of a feasible event schedule is at most the
sink event time. Acyclicity is needed: a cyclic part of the table that cannot reach the sink
is not bounded by it. -/
theorem projectFinish_input_le_sink {J : Type*} [Fintype J] {G : Digraph J} {d : J → ℕ}
    (hG : G.IsAcyclic) {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ) :
    projectFinish d (fun j => τ (.input j)) ≤ τ .sink := by
  classical
  have hout : ∀ j, τ (.output j) ≤ τ .sink := by
    suffices h : ∀ (n : ℕ) (j : J),
        (Finset.univ.filter (fun k => Relation.TransGen G.Adj j k ∨ k = j)).card ≤ n →
        τ (.output j) ≤ τ .sink from fun j => h _ j le_rfl
    intro n
    induction n with
    | zero =>
        intro j hj
        have hmem : j ∈ Finset.univ.filter (fun k => Relation.TransGen G.Adj j k ∨ k = j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, Or.inr rfl⟩
        have hcard0 : (Finset.univ.filter (fun k => Relation.TransGen G.Adj j k ∨ k = j)).card = 0 := by
          omega
        have h0 : Finset.univ.filter (fun k => Relation.TransGen G.Adj j k ∨ k = j) = ∅ :=
          Finset.card_eq_zero.mp hcard0
        rw [h0] at hmem
        simp at hmem
    | succ n ih =>
        intro j hj
        by_cases hfin : ∀ k, ¬ G.Adj j k
        · have h : τ (.output j) + 0 ≤ τ .sink := hτ (.toSink j hfin)
          omega
        · simp only [not_forall, not_not] at hfin
          obtain ⟨k, hkj⟩ := hfin
          have hsub : Finset.univ.filter (fun x => Relation.TransGen G.Adj k x ∨ x = k) ⊂
              Finset.univ.filter (fun x => Relation.TransGen G.Adj j x ∨ x = j) := by
            rw [Finset.ssubset_iff_subset_ne]
            constructor
            · intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              cases hx with
              | inl h => exact Or.inl (Relation.TransGen.trans (Relation.TransGen.single hkj) h)
              | inr h =>
                  subst h
                  exact Or.inl (Relation.TransGen.single hkj)
            · intro heq
              have hmemR : j ∈ Finset.univ.filter (fun x => Relation.TransGen G.Adj j x ∨ x = j) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ j, Or.inr rfl⟩
              have hmemL : j ∈ Finset.univ.filter (fun x => Relation.TransGen G.Adj k x ∨ x = k) := by
                rw [heq]
                exact hmemR
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmemL
              cases hmemL with
              | inl h => exact hG j (Relation.TransGen.trans (Relation.TransGen.single hkj) h)
              | inr h =>
                  rw [h] at hkj
                  exact hG k (Relation.TransGen.single hkj)
          have hcard := Finset.card_lt_card hsub
          have hlt : (Finset.univ.filter (fun x => Relation.TransGen G.Adj k x ∨ x = k)).card < n + 1 :=
            lt_of_lt_of_le hcard hj
          have hle : (Finset.univ.filter (fun x => Relation.TransGen G.Adj k x ∨ x = k)).card ≤ n := by
            omega
          have ihk := ih k hle
          have hprec : τ (.output j) + 0 ≤ τ (.input k) := hτ (.precedence j k hkj)
          have hjob : τ (.input k) + d k ≤ τ (.output k) := hτ (.job k)
          omega
  show Finset.univ.sup (fun j => τ (.input j) + d j) ≤ τ .sink
  refine Finset.sup_le fun j _ => ?_
  show τ (.input j) + d j ≤ τ .sink
  have hj : τ (.input j) + d j ≤ τ (.output j) := hτ (.job j)
  exact hj.trans (hout j)
/-- Path durations agree, accounting: the duration of any list of split arcs is the total
duration of the jobs of its duration arcs, counted with multiplicity; zero-lag arcs add
nothing. -/
theorem sum_map_splitDuration {J : Type*} {G : Digraph J} (d : J → ℕ)
    (l : List (SplitArc G)) :
    (l.map (splitDuration G d)).sum = ((l.filterMap SplitArc.job?).map d).sum := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      cases e with
      | job j =>
          show d j + (l.map (splitDuration G d)).sum =
            d j + ((l.filterMap SplitArc.job?).map d).sum
          rw [ih]
      | precedence i j h =>
          show 0 + (l.map (splitDuration G d)).sum =
            ((l.filterMap SplitArc.job?).map d).sum
          rw [ih]
          exact zero_add _
      | fromSource j h =>
          show 0 + (l.map (splitDuration G d)).sum =
            ((l.filterMap SplitArc.job?).map d).sum
          rw [ih]
          exact zero_add _
      | toSink j h =>
          show 0 + (l.map (splitDuration G d)).sum =
            ((l.filterMap SplitArc.job?).map d).sum
          rw [ih]
          exact zero_add _
      | sourceSink =>
          show 0 + (l.map (splitDuration G d)).sum =
            ((l.filterMap SplitArc.job?).map d).sum
          rw [ih]
          exact zero_add _
private theorem mem_getLast?_cons_of_mem {α : Type*} {j m : α} {c' : List α}
    (hm : m ∈ c'.getLast?) : m ∈ (j :: c').getLast? := by
  cases c' with
  | nil => simp at hm
  | cons m' rest => simpa using hm
private theorem job?_some {J : Type*} {G : Digraph J} {e : SplitArc G} {j : J}
    (h : SplitArc.job? e = some j) : e = .job j := by
  cases e with
  | job j' =>
    simp [SplitArc.job?] at h
    subst h
    rfl
  | precedence i j' h' => simp [SplitArc.job?] at h
  | fromSource j' h' => simp [SplitArc.job?] at h
  | toSink j' h' => simp [SplitArc.job?] at h
  | sourceSink => simp [SplitArc.job?] at h
private theorem tail_input {J : Type*} {G : Digraph J} {e : SplitArc G} {j : J}
    (h : splitTail G e = .input j) : e = .job j := by
  cases e with
  | job j' =>
    simp [splitTail] at h
    subst h
    rfl
  | precedence i j' h' => simp [splitTail] at h
  | fromSource j' h' => simp [splitTail] at h
  | toSink j' h' => simp [splitTail] at h
  | sourceSink => simp [splitTail] at h
private theorem tail_source {J : Type*} {G : Digraph J} {e : SplitArc G}
    (h : splitTail G e = .source) : (∃ j h', e = .fromSource j h') ∨ e = .sourceSink := by
  cases e with
  | job j' => simp [splitTail] at h
  | precedence i j' h' => simp [splitTail] at h
  | fromSource j' h' => exact Or.inl ⟨j', h', rfl⟩
  | toSink j' h' => simp [splitTail] at h
  | sourceSink => exact Or.inr rfl
private theorem tail_output {J : Type*} {G : Digraph J} {e : SplitArc G} {i : J}
    (h : splitTail G e = .output i) :
    (∃ j h', e = .precedence i j h') ∨ (∃ h', e = .toSink i h') := by
  cases e with
  | job j' => simp [splitTail] at h
  | precedence i' j' h' =>
    simp [splitTail] at h
    subst h
    exact Or.inl ⟨j', h', rfl⟩
  | fromSource j' h' => simp [splitTail] at h
  | toSink i' h' =>
    simp [splitTail] at h
    subst h
    exact Or.inr ⟨h', rfl⟩
  | sourceSink => simp [splitTail] at h
private theorem tail_sink {J : Type*} {G : Digraph J} {e : SplitArc G}
    (h : splitTail G e = .sink) : False := by
  cases e <;> simp [splitTail] at h
private theorem walk_from_sink_nil {J : Type*} {G : Digraph J} {d : SplitEvent J}
    {l : List (SplitArc G)} (h : IsArcWalk (splitTail G) (splitHead G) .sink d l) :
    l = [] := by
  cases l with
  | nil => rfl
  | cons a l' =>
    obtain ⟨-, hhead, -, -⟩ := h
    exact False.elim (tail_sink (hhead a (by simp)))
private theorem walk_input_jobs_nil {J : Type*} {G : Digraph J} {j₀ : J} {d : SplitEvent J}
    {l : List (SplitArc G)} (h : IsArcWalk (splitTail G) (splitHead G) (.input j₀) d l)
    (hempty : l.filterMap SplitArc.job? = []) : l = [] ∧ .input j₀ = d := by
  cases l with
  | nil =>
    obtain ⟨hnil, -, -, -⟩ := h
    exact ⟨rfl, hnil rfl⟩
  | cons a l' =>
    obtain ⟨-, hhead, -, -⟩ := h
    have ha : a = .job j₀ := tail_input (hhead a (by simp))
    subst ha
    rw [List.filterMap_cons_some (f := SplitArc.job?) rfl] at hempty
    simp at hempty
private noncomputable def transGenSucc {J : Type*} [Fintype J] (r : J → J → Prop) (j : J) :
    Finset J := by
  classical
  exact Finset.univ.filter (fun i => Relation.TransGen r j i)
private theorem transGenSucc_card_lt {J : Type*} [Fintype J] {r : J → J → Prop}
    (hirr : ∀ v, ¬ Relation.TransGen r v v) {j k : J} (hjk : r j k) :
    (transGenSucc r k).card < (transGenSucc r j).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    simp only [transGenSucc, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact Relation.TransGen.head hjk hx
  · intro heq
    have hk : k ∈ transGenSucc r j := by
      simp only [transGenSucc, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.TransGen.single hjk
    rw [← heq] at hk
    simp only [transGenSucc, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hirr k hk
private theorem wf_of_card_measure {J : Type*} {r : J → J → Prop}
    (m : J → Finset J) (h : ∀ i j, r i j → (m i).card < (m j).card) :
    WellFounded r := by
  refine Subrelation.wf ?_ (measure (fun j => (m j).card)).wf
  intro a b hab
  exact h a b hab
private theorem wf_conv_of_acyclic {J : Type*} [Finite J] {G : Digraph J} (hG : G.IsAcyclic) :
    WellFounded (fun k j => G.Adj j k) :=
  wf_of_card_measure (@transGenSucc J (Fintype.ofFinite J) G.Adj)
    (fun _ _ hij => @transGenSucc_card_lt J (Fintype.ofFinite J) _ hG _ _ hij)
private theorem walk_source_output {J : Type*} [Finite J] {G : Digraph J} (hG : G.IsAcyclic)
    (j : J) : ∃ l, IsArcWalk (splitTail G) (splitHead G) .source (.output j) l := by
  refine WellFounded.fix
    (C := fun j => ∃ l, IsArcWalk (splitTail G) (splitHead G) .source (.output j) l)
    (Digraph.isAcyclic_iff_wellFounded.mp hG) ?_ j
  intro j IH
  by_cases hstart : ∀ i, ¬ G.Adj i j
  · refine ⟨[.fromSource j hstart, .job j], ?_⟩
    apply walk_cons
    · rfl
    · exact walk_singleton rfl rfl
    · intro b hb
      simp at hb
      subst hb
      rfl
  · have hex : ∃ i, G.Adj i j := by
      by_contra hcon
      exact hstart (fun i hij => hcon ⟨i, hij⟩)
    obtain ⟨i, hij⟩ := hex
    obtain ⟨w, hw⟩ := IH i hij
    refine ⟨(w ++ [.precedence i j hij]) ++ [.job j], ?_⟩
    apply walk_snoc
    · apply walk_snoc
      · exact hw
      · rfl
    · rfl
private theorem walk_output_sink {J : Type*} [Finite J] {G : Digraph J} (hG : G.IsAcyclic)
    (j : J) : ∃ l, IsArcWalk (splitTail G) (splitHead G) (.output j) .sink l := by
  refine WellFounded.fix
    (C := fun j => ∃ l, IsArcWalk (splitTail G) (splitHead G) (.output j) .sink l)
    (wf_conv_of_acyclic hG) ?_ j
  intro j IH
  by_cases hfin : ∀ k, ¬ G.Adj j k
  · exact ⟨[.toSink j hfin], walk_singleton rfl rfl⟩
  · have hex : ∃ k, G.Adj j k := by
      by_contra hcon
      exact hfin (fun k hjk => hcon ⟨k, hjk⟩)
    obtain ⟨k, hjk⟩ := hex
    obtain ⟨w, hw⟩ := IH k hjk
    refine ⟨.precedence j k hjk :: .job k :: w, ?_⟩
    apply walk_cons
    · rfl
    · apply walk_cons
      · rfl
      · exact hw
      · have hhead' := hw.2.1
        exact fun b hb => (hhead' b hb).symm
    · intro b hb
      simp at hb
      subst hb
      rfl
private theorem walk_jobs_aux {J : Type*} {G : Digraph J} :
    ∀ (l : List (SplitArc G)) (o d : SplitEvent J),
      IsArcWalk (splitTail G) (splitHead G) o d l →
      (l.filterMap SplitArc.job?).IsChain G.Adj ∧
      (∀ j₀, o = .input j₀ → ∀ j ∈ (l.filterMap SplitArc.job?).head?, j = j₀) ∧
      (∀ i, o = .output i → ∀ j ∈ (l.filterMap SplitArc.job?).head?, G.Adj i j) ∧
      (o = .source → ∀ j ∈ (l.filterMap SplitArc.job?).head?, ∀ i, ¬ G.Adj i j) ∧
      (d = .sink → ∀ j ∈ (l.filterMap SplitArc.job?).getLast?, ∀ k, ¬ G.Adj j k) ∧
      (o = .source → d = .sink → l.filterMap SplitArc.job? = [] → l = [.sourceSink]) := by
  intro l
  induction l with
  | nil =>
    intro o d hl
    obtain ⟨hnil, -, -, -⟩ := hl
    refine ⟨List.isChain_nil, fun j₀ _ j hj => by simp at hj, fun i _ j hj => by simp at hj,
      fun _ j hj => by simp at hj, fun _ j hj => by simp at hj, fun ho hd _ => ?_⟩
    have hsd : (.source : SplitEvent J) = .sink := ho.symm.trans ((hnil rfl).trans hd)
    simp at hsd
  | cons a l' IH =>
    intro o d hl
    have htl : IsArcWalk (splitTail G) (splitHead G) (splitHead G a) d l' := walk_tail hl
    obtain ⟨hc', hIn', hOut', hSrc', hSnk', hIff'⟩ := IH _ _ htl
    obtain ⟨-, hhead, -, -⟩ := hl
    have htail : splitTail G a = o := hhead a (by simp)
    refine ⟨?chain, ?hin, ?hout, ?hsrc, ?hsnk, ?hiff⟩
    · cases a with
      | job j =>
        rw [List.filterMap_cons_some (f := SplitArc.job?) rfl]
        apply List.isChain_cons.2
        constructor
        · intro m hm
          exact hOut' j rfl m hm
        · exact hc'
      | precedence i j h' =>
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl]
        exact hc'
      | fromSource j h' =>
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl]
        exact hc'
      | toSink j h' =>
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl]
        exact hc'
      | sourceSink =>
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl]
        exact hc'
    · intro j₀ ho j hj
      have ha : a = .job j₀ := tail_input (htail.trans ho)
      subst ha
      rw [List.filterMap_cons_some (f := SplitArc.job?) rfl, List.head?_cons] at hj
      simp at hj
      exact hj.symm
    · intro i ho j hj
      cases tail_output (htail.trans ho) with
      | inl hex =>
        obtain ⟨j', h', rfl⟩ := hex
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl] at hj
        have hjej : j = j' := hIn' j' rfl j hj
        subst hjej
        exact h'
      | inr hex =>
        obtain ⟨h', rfl⟩ := hex
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl] at hj
        have hnil' : l' = [] := walk_from_sink_nil htl
        subst hnil'
        simp at hj
    · intro ho j hj i hij
      cases tail_source (htail.trans ho) with
      | inl hex =>
        obtain ⟨j', h', rfl⟩ := hex
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl] at hj
        have hjej : j = j' := hIn' j' rfl j hj
        subst hjej
        exact (h' i) hij
      | inr hs =>
        subst hs
        rw [List.filterMap_cons_none (f := SplitArc.job?) rfl] at hj
        have hnil' : l' = [] := walk_from_sink_nil htl
        subst hnil'
        simp at hj
    · intro hd j hj k hkj
      by_cases hja : SplitArc.job? a = none
      · rw [List.filterMap_cons_none (f := SplitArc.job?) hja] at hj
        exact hSnk' hd j hj k hkj
      · cases a with
        | job j'' =>
          rw [List.filterMap_cons_some (f := SplitArc.job?) rfl] at hj
          by_cases hempty : l'.filterMap SplitArc.job? = []
          · rw [hempty] at hj
            simp at hj
            subst hj
            cases l' with
            | nil =>
              obtain ⟨hnil, -, -, -⟩ := htl
              have hcon : (.output j'' : SplitEvent J) = .sink := (hnil rfl).trans hd
              simp at hcon
            | cons b l'' =>
              have hhead' := htl.2.1
              have htb : splitTail G b = .output j'' := hhead' b (by simp)
              obtain hbo | hbo := tail_output htb
              · obtain ⟨m', h', hb⟩ := hbo
                rw [hb] at htl hempty
                have hempty'' : l''.filterMap SplitArc.job? = [] := by
                  have htmp := hempty
                  rwa [List.filterMap_cons_none (f := SplitArc.job?) rfl] at htmp
                have htl2 : IsArcWalk (splitTail G) (splitHead G)
                    (splitHead G (.precedence j'' m' h')) d l'' := walk_tail htl
                have hcon := walk_input_jobs_nil htl2 hempty''
                have hcon2 : (.input m' : SplitEvent J) = .sink := hcon.2.trans hd
                simp at hcon2
              · obtain ⟨h', hb⟩ := hbo
                exact (h' k) hkj
          · rw [List.getLast?_cons_of_ne_nil hempty] at hj
            exact hSnk' hd j hj k hkj
        | precedence i' j''' h' => simp [SplitArc.job?] at hja
        | fromSource j''' h' => simp [SplitArc.job?] at hja
        | toSink j''' h' => simp [SplitArc.job?] at hja
        | sourceSink => simp [SplitArc.job?] at hja
    · intro ho hd hempty
      cases tail_source (htail.trans ho) with
      | inl hex =>
        obtain ⟨j', h', rfl⟩ := hex
        have hempty' : l'.filterMap SplitArc.job? = [] := by
          rwa [List.filterMap_cons_none (f := SplitArc.job?) rfl] at hempty
        have hcon := walk_input_jobs_nil htl hempty'
        have hcon2 : (.input j' : SplitEvent J) = .sink := hcon.2.trans hd
        simp at hcon2
      | inr hs =>
        subst hs
        have hnil' : l' = [] := walk_from_sink_nil htl
        subst hnil'
        rfl
private theorem exists_walk_output_of_chain {J : Type*} {G : Digraph J} :
    ∀ (c : List J), c.IsChain G.Adj → (∀ j ∈ c.getLast?, ∀ k, ¬ G.Adj j k) →
      ∀ (i : J), (∀ j ∈ c.head?, G.Adj i j) → (c = [] → ∀ k, ¬ G.Adj i k) →
      ∃ l, IsArcWalk (splitTail G) (splitHead G) (.output i) .sink l ∧
        l.filterMap SplitArc.job? = c := by
  intro c
  induction c with
  | nil =>
    intro _ _ i _ hi
    refine ⟨[.toSink i (hi rfl)], walk_singleton rfl rfl, ?_⟩
    rfl
  | cons j c' IH =>
    intro hc hlast i h hi
    have hij : G.Adj i j := h j (by simp)
    have hc' : c'.IsChain G.Adj := (List.isChain_cons.1 hc).2
    have hpair : ∀ m ∈ c'.head?, G.Adj j m := (List.isChain_cons.1 hc).1
    have hlast' : ∀ m ∈ c'.getLast?, ∀ k, ¬ G.Adj m k :=
      fun m hm k hkm => hlast m (mem_getLast?_cons_of_mem hm) k hkm
    have hi' : c' = [] → ∀ k, ¬ G.Adj j k := by
      intro he
      subst he
      exact hlast j (by simp)
    obtain ⟨l', hl', hfm'⟩ := IH hc' hlast' j hpair hi'
    refine ⟨.precedence i j hij :: .job j :: l', ?_, ?_⟩
    · apply walk_cons
      · rfl
      · apply walk_cons
        · rfl
        · exact hl'
        · obtain ⟨-, hhead', -, -⟩ := hl'
          exact fun b hb => (hhead' b hb).symm
      · intro b hb
        simp at hb
        subst hb
        rfl
    · rw [List.filterMap_cons_none (f := SplitArc.job?) rfl, List.filterMap_cons_some (f := SplitArc.job?) rfl, hfm']
private theorem chain_sum_le_of_head {J : Type*} [Fintype J] {G : Digraph J} {d s : J → ℕ}
    (hs : IsPrecedenceFeasible G d s) :
    ∀ (c : List J), c.IsChain G.Adj → ∀ j ∈ c.head?, s j + (c.map d).sum ≤ projectFinish d s := by
  intro c
  induction c with
  | nil => intro hc j hj; simp at hj
  | cons j' c' IH =>
    intro hc j hj
    simp at hj
    subst hj
    cases c' with
    | nil =>
      have hmem := Finset.le_sup (s := Finset.univ) (f := fun j => s j + d j)
        (Finset.mem_univ j')
      simpa [projectFinish] using hmem
    | cons m rest =>
      have hpair : G.Adj j' m := (List.isChain_cons.1 hc).1 m (by simp)
      have hc' : (m :: rest).IsChain G.Adj := (List.isChain_cons.1 hc).2
      have hstep : s j' + d j' ≤ s m := hs hpair
      have ih : s m + ((m :: rest).map d).sum ≤ projectFinish d s :=
        IH hc' m (by simp)
      have hsum : ((j' :: m :: rest).map d).sum = d j' + ((m :: rest).map d).sum := by simp
      rw [hsum]
      omega
/-- Path durations agree, network to table: the job sequence of every source-to-sink walk of
the split network is a precedence chain of jobs that begins at a start job and ends at a
finish job, and it is empty exactly when the walk is the declared source-to-sink arc. -/
theorem isChain_filterMap_job?_of_isArcWalk {J : Type*} {G : Digraph J}
    {l : List (SplitArc G)} (hl : IsArcWalk (splitTail G) (splitHead G) .source .sink l) :
    (l.filterMap SplitArc.job?).IsChain G.Adj ∧
      (∀ j ∈ (l.filterMap SplitArc.job?).head?, ∀ i, ¬ G.Adj i j) ∧
      (∀ j ∈ (l.filterMap SplitArc.job?).getLast?, ∀ k, ¬ G.Adj j k) ∧
      (l.filterMap SplitArc.job? = [] ↔ l = [.sourceSink]) := by
  obtain ⟨hc, -, -, hs, hf, hi⟩ := walk_jobs_aux l _ _ hl
  refine ⟨hc, hs rfl, hf rfl, ?_⟩
  constructor
  · exact hi rfl rfl
  · intro hl'
    subst hl'
    rfl
/-- Path durations agree, table to network: every precedence chain of jobs that begins at a
start job and ends at a finish job is the job sequence of a source-to-sink walk of the split
network; the empty chain is the job sequence of the declared source-to-sink arc. -/
theorem exists_isArcWalk_filterMap_job?_eq {J : Type*} {G : Digraph J} {c : List J}
    (hc : c.IsChain G.Adj) (hstart : ∀ j ∈ c.head?, ∀ i, ¬ G.Adj i j)
    (hfinish : ∀ j ∈ c.getLast?, ∀ k, ¬ G.Adj j k) :
    ∃ l, IsArcWalk (splitTail G) (splitHead G) .source .sink l ∧
      l.filterMap SplitArc.job? = c := by
  cases c with
  | nil => exact ⟨[.sourceSink], walk_singleton rfl rfl, rfl⟩
  | cons j c' =>
    have hstart' : ∀ i, ¬ G.Adj i j := hstart j (by simp)
    have hc' : c'.IsChain G.Adj := (List.isChain_cons.1 hc).2
    have hpair : ∀ m ∈ c'.head?, G.Adj j m := (List.isChain_cons.1 hc).1
    have hlast' : ∀ m ∈ c'.getLast?, ∀ k, ¬ G.Adj m k :=
      fun m hm k hkm => hfinish m (mem_getLast?_cons_of_mem hm) k hkm
    have hi' : c' = [] → ∀ k, ¬ G.Adj j k := by
      intro he
      subst he
      exact hfinish j (by simp)
    obtain ⟨l', hl', hfm'⟩ := exists_walk_output_of_chain c' hc' hlast' j hpair hi'
    refine ⟨.fromSource j hstart' :: .job j :: l', ?_, ?_⟩
    · apply walk_cons
      · rfl
      · apply walk_cons
        · rfl
        · exact hl'
        · obtain ⟨-, hhead', -, -⟩ := hl'
          exact fun b hb => (hhead' b hb).symm
      · intro b hb
        simp at hb
        subst hb
        rfl
    · rw [List.filterMap_cons_none (f := SplitArc.job?) rfl, List.filterMap_cons_some (f := SplitArc.job?) rfl, hfm']
/-- Critical-path lower bound for the job table, transported from the owner bound
through the split network: under precedence-feasible start ticks, the project finish is at
least the total duration of every precedence chain of jobs, a critical (longest) chain
included. No acyclicity is assumed. -/
theorem sum_map_le_projectFinish {J : Type*} [Fintype J] {G : Digraph J} {d s : J → ℕ}
    (hs : IsPrecedenceFeasible G d s) {c : List J} (hc : c.IsChain G.Adj) :
    (c.map d).sum ≤ projectFinish d s := by
  cases c with
  | nil => simp
  | cons j c' =>
    have h := chain_sum_le_of_head hs (j :: c') hc j (by simp)
    omega
/-- Source/sink reachability of the split network of a finite acyclic table: every event is
reached from the source by a walk and reaches the sink by a walk, so every job lies on a
source-to-sink walk. A finite table with a job unreachable from the source is therefore cyclic,
and it fails this requirement of the owner interface. -/
theorem exists_isArcWalk_source_sink {J : Type*} [Finite J] {G : Digraph J} (hG : G.IsAcyclic)
    (v : SplitEvent J) :
    (∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l) ∧
      ∃ l, IsArcWalk (splitTail G) (splitHead G) v .sink l := by
  cases v with
  | source =>
    constructor
    · exact ⟨[], walk_nil⟩
    · exact ⟨[.sourceSink], walk_singleton rfl rfl⟩
  | sink =>
    constructor
    · exact ⟨[.sourceSink], walk_singleton rfl rfl⟩
    · exact ⟨[], walk_nil⟩
  | input j =>
    constructor
    · by_cases hstart : ∀ i, ¬ G.Adj i j
      · exact ⟨[.fromSource j hstart], walk_singleton rfl rfl⟩
      · have hex : ∃ i, G.Adj i j := by
          by_contra hcon
          exact hstart (fun i hij => hcon ⟨i, hij⟩)
        obtain ⟨i, hij⟩ := hex
        obtain ⟨w, hw⟩ := walk_source_output hG i
        refine ⟨w ++ [.precedence i j hij], ?_⟩
        apply walk_snoc
        · exact hw
        · rfl
    · obtain ⟨w, hw⟩ := walk_output_sink hG j
      refine ⟨.job j :: w, ?_⟩
      apply walk_cons
      · rfl
      · exact hw
      · have hhead' := hw.2.1
        exact fun b hb => (hhead' b hb).symm
  | output j =>
    constructor
    · exact walk_source_output hG j
    · exact walk_output_sink hG j
private theorem walk_singleton_job {J : Type*} {G : Digraph J} {m1 m2 : SplitEvent J} {j : J}
    (hl : IsArcWalk (splitTail G) (splitHead G) m1 m2 [SplitArc.job (G := G) j]) :
    m1 = .input j ∧ m2 = .output j := by
  obtain ⟨h1, h2, h3, h4⟩ := hl
  have hh : splitTail G (SplitArc.job (G := G) j) = m1 :=
    h2 (SplitArc.job (G := G) j) (by simp [List.head?_cons])
  have ht : splitHead G (SplitArc.job (G := G) j) = m2 :=
    h4 (SplitArc.job (G := G) j) (by simp [List.getLast?_singleton])
  exact ⟨hh.symm, ht.symm⟩
private theorem walk_from_input_jobfree_nil {J : Type*} {G : Digraph J} {j : J}
    {d : SplitEvent J} {l : List (SplitArc G)}
    (hl : IsArcWalk (splitTail G) (splitHead G) (.input j) d l)
    (hfree : ∀ a ∈ l, a.job? = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons a rest =>
      obtain ⟨htail, _⟩ := walk_cons_pair hl
      cases a with
      | job j' =>
          have hnone := hfree _ List.mem_cons_self
          simp [SplitArc.job?] at hnone
      | precedence i j' h =>
          simp [splitTail] at htail
      | fromSource j' h =>
          simp [splitTail] at htail
      | toSink j' h =>
          simp [splitTail] at htail
      | sourceSink =>
          simp [splitTail] at htail
private theorem walk_from_sink_nil_ga2 {J : Type*} {G : Digraph J}
    {d : SplitEvent J} {l : List (SplitArc G)}
    (hl : IsArcWalk (splitTail G) (splitHead G) .sink d l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a rest =>
      obtain ⟨htail, _⟩ := walk_cons_pair hl
      cases a with
      | job j' => simp [splitTail] at htail
      | precedence i j' h => simp [splitTail] at htail
      | fromSource j' h => simp [splitTail] at htail
      | toSink j' h => simp [splitTail] at htail
      | sourceSink => simp [splitTail] at htail
private theorem adj_of_walk_output_input {J : Type*} {G : Digraph J} {i j : J}
    {l : List (SplitArc G)}
    (hl : IsArcWalk (splitTail G) (splitHead G) (.output i) (.input j) l)
    (hfree : ∀ a ∈ l, a.job? = none) (hne : l ≠ []) : G.Adj i j := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a rest =>
      obtain ⟨htail, hrest⟩ := walk_cons_pair hl
      have hfree' : ∀ a ∈ rest, a.job? = none :=
        fun a ha => hfree a (List.mem_cons.mpr (Or.inr ha))
      cases a with
      | job j' =>
          have hnone := hfree _ List.mem_cons_self
          simp [SplitArc.job?] at hnone
      | precedence i' j' h =>
          have hi : i' = i := by simpa [splitTail] using htail
          have hnil : rest = [] := walk_from_input_jobfree_nil hrest hfree'
          subst hnil
          obtain ⟨_, _, _, h4⟩ := hl
          have hj : splitHead G (SplitArc.precedence (G := G) i' j' h) = .input j :=
            h4 _ (by simp [List.getLast?_singleton])
          have hj' : j' = j := by simpa [splitHead] using hj
          cases hi
          cases hj'
          exact h
      | fromSource j' h =>
          simp [splitTail] at htail
      | toSink j' h =>
          have hrest' : IsArcWalk (splitTail G) (splitHead G) .sink (.input j) rest := hrest
          have hnil : rest = [] := walk_from_sink_nil_ga2 hrest'
          subst hnil
          obtain ⟨_, _, _, h4⟩ := hl
          have hs : splitHead G (SplitArc.toSink (G := G) j' h) = .input j :=
            h4 _ (by simp [List.getLast?_singleton])
          simp [splitHead] at hs
      | sourceSink =>
          simp [splitTail] at htail
private theorem closed_jobfree_nil {J : Type*} {G : Digraph J} {v : SplitEvent J}
    {l : List (SplitArc G)} (hl : IsArcWalk (splitTail G) (splitHead G) v v l)
    (hfree : ∀ a ∈ l, a.job? = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons a rest =>
      obtain ⟨htail, hrest⟩ := walk_cons_pair hl
      have hfree' : ∀ a ∈ rest, a.job? = none :=
        fun a ha => hfree a (List.mem_cons.mpr (Or.inr ha))
      cases a with
      | job j' =>
          have hnone := hfree _ List.mem_cons_self
          simp [SplitArc.job?] at hnone
      | precedence i' j' h =>
          have hnil : rest = [] := walk_from_input_jobfree_nil hrest hfree'
          subst hnil
          obtain ⟨_, _, _, h4⟩ := hl
          have hhead : splitHead G (SplitArc.precedence (G := G) i' j' h) = v :=
            h4 _ (by simp [List.getLast?_singleton])
          have hcontra : SplitEvent.output i' = SplitEvent.input j' :=
            htail.trans hhead.symm
          cases hcontra
      | fromSource j' h =>
          have hnil : rest = [] := walk_from_input_jobfree_nil hrest hfree'
          subst hnil
          obtain ⟨_, _, _, h4⟩ := hl
          have hhead : splitHead G (SplitArc.fromSource (G := G) j' h) = v :=
            h4 _ (by simp [List.getLast?_singleton])
          have hcontra : SplitEvent.source = SplitEvent.input j' :=
            htail.trans hhead.symm
          cases hcontra
      | toSink j' h =>
          have hrest' : IsArcWalk (splitTail G) (splitHead G) .sink v rest := hrest
          have hnil : rest = [] := walk_from_sink_nil_ga2 hrest'
          subst hnil
          obtain ⟨_, _, _, h4⟩ := hl
          have hhead : splitHead G (SplitArc.toSink (G := G) j' h) = v :=
            h4 _ (by simp [List.getLast?_singleton])
          have hcontra : SplitEvent.output j' = SplitEvent.sink :=
            htail.trans hhead.symm
          cases hcontra
      | sourceSink =>
          have hrest' : IsArcWalk (splitTail G) (splitHead G) .sink v rest := hrest
          have hnil : rest = [] := walk_from_sink_nil_ga2 hrest'
          subst hnil
          obtain ⟨_, _, _, h4⟩ := hl
          have hhead : splitHead G (SplitArc.sourceSink (G := G)) = v :=
            h4 _ (by simp [List.getLast?_singleton])
          have hcontra : SplitEvent.source = SplitEvent.sink :=
            htail.trans hhead.symm
          cases hcontra
private theorem split_first_job_cons {J : Type*} {G : Digraph J} {a : SplitArc G}
    {rest : List (SplitArc G)} (hfree_a : a.job? = none)
    (ih : (∃ j, SplitArc.job (G := G) j ∈ rest) →
      ∃ pre j post, rest = pre ++ [SplitArc.job (G := G) j] ++ post ∧
        ∀ x ∈ pre, x.job? = none)
    (hex : ∃ j, SplitArc.job (G := G) j ∈ a :: rest) :
    ∃ pre j post, (a :: rest) = pre ++ [SplitArc.job (G := G) j] ++ post ∧
      ∀ x ∈ pre, x.job? = none := by
  obtain ⟨j', hj'⟩ := hex
  have hmem : SplitArc.job (G := G) j' ∈ rest := by
    cases List.mem_cons.mp hj' with
    | inl heq =>
        cases heq
        simp [SplitArc.job?] at hfree_a
    | inr hmem => exact hmem
  obtain ⟨pre, j'', post, hsplit, hfree⟩ := ih ⟨j', hmem⟩
  refine ⟨a :: pre, j'', post, by simp [hsplit], ?_⟩
  intro x hx
  cases List.mem_cons.mp hx with
  | inl heq =>
      cases heq
      exact hfree_a
  | inr hmem => exact hfree x hmem
private theorem split_first_job {J : Type*} {G : Digraph J} {l : List (SplitArc G)}
    (hex : ∃ j, SplitArc.job (G := G) j ∈ l) :
    ∃ pre j post, l = pre ++ [SplitArc.job (G := G) j] ++ post ∧
      ∀ x ∈ pre, x.job? = none := by
  revert hex
  induction l with
  | nil =>
      intro hex
      obtain ⟨j, hj⟩ := hex
      simp at hj
  | cons a rest ih =>
      intro hex
      cases a with
      | job j => exact ⟨[], j, rest, by simp, by simp⟩
      | precedence i j h => exact split_first_job_cons rfl ih hex
      | fromSource j h => exact split_first_job_cons rfl ih hex
      | toSink j h => exact split_first_job_cons rfl ih hex
      | sourceSink => exact split_first_job_cons rfl ih hex
private theorem split_last_job_cons {J : Type*} {G : Digraph J} {a : SplitArc G}
    {rest : List (SplitArc G)}
    (ih : (∃ j, SplitArc.job (G := G) j ∈ rest) →
      ∃ pre j post, rest = pre ++ [SplitArc.job (G := G) j] ++ post ∧
        ∀ x ∈ post, x.job? = none)
    (hex : ∃ j, SplitArc.job (G := G) j ∈ a :: rest)
    (ha : ∀ j, a ≠ SplitArc.job (G := G) j) :
    ∃ pre j post, (a :: rest) = pre ++ [SplitArc.job (G := G) j] ++ post ∧
      ∀ x ∈ post, x.job? = none := by
  obtain ⟨j', hj'⟩ := hex
  have hmem : SplitArc.job (G := G) j' ∈ rest := by
    cases List.mem_cons.mp hj' with
    | inl heq => exact absurd heq.symm (ha j')
    | inr hmem => exact hmem
  obtain ⟨pre, j'', post, hsplit, hfree⟩ := ih ⟨j', hmem⟩
  exact ⟨a :: pre, j'', post, by simp [hsplit], hfree⟩
private theorem split_last_job {J : Type*} {G : Digraph J} {l : List (SplitArc G)}
    (hex : ∃ j, SplitArc.job (G := G) j ∈ l) :
    ∃ pre j post, l = pre ++ [SplitArc.job (G := G) j] ++ post ∧
      ∀ x ∈ post, x.job? = none := by
  revert hex
  induction l with
  | nil =>
      intro hex
      obtain ⟨j, hj⟩ := hex
      simp at hj
  | cons a rest ih =>
      intro hex
      cases a with
      | job j =>
          obtain h | h := Classical.em (∃ j, SplitArc.job (G := G) j ∈ rest)
          · obtain ⟨pre, j', post, hsplit, hfree⟩ := ih h
            exact ⟨SplitArc.job (G := G) j :: pre, j', post, by simp [hsplit], hfree⟩
          · have hfree_rest : ∀ x ∈ rest, x.job? = none := by
              intro x hx
              cases x with
              | job j' => exact absurd ⟨j', hx⟩ h
              | precedence _ _ _ => rfl
              | fromSource _ _ => rfl
              | toSink _ _ => rfl
              | sourceSink => rfl
            exact ⟨[], j, rest, by simp, hfree_rest⟩
      | precedence i j h =>
          exact split_last_job_cons ih hex (fun j' heq => by cases heq)
      | fromSource j h =>
          exact split_last_job_cons ih hex (fun j' heq => by cases heq)
      | toSink j h =>
          exact split_last_job_cons ih hex (fun j' heq => by cases heq)
      | sourceSink =>
          exact split_last_job_cons ih hex (fun j' heq => by cases heq)
private theorem transGen_of_chain_append {J : Type*} {G : Digraph J} {b : J}
    {c : List J} {a : J} (hc : (a :: (c ++ [b])).IsChain G.Adj) :
    Relation.TransGen G.Adj a b := by
  induction c generalizing a with
  | nil =>
      rw [List.nil_append] at hc
      obtain ⟨hedge, _⟩ := List.isChain_cons_cons.mp hc
      exact Relation.TransGen.single hedge
  | cons d e ih =>
      rw [List.cons_append] at hc
      obtain ⟨had, hchain⟩ := List.isChain_cons_cons.mp hc
      exact (Relation.TransGen.single had).trans (ih hchain)
private theorem isChain_jobs {J : Type*} {G : Digraph J} {o d : SplitEvent J}
    {l : List (SplitArc G)} (hl : IsArcWalk (splitTail G) (splitHead G) o d l) :
    (l.filterMap SplitArc.job?).IsChain G.Adj := by
  induction l generalizing o with
  | nil => exact List.isChain_nil
  | cons a rest ih =>
      obtain ⟨htail, hrest⟩ := walk_cons_pair hl
      have ih' : (rest.filterMap SplitArc.job?).IsChain G.Adj := ih hrest
      cases a with
      | job j =>
          have hfm : (SplitArc.job (G := G) j :: rest).filterMap SplitArc.job? =
              j :: rest.filterMap SplitArc.job? := by
            simp [SplitArc.job?]
          rw [hfm]
          cases hfr : rest.filterMap SplitArc.job? with
          | nil => exact List.isChain_singleton j
          | cons j' rest' =>
              have hchain : (j' :: rest').IsChain G.Adj := by rw [← hfr]; exact ih'
              have hmem : j' ∈ rest.filterMap SplitArc.job? := by
                rw [hfr]
                exact List.mem_cons_self
              obtain ⟨a', ha'mem, ha'job⟩ := List.mem_filterMap.mp hmem
              have ha'eq : a' = SplitArc.job (G := G) j' := by
                cases a' with
                | job j'' =>
                    have hjj : j'' = j' := by simpa [SplitArc.job?] using ha'job
                    cases hjj
                    rfl
                | precedence _ _ _ => simp [SplitArc.job?] at ha'job
                | fromSource _ _ => simp [SplitArc.job?] at ha'job
                | toSink _ _ => simp [SplitArc.job?] at ha'job
                | sourceSink => simp [SplitArc.job?] at ha'job
              have hjobmem : SplitArc.job (G := G) j' ∈ rest := by
                rw [← ha'eq]
                exact ha'mem
              obtain ⟨pre, jf, post, hsplit, hfree⟩ := split_first_job ⟨j', hjobmem⟩
              have hfmpre : pre.filterMap SplitArc.job? = [] :=
                List.filterMap_eq_nil_iff.mpr hfree
              have hfmrest : rest.filterMap SplitArc.job? =
                  jf :: post.filterMap SplitArc.job? := by
                simp [hsplit, List.filterMap_append, hfmpre, SplitArc.job?]
              rw [hsplit, List.append_assoc] at hrest
              obtain ⟨m1, hpre, hmid⟩ := walk_append hrest
              obtain ⟨m2, hsing, hpost⟩ := walk_append hmid
              obtain ⟨hm1, hm2⟩ := walk_singleton_job hsing
              subst hm1
              subst hm2
              have hprene : pre ≠ [] := by
                intro hnil
                subst hnil
                obtain ⟨hpe, _, _, _⟩ := hpre
                have hcontra : SplitEvent.output j = SplitEvent.input jf := hpe rfl
                cases hcontra
              have hedge : G.Adj j jf := adj_of_walk_output_input hpre hfree hprene
              rw [hfr] at hfmrest
              cases hfmrest
              exact List.isChain_cons_cons.mpr ⟨hedge, hchain⟩
      | precedence i j h =>
          have hfm : (SplitArc.precedence (G := G) i j h :: rest).filterMap
              SplitArc.job? = rest.filterMap SplitArc.job? := by
            simp [List.filterMap_cons, SplitArc.job?]
          rw [hfm]
          exact ih'
      | fromSource j h =>
          have hfm : (SplitArc.fromSource (G := G) j h :: rest).filterMap
              SplitArc.job? = rest.filterMap SplitArc.job? := by
            simp [List.filterMap_cons, SplitArc.job?]
          rw [hfm]
          exact ih'
      | toSink j h =>
          have hfm : (SplitArc.toSink (G := G) j h :: rest).filterMap
              SplitArc.job? = rest.filterMap SplitArc.job? := by
            simp [List.filterMap_cons, SplitArc.job?]
          rw [hfm]
          exact ih'
      | sourceSink =>
          have hfm : (SplitArc.sourceSink (G := G) :: rest).filterMap
              SplitArc.job? = rest.filterMap SplitArc.job? := by
            simp [List.filterMap_cons, SplitArc.job?]
          rw [hfm]
          exact ih'
private theorem jobfree_of_no_job {J : Type*} {G : Digraph J} {l : List (SplitArc G)}
    (h : ¬ ∃ j, SplitArc.job (G := G) j ∈ l) : ∀ a ∈ l, a.job? = none := by
  intro a ha
  cases a with
  | job j => exact absurd ⟨j, ha⟩ h
  | precedence _ _ _ => rfl
  | fromSource _ _ => rfl
  | toSink _ _ => rfl
  | sourceSink => rfl
private theorem wrap_edge {J : Type*} {G : Digraph J} {pre post : List (SplitArc G)}
    {jA jB : J} {v : SplitEvent J}
    (hpost : IsArcWalk (splitTail G) (splitHead G) (.output jA) v post)
    (hpre : IsArcWalk (splitTail G) (splitHead G) v (.input jB) pre)
    (hfree_post : ∀ a ∈ post, a.job? = none)
    (hfree_pre : ∀ a ∈ pre, a.job? = none) : G.Adj jA jB := by
  have hseg := walk_append_mk hpost hpre
  have hfree : ∀ a ∈ post ++ pre, a.job? = none := by
    intro a ha
    cases List.mem_append.mp ha with
    | inl h => exact hfree_post a h
    | inr h => exact hfree_pre a h
  have hne : post ++ pre ≠ [] := by
    intro hnil
    rw [List.append_eq_nil_iff] at hnil
    obtain ⟨hpost_nil, hpre_nil⟩ := hnil
    obtain ⟨hpe, _, _, _⟩ := hpost
    obtain ⟨hpre_e, _, _, _⟩ := hpre
    have h1 : SplitEvent.output jA = v := hpe hpost_nil
    have h2 : v = SplitEvent.input jB := hpre_e hpre_nil
    have hcontra : SplitEvent.output jA = SplitEvent.input jB := h1.trans h2
    cases hcontra
  exact adj_of_walk_output_input hseg hfree hne
/-- The split network of an acyclic table has no nonempty closed walk: such a walk would run
through a cycle of precedences. This is the closed-walk premise of
`exists_isFeasibleSchedule_eq_sum` for the split network; no finiteness is needed. -/
theorem eq_nil_of_isArcWalk_split_self {J : Type*} {G : Digraph J} (hG : G.IsAcyclic) :
    ∀ v (l : List (SplitArc G)), IsArcWalk (splitTail G) (splitHead G) v v l → l = [] := by
  intro v l hl
  by_contra hne
  have hasJob : ∃ j, SplitArc.job (G := G) j ∈ l := by
    by_contra hnoj
    exact hne (closed_jobfree_nil hl (jobfree_of_no_job hnoj))
  obtain ⟨pre₁, j₁, post₁, hsplit₁, hfree₁⟩ := split_first_job hasJob
  rw [hsplit₁, List.append_assoc] at hl
  obtain ⟨m1, hpre₁, hmid₁⟩ := walk_append hl
  obtain ⟨m2, hsing₁, hpost₁⟩ := walk_append hmid₁
  obtain ⟨hm1, hm2⟩ := walk_singleton_job hsing₁
  subst hm1
  subst hm2
  obtain hpost_job | hpost_nojob := Classical.em (∃ j, SplitArc.job (G := G) j ∈ post₁)
  · obtain ⟨pre₂, j_k, post₂, hsplit₂, hfree₂⟩ := split_last_job hpost_job
    rw [hsplit₂, List.append_assoc] at hpost₁
    obtain ⟨m3, hpre₂, hmid₂⟩ := walk_append hpost₁
    obtain ⟨m4, hsing₂, hpost₂⟩ := walk_append hmid₂
    obtain ⟨hm3, hm4⟩ := walk_singleton_job hsing₂
    subst hm3
    subst hm4
    have hfm1 : pre₁.filterMap SplitArc.job? = [] :=
      List.filterMap_eq_nil_iff.mpr hfree₁
    have hfm2 : post₂.filterMap SplitArc.job? = [] :=
      List.filterMap_eq_nil_iff.mpr hfree₂
    have hchain := isChain_jobs hl
    rw [hsplit₂] at hchain
    have hjobs : (pre₁ ++ ([SplitArc.job (G := G) j₁] ++
          ((pre₂ ++ [SplitArc.job (G := G) j_k]) ++ post₂))).filterMap SplitArc.job? =
        j₁ :: (pre₂.filterMap SplitArc.job? ++ [j_k]) := by
      simp [List.filterMap_append, hfm1, hfm2, SplitArc.job?]
    rw [hjobs] at hchain
    have htrans : Relation.TransGen G.Adj j₁ j_k := transGen_of_chain_append hchain
    have hedge : G.Adj j_k j₁ := wrap_edge hpost₂ hpre₁ hfree₂ hfree₁
    exact hG j₁ (htrans.trans (Relation.TransGen.single hedge))
  · have hfreePost := jobfree_of_no_job hpost_nojob
    have hedge : G.Adj j₁ j₁ := wrap_edge hpost₁ hpre₁ hfreePost hfree₁
    exact hG j₁ (Relation.TransGen.single hedge)
/-- The split network of a finite table has finitely many arcs: one duration arc per job, at most
one precedence arc per ordered pair of jobs, at most one source arc and one sink arc per job, and
the declared arc. This is the finiteness premise of `exists_isFeasibleSchedule_eq_sum` for the
split network. -/
instance finite_splitArc {J : Type*} [Finite J] (G : Digraph J) : Finite (SplitArc G) := by
  letI := Classical.propDecidable
  letI : DecidableEq (SplitArc G) := fun a b => Classical.propDecidable (a = b)
  have hJ : Fintype J := Fintype.ofFinite J
  refine @Finite.of_fintype _ ⟨?_, ?_⟩
  · exact (@Finset.univ J hJ).image SplitArc.job ∪
      ((@Finset.univ J hJ).biUnion fun i =>
        (((@Finset.univ J hJ).filter (fun j => G.Adj i j)).attach.image
          (fun x : { x : J // x ∈ (@Finset.univ J hJ).filter (fun j => G.Adj i j) } =>
            SplitArc.precedence i x.1 (Finset.mem_filter.mp x.2).2))) ∪
      (((@Finset.univ J hJ).filter (fun j => ∀ i, ¬ G.Adj i j)).attach.image
        (fun x : { x : J // x ∈ (@Finset.univ J hJ).filter (fun j => ∀ i, ¬ G.Adj i j) } =>
          SplitArc.fromSource x.1 (Finset.mem_filter.mp x.2).2)) ∪
      (((@Finset.univ J hJ).filter (fun j => ∀ k, ¬ G.Adj j k)).attach.image
        (fun x : { x : J // x ∈ (@Finset.univ J hJ).filter (fun j => ∀ k, ¬ G.Adj j k) } =>
          SplitArc.toSink x.1 (Finset.mem_filter.mp x.2).2)) ∪
      {SplitArc.sourceSink}
  · intro a
    cases a with
    | job j =>
      simp only [Finset.mem_union]
      refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
      exact Finset.mem_image.mpr ⟨j, @Finset.mem_univ J hJ j, rfl⟩
    | precedence i j h =>
      simp only [Finset.mem_union]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      refine Finset.mem_biUnion.mpr ⟨i, @Finset.mem_univ J hJ i, ?_⟩
      refine Finset.mem_image.mpr ⟨⟨j, ?_⟩, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_filter.mpr ⟨@Finset.mem_univ J hJ j, h⟩
    | fromSource j h =>
      simp only [Finset.mem_union]
      refine Or.inl (Or.inl (Or.inr ?_))
      refine Finset.mem_image.mpr ⟨⟨j, ?_⟩, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_filter.mpr ⟨@Finset.mem_univ J hJ j, h⟩
    | toSink j h =>
      simp only [Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      refine Finset.mem_image.mpr ⟨⟨j, ?_⟩, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_filter.mpr ⟨@Finset.mem_univ J hJ j, h⟩
    | sourceSink =>
      simp only [Finset.mem_union]
      refine Or.inr ?_
      exact Finset.mem_singleton.mpr rfl

end Cslib.Scheduling.ProjectNetwork
