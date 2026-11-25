/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Multiparty.LTS

/-!
# Multiparty session types: finite synchronous process typing

Finite, synchronous, single-session, participant-addressed specialization
of the process typing of Honda, Yoshida and Carbone, *Multiparty
Asynchronous Session Types*, JACM 63(1), 2016: the process grammar of
Fig. 1 restricted to one sequential thread per participant; the
program-phrase typing rules [INACT], [SEND], [RCV], [SEL] and [BRANCH] of
Fig. 7 (§4.4), where each participant's process carries a singleton typing
`s̃ : T@p` (Notation 4.5) given by one local type; typing of a network by
the projections of a well-formed global type (Definition 5.8, specialized
to a total participant map; Proposition 5.5 makes the queue-free typing the
right one); the free-variable property (Lemma 5.15, value variables); and
value substitution (Lemma 5.18 (1)). HYC does not state value-context
weakening; it is a standard structural lemma, included here as such.
[Yoshida and Vasconcelos 2007] is cited only as HYC's reference for the
proof of Lemma 5.18. This is a project specialization, not a verbatim
source statement.

Dropped, each a nonclaim: session initiation ([MCAST], [MACC]), name
restriction and shared-name sorts ([NRES]), delegation ([DELEG], [SREC]),
recursion ([VAR], [DEF]), conditionals and Boolean expressions ([IF]),
queues and every runtime typing rule (including [CRES] and subsumption
[SUBS]), parallel threads inside one participant ([CONC]; processes of
different participants are composed only by the fixed participant map
`Net`), decidability of typing (Proposition 4.6), weakening by end-typed
channels (Lemma 5.18 (2); there is no channel environment to weaken in
the singleton typing used here), and structural congruence (Fig. 2) with
subject congruence (Theorem 5.19 (1)); no congruence relation is defined.

Project-specific, not from the source: value variables are de Bruijn
indices (mirroring the π-calculus convention in `PiCalculus.Basic`); every
value has one sort (`sortOf`), so synchronous step labels are determined;
a network is total on participants and a non-participant projects to `end`,
so typing forces it to run `inact` (`Net.TypedBy.inact_of_not_mem`); and
typing is closed under `LocalType.braceEq` (`HasType` is ordered typing
`HasType0` up to brace equality), because the finite LTS preserves
bystander projections only up to brace equality. Projection uses plain
merging (see `Multiparty.Projection`).

Naming: the binary `SessionTypes.Basic` already declares
`Cslib.SessionTypes.HasType`, `Cslib.SessionTypes.HasType.subst` and
`Cslib.SessionTypes.HasType.closedAt`, which become ambiguous with this
file's names if both namespaces are opened. Refer to this file's judgement
as `Multiparty.HasType`, and do not open `Cslib.SessionTypes` and
`Cslib.SessionTypes.Multiparty` together.

The synchronous network step `Net.Step` is defined here for the subject
reduction and session fidelity unit; this file proves nothing about it.
No subject reduction, session fidelity, communication safety or progress is
stated here.
-/
@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

/-! ### Supplier-type lemmas (new; no edit to `Projection` or `LTS`) -/

/-- Erasing one label does not change lookup of a different label. -/
private theorem LocalType.Branches.lookup_eraseLabel_of_ne {P S L : Type} [DecidableEq L]
    {label label' : L} (hne : label' ≠ label) :
    ∀ branches : LocalType.Branches P S L,
      (branches.eraseLabel label).lookup label' = branches.lookup label'
  | .nil => rfl
  | .cons entryLabel head tail => by
    by_cases h : label = entryLabel
    · subst h
      simp [LocalType.Branches.eraseLabel, LocalType.Branches.lookup, hne]
    · have ih := LocalType.Branches.lookup_eraseLabel_of_ne hne tail
      simp only [LocalType.Branches.eraseLabel, h, ite_false,
        LocalType.Branches.lookup]
      split <;> simp_all

/-- (T4) Brace-equal branch lists agree on lookup up to brace equality.
No well-formedness premise is needed for this direction. -/
theorem LocalType.Branches.braceEq_lookup {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {label : L} {t : LocalType P S L} :
    ∀ {branches branches' : LocalType.Branches P S L},
      branches.braceEq branches' = true → branches.lookup label = some t →
        ∃ t', branches'.lookup label = some t' ∧ t.braceEq t' = true
  | .nil, _, _, h => by cases h
  | .cons entryLabel head tail, branches', hbeq, hlook => by
    simp only [LocalType.Branches.braceEq] at hbeq
    split at hbeq
    · rename_i head' hhead'
      simp only [Bool.and_eq_true] at hbeq
      by_cases h : label = entryLabel
      · subst h
        simp only [LocalType.Branches.lookup, ite_true, Option.some.injEq] at hlook
        subst hlook
        exact ⟨head', hhead', hbeq.1⟩
      · simp only [LocalType.Branches.lookup, h, ite_false] at hlook
        obtain ⟨t', ht', htt'⟩ := LocalType.Branches.braceEq_lookup hbeq.2 hlook
        refine ⟨t', ?_, htt'⟩
        rw [← LocalType.Branches.lookup_eraseLabel_of_ne h branches']
        exact ht'
    · cases hbeq

/-- Label membership is definedness of lookup. -/
private theorem LocalType.Branches.mem_labels_iff_lookup_isSome {P S L : Type} [DecidableEq L]
    {label : L} : ∀ branches : LocalType.Branches P S L,
      label ∈ branches.labels ↔ (branches.lookup label).isSome
  | .nil => by simp [LocalType.Branches.labels, LocalType.Branches.entries,
      LocalType.Branches.lookup]
  | .cons entryLabel head tail => by
    have ih := LocalType.Branches.mem_labels_iff_lookup_isSome (label := label) tail
    by_cases h : label = entryLabel
    · subst h
      simp [LocalType.Branches.labels, LocalType.Branches.entries,
        LocalType.Branches.lookup]
    · simp only [LocalType.Branches.labels] at ih
      simp [LocalType.Branches.labels, LocalType.Branches.entries,
        LocalType.Branches.lookup, h, ih]

/-- (T4, labels) Brace-equal branch lists have the same label sets. -/
theorem LocalType.Branches.braceEq_mem_labels {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {branches branches' : LocalType.Branches P S L}
    (h : branches.braceEq branches' = true) (label : L) :
    label ∈ branches.labels ↔ label ∈ branches'.labels := by
  have key : ∀ {bs bs' : LocalType.Branches P S L}, bs.braceEq bs' = true →
      label ∈ bs.labels → label ∈ bs'.labels := by
    intro bs bs' hb hl
    rw [LocalType.Branches.mem_labels_iff_lookup_isSome] at hl ⊢
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨t', ht', -⟩ := LocalType.Branches.braceEq_lookup hb ht
    simp [ht']
  exact ⟨key h, key (LocalType.Branches.braceEq_symm h)⟩

/-- (T4b) On a well-formed branch list, entry membership determines lookup. -/
theorem LocalType.Branches.lookup_of_mem_entries {P S L : Type} [DecidableEq L]
    {label : L} {t : LocalType P S L} : ∀ {branches : LocalType.Branches P S L},
      branches.WellFormed → (label, t) ∈ branches.entries →
        branches.lookup label = some t
  | .nil, _, hm => by simp [LocalType.Branches.entries] at hm
  | .cons entryLabel head tail, hwf, hm => by
    cases hwf with
    | cons hnot _ htail =>
      simp only [LocalType.Branches.entries, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · simp [LocalType.Branches.lookup]
      · have hne : label ≠ entryLabel := by
          rintro rfl
          exact hnot (by
            simpa [LocalType.Branches.labels] using
              List.mem_map_of_mem (f := Prod.fst) hm)
        rw [LocalType.Branches.lookup, ite_eq_right hne]
        exact LocalType.Branches.lookup_of_mem_entries htail hm

namespace Multiparty

/-! ### Syntax -/

/-- Expressions: a de Bruijn value variable or a closed value. -/
inductive Expr (V : Type) where
  | var (index : Nat) : Expr V
  | val (value : V) : Expr V
deriving DecidableEq

mutual
/-- Finite sequential process of one participant, addressed by peer:
inaction, send an expression, receive a value (binding variable `0` in the
continuation), select a label, or branch on labelled continuations. -/
inductive Proc (P V L : Type) where
  | inact : Proc P V L
  | send (peer : P) (payload : Expr V) (next : Proc P V L) : Proc P V L
  | recv (peer : P) (next : Proc P V L) : Proc P V L
  | select (peer : P) (label : L) (next : Proc P V L) : Proc P V L
  | branch (peer : P) (branches : Proc.Branches P V L) : Proc P V L
deriving DecidableEq

/-- Ordered association list of labelled process continuations. -/
inductive Proc.Branches (P V L : Type) where
  | nil : Proc.Branches P V L
  | cons (label : L) (head : Proc P V L) (tail : Proc.Branches P V L) :
    Proc.Branches P V L
deriving DecidableEq
end

/-- Association-list entries of a process branch list, in order. -/
def Proc.Branches.entries {P V L : Type} (branches : Proc.Branches P V L) :
    List (L × Proc P V L) :=
  match branches with
  | .nil => ([] : List (L × Proc P V L))
  | .cons label head tail => (label, head) :: tail.entries

/-- Labels of a process branch list, in order. -/
def Proc.Branches.labels {P V L : Type} (branches : Proc.Branches P V L) : List L :=
  branches.entries.map Prod.fst

/-- First match on the raw ordered list, or `none` if absent. -/
def Proc.Branches.lookup {P V L : Type} [DecidableEq L]
    (branches : Proc.Branches P V L) (label : L) : Option (Proc P V L) :=
  match branches with
  | .nil => (none : Option (Proc P V L))
  | .cons entryLabel head tail =>
    if label = entryLabel then some head else tail.lookup label

/-! ### de Bruijn lifting and substitution of closed values -/

/-- Shift every variable at or above the cutoff up by one. -/
def Expr.lift {V : Type} (cutoff : Nat) : Expr V → Expr V
  | .var index => if cutoff ≤ index then .var (index + 1) else .var index
  | .val value => .val value

mutual
/-- Shift free variables at or above the cutoff; `recv` raises the cutoff. -/
def Proc.lift {P V L : Type} (cutoff : Nat) : Proc P V L → Proc P V L
  | .inact => .inact
  | .send peer payload next => .send peer (payload.lift cutoff) (next.lift cutoff)
  | .recv peer next => .recv peer (next.lift (cutoff + 1))
  | .select peer label next => .select peer label (next.lift cutoff)
  | .branch peer branches => .branch peer (branches.lift cutoff)

/-- Lift every continuation of a branch list. -/
def Proc.Branches.lift {P V L : Type} (cutoff : Nat) :
    Proc.Branches P V L → Proc.Branches P V L
  | .nil => .nil
  | .cons label head tail => .cons label (head.lift cutoff) (tail.lift cutoff)
end

/-- Replace variable `index` by a closed value and close the gap above it. -/
def Expr.subst {V : Type} (value : V) (index : Nat) : Expr V → Expr V
  | .var i => if i = index then .val value else if index < i then .var (i - 1) else .var i
  | .val w => .val w

mutual
/-- Substitute a closed value for a variable; `recv` raises the index.
The value is closed, so no lifting of the value and no capture case. -/
def Proc.subst {P V L : Type} (value : V) (index : Nat) : Proc P V L → Proc P V L
  | .inact => .inact
  | .send peer payload next =>
    .send peer (payload.subst value index) (next.subst value index)
  | .recv peer next => .recv peer (next.subst value (index + 1))
  | .select peer label next => .select peer label (next.subst value index)
  | .branch peer branches => .branch peer (branches.subst value index)

/-- Substitute in every continuation of a branch list. -/
def Proc.Branches.subst {P V L : Type} (value : V) (index : Nat) :
    Proc.Branches P V L → Proc.Branches P V L
  | .nil => .nil
  | .cons label head tail => .cons label (head.subst value index) (tail.subst value index)
end

/-- Every variable of the expression is below the bound. -/
def Expr.ClosedAt {V : Type} (bound : Nat) : Expr V → Prop
  | .var index => index < bound
  | .val _ => True

mutual
/-- Every free variable of the process is below the bound. -/
def Proc.ClosedAt {P V L : Type} (bound : Nat) : Proc P V L → Prop
  | .inact => True
  | .send _ payload next => payload.ClosedAt bound ∧ next.ClosedAt bound
  | .recv _ next => next.ClosedAt (bound + 1)
  | .select _ _ next => next.ClosedAt bound
  | .branch _ branches => branches.ClosedAt bound

/-- Every continuation of the branch list is closed at the bound. -/
def Proc.Branches.ClosedAt {P V L : Type} (bound : Nat) : Proc.Branches P V L → Prop
  | .nil => True
  | .cons _ head tail => head.ClosedAt bound ∧ tail.ClosedAt bound
end

/-! ### Typing -/

/-- Expression sorting: a variable has its context sort, a value its own
sort. The value context is a list of sorts indexed by de Bruijn index. -/
inductive Expr.HasSort {V S : Type} (sortOf : V → S) :
    List S → Expr V → S → Prop where
  | var {ctx : List S} {index : Nat} {s : S} :
    ctx[index]? = some s → Expr.HasSort sortOf ctx (.var index) s
  | val {ctx : List S} {value : V} {s : S} :
    sortOf value = s → Expr.HasSort sortOf ctx (.val value) s

mutual
/-- Ordered typing, Fig. 7 [INACT], [SEND], [RCV], [SEL] and [BRANCH]
specialized: one session, one thread, the participant's own local type.
[BRANCH] types the branches against the same labels in the same order
(the source's common index set `I`, so the labels are distinct); [SEL] selects
from a well-formed local branch list, whose labels are distinct for the same
reason. -/
inductive HasType0 {P S V L : Type} [DecidableEq L] (sortOf : V → S) :
    List S → Proc P V L → LocalType P S L → Prop where
  | inact {ctx : List S} : HasType0 sortOf ctx .inact .end
  | send {ctx : List S} {peer : P} {payload : Expr V} {s : S}
    {next : Proc P V L} {t : LocalType P S L} :
    Expr.HasSort sortOf ctx payload s → HasType0 sortOf ctx next t →
      HasType0 sortOf ctx (.send peer payload next) (.send peer s t)
  | recv {ctx : List S} {peer : P} {s : S} {next : Proc P V L}
    {t : LocalType P S L} :
    HasType0 sortOf (s :: ctx) next t →
      HasType0 sortOf ctx (.recv peer next) (.recv peer s t)
  | select {ctx : List S} {peer : P} {label : L} {next : Proc P V L}
    {branches : LocalType.Branches P S L} {t : LocalType P S L} :
    branches.lookup label = some t → HasType0 sortOf ctx next t →
      branches.WellFormed →
      HasType0 sortOf ctx (.select peer label next) (.select peer branches)
  | branch {ctx : List S} {peer : P} {procs : Proc.Branches P V L}
    {types : LocalType.Branches P S L} :
    HasType0.Branches sortOf ctx procs types →
      HasType0 sortOf ctx (.branch peer procs) (.branch peer types)

/-- Ordered branch typing: same labels in the same order, each continuation
typed against the corresponding local continuation. Each label is fresh for
the rest of the process branch list: the source's branch labels range over an
index set, so repeated labels are not source syntax. -/
inductive HasType0.Branches {P S V L : Type} [DecidableEq L] (sortOf : V → S) :
    List S → Proc.Branches P V L → LocalType.Branches P S L → Prop where
  | nil {ctx : List S} : HasType0.Branches sortOf ctx .nil .nil
  | cons {ctx : List S} {label : L} {proc : Proc P V L} {t : LocalType P S L}
    {procs : Proc.Branches P V L} {types : LocalType.Branches P S L} :
    HasType0 sortOf ctx proc t → HasType0.Branches sortOf ctx procs types →
      label ∉ procs.labels →
      HasType0.Branches sortOf ctx (.cons label proc procs) (.cons label t types)
end

/-- Process typing closed under brace equality: ordered typing against some
brace-equal local type. -/
def HasType {P S V L : Type} [DecidableEq P] [DecidableEq S] [DecidableEq L]
    (sortOf : V → S) (ctx : List S) (proc : Proc P V L) (t : LocalType P S L) :
    Prop :=
  ∃ t₀ : LocalType P S L, HasType0 sortOf ctx proc t₀ ∧ t₀.braceEq t = true

/-! ### Networks -/

/-- One session: a sequential process for every participant. -/
abbrev Net (P V L : Type) := P → Proc P V L

/-- Typing by projections (Definition 5.8, specialized to a total
participant map): the global type is well formed and every peer's process
has that peer's projection, in the empty value context. Non-participants
project to `end` (project-specific: the source's full projection ranges
over participants only). -/
def Net.TypedBy {P S V L : Type} [DecidableEq P] [DecidableEq S] [DecidableEq L]
    (sortOf : V → S) (G : GlobalType P S L) (net : Net P V L) : Prop :=
  G.WellFormed ∧ ∀ peer : P, ∃ t : LocalType P S L,
    G.project peer = some t ∧ HasType sortOf [] (net peer) t

/-- Synchronous labelled network step (no queues): a send of a value meets
the matching receive, or a selection meets the matching branch. Defined
for the subject reduction unit; no theorem about it is stated here. -/
inductive Net.Step {P S V L : Type} [DecidableEq P] [DecidableEq L]
    (sortOf : V → S) : Net P V L → GlobalType.Label P S L → Net P V L → Prop where
  | msg {net : Net P V L} {sender receiver : P} {value : V}
    {next cont : Proc P V L} :
    sender ≠ receiver →
    net sender = .send receiver (.val value) next →
    net receiver = .recv sender cont →
    Net.Step sortOf net (.msg sender receiver (sortOf value))
      (Function.update (Function.update net sender next) receiver
        (cont.subst value 0))
  | choice {net : Net P V L} {sender receiver : P} {label : L}
    {next cont : Proc P V L} {branches : Proc.Branches P V L} :
    sender ≠ receiver →
    net sender = .select receiver label next →
    net receiver = .branch sender branches →
    branches.lookup label = some cont →
    Net.Step sortOf net (.choice sender receiver label)
      (Function.update (Function.update net sender next) receiver cont)

/-! ### Structural lemmas -/

section Ordered

variable {P S V L : Type} [DecidableEq L] {sortOf : V → S}

omit [DecidableEq L] in
/-- Lifting keeps the labels of a process branch list. -/
private theorem Proc.Branches.labels_lift (cutoff : Nat) :
    ∀ procs : Proc.Branches P V L, (procs.lift cutoff).labels = procs.labels
  | .nil => by rw [Proc.Branches.lift]
  | .cons label head tail => by
    have ih := Proc.Branches.labels_lift cutoff tail
    simp only [Proc.Branches.lift, Proc.Branches.labels, Proc.Branches.entries,
      List.map_cons] at ih ⊢
    rw [ih]

omit [DecidableEq L] in
/-- Substitution keeps the labels of a process branch list. -/
private theorem Proc.Branches.labels_subst (value : V) (index : Nat) :
    ∀ procs : Proc.Branches P V L, (procs.subst value index).labels = procs.labels
  | .nil => by rw [Proc.Branches.subst]
  | .cons label head tail => by
    have ih := Proc.Branches.labels_subst value index tail
    simp only [Proc.Branches.subst, Proc.Branches.labels, Proc.Branches.entries,
      List.map_cons] at ih ⊢
    rw [ih]

/-- Weakening for expression sorting. -/
private theorem Expr.HasSort.weaken {ctx : List S} {e : Expr V} {s₀ : S}
    (cutoff : Nat) (s : S) :
    Expr.HasSort sortOf ctx e s₀ →
      Expr.HasSort sortOf (ctx.insertIdx cutoff s) (e.lift cutoff) s₀
  | .var h => by
    rw [Expr.lift]
    split
    · exact .var (by rw [List.getElem?_insertIdx_of_gt (by omega)]; exact h)
    · exact .var (by rw [List.getElem?_insertIdx_of_lt (by omega)]; exact h)
  | .val h => by
    rw [Expr.lift]
    exact .val h

/-- Substitution for expression sorting. -/
private theorem Expr.HasSort.subst {ctx : List S} {e : Expr V} {s₀ : S} {index : Nat}
    {s : S} {value : V} :
    Expr.HasSort sortOf (ctx.insertIdx index s) e s₀ → sortOf value = s →
      index ≤ ctx.length → Expr.HasSort sortOf ctx (e.subst value index) s₀
  | .var h, hs, hle => by
    rw [Expr.subst]
    split
    · rename_i heq
      subst heq
      rw [List.getElem?_insertIdx_self, ite_eq_left hle, Option.some.injEq] at h
      exact .val (hs.trans h)
    · split
      · rename_i hlt
        rw [List.getElem?_insertIdx_of_gt hlt] at h
        exact .var h
      · rw [List.getElem?_insertIdx_of_lt (by omega)] at h
        exact .var h
  | .val h, _, _ => by
    rw [Expr.subst]
    exact .val h

/-- A sorted expression is closed at the context length. -/
private theorem Expr.HasSort.closedAt {ctx : List S} {e : Expr V} {s : S} :
    Expr.HasSort sortOf ctx e s → e.ClosedAt ctx.length
  | .var h => by
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp h
    exact hi
  | .val _ => trivial

mutual
/-- (T1) Value-context weakening, ordered typing (standard structural
lemma). -/
theorem HasType0.weaken {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} (cutoff : Nat) (s : S) :
    HasType0 sortOf ctx proc t →
      HasType0 sortOf (ctx.insertIdx cutoff s) (proc.lift cutoff) t
  | .inact => by
    rw [Proc.lift]
    exact .inact
  | .send hs hnext => by
    rw [Proc.lift]
    exact .send (hs.weaken cutoff s) (hnext.weaken cutoff s)
  | .recv hnext => by
    rw [Proc.lift]
    exact .recv (hnext.weaken (cutoff + 1) s)
  | .select hlook hnext hwf => by
    rw [Proc.lift]
    exact .select hlook (hnext.weaken cutoff s) hwf
  | .branch hbs => by
    rw [Proc.lift]
    exact .branch (hbs.weaken cutoff s)

/-- (T1) Value-context weakening, ordered branch typing. -/
theorem HasType0.Branches.weaken {ctx : List S} {procs : Proc.Branches P V L}
    {types : LocalType.Branches P S L} (cutoff : Nat) (s : S) :
    HasType0.Branches sortOf ctx procs types →
      HasType0.Branches sortOf (ctx.insertIdx cutoff s) (procs.lift cutoff) types
  | .nil => by
    rw [Proc.Branches.lift]
    exact .nil
  | .cons hhead htail hfresh => by
    rw [Proc.Branches.lift]
    exact .cons (hhead.weaken cutoff s) (htail.weaken cutoff s)
      (by rw [Proc.Branches.labels_lift]; exact hfresh)
end

mutual
/-- (T2) Substitution of a closed value, ordered typing (Lemma 5.18 (1)). -/
theorem HasType0.subst {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} {index : Nat} {s : S} {value : V} :
    HasType0 sortOf (ctx.insertIdx index s) proc t → sortOf value = s →
      index ≤ ctx.length → HasType0 sortOf ctx (proc.subst value index) t
  | .inact, _, _ => by
    rw [Proc.subst]
    exact .inact
  | .send hsort hnext, hs, hle => by
    rw [Proc.subst]
    exact .send (hsort.subst hs hle) (hnext.subst hs hle)
  | .recv (s := s₁) hnext, hs, hle => by
    rw [Proc.subst]
    exact .recv (HasType0.subst (ctx := s₁ :: ctx) (index := index + 1) hnext hs
      (Nat.succ_le_succ hle))
  | .select hlook hnext hwf, hs, hle => by
    rw [Proc.subst]
    exact .select hlook (hnext.subst hs hle) hwf
  | .branch hbs, hs, hle => by
    rw [Proc.subst]
    exact .branch (hbs.subst hs hle)

/-- (T2) Substitution of a closed value, ordered branch typing. -/
theorem HasType0.Branches.subst {ctx : List S} {procs : Proc.Branches P V L}
    {types : LocalType.Branches P S L} {index : Nat} {s : S} {value : V} :
    HasType0.Branches sortOf (ctx.insertIdx index s) procs types →
      sortOf value = s → index ≤ ctx.length →
      HasType0.Branches sortOf ctx (procs.subst value index) types
  | .nil, _, _ => by
    rw [Proc.Branches.subst]
    exact .nil
  | .cons hhead htail hfresh, hs, hle => by
    rw [Proc.Branches.subst]
    exact .cons (hhead.subst hs hle) (htail.subst hs hle)
      (by rw [Proc.Branches.labels_subst]; exact hfresh)
end

mutual
/-- (T3) Free variables of an ordered-typed process occur in the context
(Lemma 5.15, value variables). -/
theorem HasType0.closedAt {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} :
    HasType0 sortOf ctx proc t → proc.ClosedAt ctx.length
  | .inact => trivial
  | .send hs hnext => by
    rw [Proc.ClosedAt]
    exact ⟨hs.closedAt, hnext.closedAt⟩
  | .recv hnext => by
    rw [Proc.ClosedAt]
    exact hnext.closedAt
  | .select _ hnext _ => by
    rw [Proc.ClosedAt]
    exact hnext.closedAt
  | .branch hbs => by
    rw [Proc.ClosedAt]
    exact hbs.closedAt

/-- (T3) Branch version. -/
theorem HasType0.Branches.closedAt {ctx : List S} {procs : Proc.Branches P V L}
    {types : LocalType.Branches P S L} :
    HasType0.Branches sortOf ctx procs types → procs.ClosedAt ctx.length
  | .nil => trivial
  | .cons hhead htail _ => by
    rw [Proc.Branches.ClosedAt]
    exact ⟨hhead.closedAt, htail.closedAt⟩
end

/-- Ordered branch typing keeps the label list. -/
private theorem HasType0.Branches.labels_eq {ctx : List S} :
    ∀ {procs : Proc.Branches P V L} {types : LocalType.Branches P S L},
      HasType0.Branches sortOf ctx procs types → procs.labels = types.labels
  | _, _, .nil => rfl
  | _, _, .cons _ htail _ => by
    have ih := htail.labels_eq
    simp only [Proc.Branches.labels, LocalType.Branches.labels,
      Proc.Branches.entries, LocalType.Branches.entries, List.map_cons] at ih ⊢
    rw [ih]

/-- Ordered branch typing has distinct labels on both sides: freshness is
stated on the process list and transfers to the type list. -/
private theorem HasType0.Branches.labels_nodup {ctx : List S} :
    ∀ {procs : Proc.Branches P V L} {types : LocalType.Branches P S L},
      HasType0.Branches sortOf ctx procs types →
        procs.labels.Nodup ∧ types.labels.Nodup
  | _, _, .nil => ⟨List.nodup_nil, List.nodup_nil⟩
  | _, _, .cons _ htail hfresh => by
    have ih := htail.labels_nodup
    have heq := htail.labels_eq
    simp only [Proc.Branches.labels, LocalType.Branches.labels, Proc.Branches.entries,
      LocalType.Branches.entries, List.map_cons, List.nodup_cons] at ih heq hfresh ⊢
    exact ⟨⟨hfresh, ih.1⟩, ⟨by rw [← heq]; exact hfresh, ih.2⟩⟩

/-- Ordered branch typing transports lookup. -/
private theorem HasType0.Branches.lookup_some {ctx : List S} {label : L}
    {proc : Proc P V L} :
    ∀ {procs : Proc.Branches P V L} {types : LocalType.Branches P S L},
      HasType0.Branches sortOf ctx procs types → procs.lookup label = some proc →
        ∃ u : LocalType P S L, types.lookup label = some u ∧
          HasType0 sortOf ctx proc u
  | _, _, .nil, h => by cases h
  | _, _, .cons (label := entryLabel) hhead htail _, h => by
    by_cases hl : label = entryLabel
    · rw [Proc.Branches.lookup, ite_eq_left hl, Option.some.injEq] at h
      subst h
      exact ⟨_, by rw [LocalType.Branches.lookup, ite_eq_left hl], hhead⟩
    · rw [Proc.Branches.lookup, ite_eq_right hl] at h
      obtain ⟨u, hu, htu⟩ := htail.lookup_some h
      exact ⟨u, by rw [LocalType.Branches.lookup, ite_eq_right hl]; exact hu, htu⟩

mutual
/-- Ordered typing only assigns well-formed local types. -/
private theorem HasType0.wellFormed {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} : HasType0 sortOf ctx proc t → t.WellFormed
  | .inact => .end
  | .send _ hnext => .send hnext.wellFormed
  | .recv hnext => .recv hnext.wellFormed
  | .select _ _ hwf => .select hwf
  | .branch hbs => .branch hbs.wellFormed

/-- Ordered branch typing only assigns well-formed local branch lists. -/
private theorem HasType0.Branches.wellFormed {ctx : List S}
    {procs : Proc.Branches P V L} {types : LocalType.Branches P S L} :
    HasType0.Branches sortOf ctx procs types → types.WellFormed
  | .nil => .nil
  | .cons hhead htail hfresh =>
    .cons (by rw [← htail.labels_eq]; exact hfresh) hhead.wellFormed htail.wellFormed
end

end Ordered

section Lemmas

variable {P S V L : Type} [DecidableEq P] [DecidableEq S] [DecidableEq L]
  {sortOf : V → S}

/-- Ordered typing implies typing. -/
theorem HasType.of_hasType0 {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} (h : HasType0 sortOf ctx proc t) :
    HasType sortOf ctx proc t :=
  ⟨t, h, LocalType.braceEq_refl t⟩

/-- (T1) Value-context weakening (standard structural lemma). -/
theorem HasType.weaken {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} (index : Nat) (s : S) :
    HasType sortOf ctx proc t →
      HasType sortOf (ctx.insertIdx index s) (proc.lift index) t := by
  rintro ⟨t₀, h, hb⟩
  exact ⟨t₀, h.weaken index s, hb⟩

/-- (T2) Substitution of a closed value (Lemma 5.18 (1)). -/
theorem HasType.subst {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} {index : Nat} {s : S} {value : V} :
    HasType sortOf (ctx.insertIdx index s) proc t → sortOf value = s →
      index ≤ ctx.length → HasType sortOf ctx (proc.subst value index) t := by
  rintro ⟨t₀, h, hb⟩ hs hle
  exact ⟨t₀, h.subst hs hle, hb⟩

/-- (T2′) Substitution for the innermost variable, the form a receive step
consumes. -/
theorem HasType.subst_zero {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} {s : S} {value : V} :
    HasType sortOf (s :: ctx) proc t → sortOf value = s →
      HasType sortOf ctx (proc.subst value 0) t := by
  intro h hs
  exact HasType.subst (index := 0) (by simpa using h) hs (Nat.zero_le _)

/-- (T3) Free variables of a typed process occur in the context
(Lemma 5.15, value variables). -/
theorem HasType.closedAt {ctx : List S} {proc : Proc P V L}
    {t : LocalType P S L} :
    HasType sortOf ctx proc t → proc.ClosedAt ctx.length := by
  rintro ⟨t₀, h, -⟩
  exact h.closedAt

/-- (T5) Typing is invariant under brace equality of the local type. -/
theorem HasType.braceEq {ctx : List S} {proc : Proc P V L}
    {t t' : LocalType P S L} :
    HasType sortOf ctx proc t → t.braceEq t' = true →
      HasType sortOf ctx proc t' := by
  rintro ⟨t₀, h, hb⟩ htt'
  exact ⟨t₀, h, LocalType.braceEq_trans hb htt'⟩

/-- (T6) Inversion for inaction. -/
theorem HasType.inact_inv {ctx : List S} {t : LocalType P S L} :
    HasType sortOf ctx (Proc.inact : Proc P V L) t → t = .end := by
  rintro ⟨t₀, h, hb⟩
  cases h
  cases t <;> simp_all [LocalType.braceEq]

/-- (T6) Only inaction has type `end`. -/
theorem HasType.eq_inact_of_end {ctx : List S} {proc : Proc P V L} :
    HasType sortOf ctx proc .end → proc = .inact := by
  rintro ⟨t₀, h, hb⟩
  cases t₀ <;> simp [LocalType.braceEq] at hb
  cases h
  rfl

/-- (T6) Inversion for send. -/
theorem HasType.send_inv {ctx : List S} {peer : P} {payload : Expr V}
    {next : Proc P V L} {t : LocalType P S L} :
    HasType sortOf ctx (.send peer payload next) t →
      ∃ (s : S) (t' : LocalType P S L), t = .send peer s t' ∧
        Expr.HasSort sortOf ctx payload s ∧ HasType sortOf ctx next t' := by
  rintro ⟨t₀, h, hb⟩
  cases h with
  | send hs hnext =>
    cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
      Bool.false_eq_true] at hb
    obtain ⟨⟨rfl, rfl⟩, hb⟩ := hb
    exact ⟨_, _, rfl, hs, _, hnext, hb⟩

/-- (T6) Inversion for receive. -/
theorem HasType.recv_inv {ctx : List S} {peer : P} {next : Proc P V L}
    {t : LocalType P S L} :
    HasType sortOf ctx (.recv peer next) t →
      ∃ (s : S) (t' : LocalType P S L), t = .recv peer s t' ∧
        HasType sortOf (s :: ctx) next t' := by
  rintro ⟨t₀, h, hb⟩
  cases h with
  | recv hnext =>
    cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
      Bool.false_eq_true] at hb
    obtain ⟨⟨rfl, rfl⟩, hb⟩ := hb
    exact ⟨_, _, rfl, _, hnext, hb⟩

/-- (T6) Inversion for selection: the selected label is offered by the
type, and the continuation has that branch's type. -/
theorem HasType.select_inv {ctx : List S} {peer : P} {label : L}
    {next : Proc P V L} {t : LocalType P S L} :
    HasType sortOf ctx (.select peer label next) t →
      ∃ (branches : LocalType.Branches P S L) (u : LocalType P S L),
        t = .select peer branches ∧ branches.lookup label = some u ∧
        HasType sortOf ctx next u := by
  rintro ⟨t₀, h, hb⟩
  cases h with
  | select hlook hnext _ =>
    cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
      Bool.false_eq_true] at hb
    obtain ⟨rfl, hb⟩ := hb
    obtain ⟨u, hu, htu⟩ := LocalType.Branches.braceEq_lookup hb hlook
    exact ⟨_, u, rfl, hu, _, hnext, htu⟩

/-- (T6) Inversion for branching: the same label set, and every process
branch has the type's branch for its label. -/
theorem HasType.branch_inv {ctx : List S} {peer : P}
    {procs : Proc.Branches P V L} {t : LocalType P S L} :
    HasType sortOf ctx (.branch peer procs) t →
      ∃ types : LocalType.Branches P S L, t = .branch peer types ∧
        (∀ label : L, label ∈ procs.labels ↔ label ∈ types.labels) ∧
        ∀ (label : L) (proc : Proc P V L), procs.lookup label = some proc →
          ∃ u : LocalType P S L, types.lookup label = some u ∧
            HasType sortOf ctx proc u := by
  rintro ⟨t₀, h, hb⟩
  cases h with
  | branch hbs =>
    cases t <;> simp only [LocalType.braceEq, Bool.and_eq_true, beq_iff_eq,
      Bool.false_eq_true] at hb
    obtain ⟨rfl, hb⟩ := hb
    refine ⟨_, rfl, ?_, ?_⟩
    · intro label
      rw [hbs.labels_eq]
      exact LocalType.Branches.braceEq_mem_labels hb label
    · intro label proc hlook
      obtain ⟨u₀, hu₀, hproc⟩ := hbs.lookup_some hlook
      obtain ⟨u, hu, hbu⟩ := LocalType.Branches.braceEq_lookup hb hu₀
      exact ⟨u, hu, u₀, hproc, hbu⟩

/-- (T7) Typing by projections forces non-participants to be inert:
non-participants project to `end`, and only `.inact` has type `end`. A
project-specific consequence of total networks; the source's full
projection (Definition 5.8) ranges over participants only. -/
theorem Net.TypedBy.inact_of_not_mem {G : GlobalType P S L} {net : Net P V L}
    {peer : P} :
    Net.TypedBy sortOf G net → peer ∉ G.participants → net peer = .inact := by
  rintro ⟨hwf, htyped⟩ hnot
  obtain ⟨t, hproj, ht⟩ := htyped peer
  rw [GlobalType.project_of_not_mem_participants hwf.1 hnot] at hproj
  cases hproj
  exact HasType.eq_inact_of_end ht

/-- (T8) Typing by projections, packaged with well-formedness of each
projection. -/
theorem Net.TypedBy.project_some {G : GlobalType P S L} {net : Net P V L} :
    Net.TypedBy sortOf G net → ∀ peer : P, ∃ t : LocalType P S L,
      G.project peer = some t ∧ t.WellFormed ∧ HasType sortOf [] (net peer) t := by
  rintro ⟨hwf, htyped⟩ peer
  obtain ⟨t, hproj, ht⟩ := htyped peer
  exact ⟨t, hproj, GlobalType.project_wellFormed hwf.1 hproj, ht⟩

end Lemmas

end Multiparty

end Cslib.SessionTypes
