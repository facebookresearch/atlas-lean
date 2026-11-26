/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Branching
public import Mathlib.Data.Finset.Basic

/-!
# Multiparty session types: finite global types and projection

Finite, synchronous, participant-addressed fragment of the global and local
types of Honda, Yoshida and Carbone, *Multiparty Asynchronous Session Types*,
JACM 63(1), 2016: the global-type grammar (Fig. 4) and local-type grammar
(Fig. 6) without parallel composition, recursion, channel indices, delegation
and shared-name sorts, with participants in place of channel indices, and
projection (Definition 4.1) with plain merging. Coherence (Definition 4.2)
specializes to projectability at every participant in this fragment, and
well-formedness is decidable (Theorem 4.3, specialized).

Project-specific, not from the source: the structural brace equality used by
plain merging, and the bridge (`LocalType.erase`) from local types to binary
`BranchingType`s with its two-party duality statement.

No LTS, subject reduction or session fidelity (separate units); no
asynchrony or queues; no linearity predicate (a channel-race condition that
does not arise for participant-addressed finite global types); no subtyping;
no process typing. Branch lists are ordered association lists, as in
`Branching`; choices communicated to a third party are compared by
`LocalType.braceEq`, not by syntactic `=`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

mutual
/-- Finite global type over participants `P`, payload sorts `S` and choice
labels `L`: inaction, one message from sender to receiver, or a labelled
choice from sender to receiver. -/
inductive GlobalType (P S L : Type) where
  | end : GlobalType P S L
  | msg (sender receiver : P) (payload : S) (next : GlobalType P S L) :
    GlobalType P S L
  | choice (sender receiver : P) (branches : GlobalType.Branches P S L) :
    GlobalType P S L
deriving DecidableEq

/-- Ordered association list of labelled global continuations. -/
inductive GlobalType.Branches (P S L : Type) where
  | nil : GlobalType.Branches P S L
  | cons (label : L) (head : GlobalType P S L)
    (tail : GlobalType.Branches P S L) : GlobalType.Branches P S L
deriving DecidableEq
end

/-- Association-list entries of a global branch list, in order. -/
def GlobalType.Branches.entries {P S L : Type}
    (branches : GlobalType.Branches P S L) : List (L × GlobalType P S L) :=
  match branches with
  | .nil => ([] : List (L × GlobalType P S L))
  | .cons label head tail => (label, head) :: tail.entries

/-- Labels of a global branch list, in order. -/
def GlobalType.Branches.labels {P S L : Type}
    (branches : GlobalType.Branches P S L) : List L :=
  branches.entries.map Prod.fst

/-- First match on the raw ordered list, or `none` if absent. -/
def GlobalType.Branches.lookup {P S L : Type} [DecidableEq L]
    (branches : GlobalType.Branches P S L) (label : L) :
    Option (GlobalType P S L) :=
  match branches with
  | .nil => (none : Option (GlobalType P S L))
  | .cons entryLabel head tail =>
    if label = entryLabel then some head else tail.lookup label

mutual
/-- Participants occurring in a global type. -/
def GlobalType.participants {P S L : Type} [DecidableEq P] :
    GlobalType P S L → Finset P
  | .end => ∅
  | .msg sender receiver _ next =>
    insert sender (insert receiver next.participants)
  | .choice sender receiver branches =>
    insert sender (insert receiver branches.participants)

/-- Participants occurring in a global branch list. -/
def GlobalType.Branches.participants {P S L : Type} [DecidableEq P] :
    GlobalType.Branches P S L → Finset P
  | .nil => ∅
  | .cons _ head tail => head.participants ∪ tail.participants
end

mutual
/-- Finite local (end-point) type: inaction, send/receive one payload to or
from a peer, or select/branch over labelled continuations with one peer. -/
inductive LocalType (P S L : Type) where
  | end : LocalType P S L
  | send (peer : P) (payload : S) (next : LocalType P S L) : LocalType P S L
  | recv (peer : P) (payload : S) (next : LocalType P S L) : LocalType P S L
  | select (peer : P) (branches : LocalType.Branches P S L) : LocalType P S L
  | branch (peer : P) (branches : LocalType.Branches P S L) : LocalType P S L
deriving DecidableEq

/-- Ordered association list of labelled local continuations. -/
inductive LocalType.Branches (P S L : Type) where
  | nil : LocalType.Branches P S L
  | cons (label : L) (head : LocalType P S L)
    (tail : LocalType.Branches P S L) : LocalType.Branches P S L
deriving DecidableEq
end

/-- Association-list entries of a local branch list, in order. -/
def LocalType.Branches.entries {P S L : Type}
    (branches : LocalType.Branches P S L) : List (L × LocalType P S L) :=
  match branches with
  | .nil => ([] : List (L × LocalType P S L))
  | .cons label head tail => (label, head) :: tail.entries

/-- Labels of a local branch list, in order. -/
def LocalType.Branches.labels {P S L : Type}
    (branches : LocalType.Branches P S L) : List L :=
  branches.entries.map Prod.fst

/-- First match on the raw ordered list, or `none` if absent. -/
def LocalType.Branches.lookup {P S L : Type} [DecidableEq L]
    (branches : LocalType.Branches P S L) (label : L) :
    Option (LocalType P S L) :=
  match branches with
  | .nil => (none : Option (LocalType P S L))
  | .cons entryLabel head tail =>
    if label = entryLabel then some head else tail.lookup label

/-- Remove the first entry with the given label, if present. -/
def LocalType.Branches.eraseLabel {P S L : Type} [DecidableEq L] :
    LocalType.Branches P S L → L → LocalType.Branches P S L
  | .nil, _ => .nil
  | .cons entryLabel head tail, label =>
    if label = entryLabel then tail else .cons entryLabel head (tail.eraseLabel label)

mutual
/-- Well-formed local types: continuations and branch lists are well formed. -/
inductive LocalType.WellFormed {P S L : Type} : LocalType P S L → Prop where
  | end : LocalType.WellFormed .end
  | send {peer : P} {payload : S} {next : LocalType P S L} :
    LocalType.WellFormed next →
      LocalType.WellFormed (.send peer payload next)
  | recv {peer : P} {payload : S} {next : LocalType P S L} :
    LocalType.WellFormed next →
      LocalType.WellFormed (.recv peer payload next)
  | select {peer : P} {branches : LocalType.Branches P S L} :
    LocalType.Branches.WellFormed branches →
      LocalType.WellFormed (.select peer branches)
  | branch {peer : P} {branches : LocalType.Branches P S L} :
    LocalType.Branches.WellFormed branches →
      LocalType.WellFormed (.branch peer branches)

/-- Well-formed local branch lists: distinct labels, well-formed heads. -/
inductive LocalType.Branches.WellFormed {P S L : Type} :
    LocalType.Branches P S L → Prop where
  | nil : LocalType.Branches.WellFormed .nil
  | cons {label : L} {head : LocalType P S L}
    {tail : LocalType.Branches P S L} : label ∉ tail.labels →
    LocalType.WellFormed head →
    LocalType.Branches.WellFormed tail →
    LocalType.Branches.WellFormed (.cons label head tail)
end

mutual
/-- Brace equality of local types: same constructors, peers and payloads,
with choice branches compared up to order. This reads the source's
"identical end-point type" side condition of plain merging over brace
families; it is project-specific. The order-insensitive reading is the
semantics on distinct-label branch lists; on lists with repeated labels the
function is a greedy first-match comparison and carries no source meaning. -/
def LocalType.braceEq {P S L : Type} [DecidableEq P] [DecidableEq S]
    [DecidableEq L] : LocalType P S L → LocalType P S L → Bool
  | .end, .end => true
  | .send peer payload next, .send peer' payload' next' =>
    peer == peer' && payload == payload' && next.braceEq next'
  | .recv peer payload next, .recv peer' payload' next' =>
    peer == peer' && payload == payload' && next.braceEq next'
  | .select peer branches, .select peer' branches' =>
    peer == peer' && branches.braceEq branches'
  | .branch peer branches, .branch peer' branches' =>
    peer == peer' && branches.braceEq branches'
  | _, _ => false

/-- Brace equality of local branch lists: every entry of the first list has
a brace-equal entry with the same label in the second, consumed once. -/
def LocalType.Branches.braceEq {P S L : Type} [DecidableEq P] [DecidableEq S]
    [DecidableEq L] : LocalType.Branches P S L → LocalType.Branches P S L → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ _ => false
  | .cons label head tail, branches' =>
    match branches'.lookup label with
    | some head' => head.braceEq head' && tail.braceEq (branches'.eraseLabel label)
    | none => false
end

mutual
/-- Projection of a global type onto one participant (Def. 4.1, finite
fragment): principals send, receive, select or branch; a third party follows
messages and needs every choice branch to project to brace-equal types
(plain merging). A reflexive interaction has no projection onto its
principal; a third party still projects it as above. -/
def GlobalType.project {P S L : Type} [DecidableEq P] [DecidableEq S]
    [DecidableEq L] : GlobalType P S L → P → Option (LocalType P S L)
  | .end, _ => some .end
  | .msg sender receiver payload next, peer =>
    if peer = sender then
      if sender = receiver then none
      else (next.project peer).map (.send receiver payload)
    else if peer = receiver then
      (next.project peer).map (.recv sender payload)
    else next.project peer
  | .choice sender receiver branches, peer =>
    if peer = sender then
      if sender = receiver then none
      else (branches.projectBranches peer).map (.select receiver)
    else if peer = receiver then
      (branches.projectBranches peer).map (.branch sender)
    else branches.projectThirdParty peer

/-- Project every branch of a choice for a principal, rebuilding the list. -/
def GlobalType.Branches.projectBranches {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] :
    GlobalType.Branches P S L → P → Option (LocalType.Branches P S L)
  | .nil, _ => some .nil
  | .cons label head tail, peer =>
    match head.project peer, tail.projectBranches peer with
    | some head', some tail' => some (.cons label head' tail')
    | _, _ => none

/-- Project every branch of a choice onto a list of local types. -/
def GlobalType.Branches.projectList {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] :
    GlobalType.Branches P S L → P → Option (List (LocalType P S L))
  | .nil, _ => some []
  | .cons _ head tail, peer =>
    match head.project peer, tail.projectList peer with
    | some head', some tail' => some (head' :: tail')
    | _, _ => none

/-- Third-party projection of a choice: defined when the branch list is
nonempty and every pair of branch projections is brace-equal; the first
projection is returned (plain merging). -/
def GlobalType.Branches.projectThirdParty {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] :
    GlobalType.Branches P S L → P → Option (LocalType P S L)
  | .nil, _ => none
  | .cons _ head tail, peer =>
    match head.project peer, tail.projectList peer with
    | some head', some rest =>
      if (head' :: rest).all (fun t => (head' :: rest).all (LocalType.braceEq t))
      then some head' else none
    | _, _ => none
end

mutual
/-- Label well-formedness of global types: every choice has a nonempty
branch list with distinct labels and label-well-formed continuations. -/
inductive GlobalType.LabelsWellFormed {P S L : Type} :
    GlobalType P S L → Prop where
  | end : GlobalType.LabelsWellFormed .end
  | msg {sender receiver : P} {payload : S} {next : GlobalType P S L} :
    GlobalType.LabelsWellFormed next →
      GlobalType.LabelsWellFormed (.msg sender receiver payload next)
  | choice {sender receiver : P} {branches : GlobalType.Branches P S L} :
    branches ≠ .nil →
    GlobalType.Branches.LabelsWellFormed branches →
      GlobalType.LabelsWellFormed (.choice sender receiver branches)

/-- Label well-formedness of global branch lists. -/
inductive GlobalType.Branches.LabelsWellFormed {P S L : Type} :
    GlobalType.Branches P S L → Prop where
  | nil : GlobalType.Branches.LabelsWellFormed .nil
  | cons {label : L} {head : GlobalType P S L}
    {tail : GlobalType.Branches P S L} : label ∉ tail.labels →
    GlobalType.LabelsWellFormed head →
    GlobalType.Branches.LabelsWellFormed tail →
    GlobalType.Branches.LabelsWellFormed (.cons label head tail)
end

mutual
/-- Boolean label-well-formedness checker for global types. -/
def GlobalType.labelsCheck {P S L : Type} [DecidableEq L] :
    GlobalType P S L → Bool
  | .end => true
  | .msg _ _ _ next => next.labelsCheck
  | .choice _ _ branches =>
    !(branches.labels.isEmpty) && decide branches.labels.Nodup && branches.labelsCheck

/-- Boolean label-well-formedness checker for global branch lists. -/
def GlobalType.Branches.labelsCheck {P S L : Type} [DecidableEq L] :
    GlobalType.Branches P S L → Bool
  | .nil => true
  | .cons label head tail =>
    decide (label ∉ tail.labels) && head.labelsCheck && tail.labelsCheck
end

/-- The Boolean checker decides label well-formedness of global types. -/
theorem GlobalType.labelsCheck_iff {P S L : Type} [DecidableEq L]
    (G : GlobalType P S L) :
    G.labelsCheck = true ↔ G.LabelsWellFormed := by
  have key : (∀ G : GlobalType P S L,
    G.labelsCheck = true ↔ G.LabelsWellFormed) ∧
    (∀ bs : GlobalType.Branches P S L,
      (bs.labelsCheck = true ↔ bs.LabelsWellFormed) ∧
        (bs.LabelsWellFormed → bs.labels.Nodup)) := by
    refine ⟨fun G => ?_, fun bs => ?_⟩
    · apply GlobalType.rec
        (motive_1 := fun G => G.labelsCheck = true ↔ G.LabelsWellFormed)
        (motive_2 := fun bs => (bs.labelsCheck = true ↔
          bs.LabelsWellFormed) ∧ (bs.LabelsWellFormed → bs.labels.Nodup))
      · exact Iff.intro (fun _ => GlobalType.LabelsWellFormed.end)
          (fun _ => rfl)
      · intro sender receiver payload next ih
        constructor
        · intro hcheck
          change next.labelsCheck = true at hcheck
          exact GlobalType.LabelsWellFormed.msg (ih.mp hcheck)
        · intro hwf
          cases hwf with
          | msg hnext =>
            change next.labelsCheck = true
            exact ih.mpr hnext
      · intro sender receiver branches ih
        constructor
        · intro hcheck
          change ((!branches.labels.isEmpty &&
            decide branches.labels.Nodup && branches.labelsCheck) = true)
            at hcheck
          have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
          have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
          have ha := hsplit2.1
          have hbranches := ih.1.mp hsplit1.2
          have hne : branches ≠ .nil := by
            cases branches with
            | nil =>
              change (false = true) at ha
              cases ha
            | cons label head tail =>
              intro hcontra
              cases hcontra
          exact GlobalType.LabelsWellFormed.choice hne hbranches
        · intro hwf
          cases hwf with
          | choice hne hbranches =>
            have hcheck_branches := ih.1.mpr hbranches
            have hnodup := ih.2 hbranches
            have hdec : decide branches.labels.Nodup = true :=
              decide_eq_true hnodup
            have hisempty : (!branches.labels.isEmpty) = true := by
              cases branches with
              | nil =>
                cases hne rfl
              | cons label head tail =>
                rfl
            change ((!branches.labels.isEmpty &&
              decide branches.labels.Nodup && branches.labelsCheck) = true)
            rw [hisempty, hdec, hcheck_branches]
            rfl
      · constructor
        · exact Iff.intro (fun _ => GlobalType.Branches.LabelsWellFormed.nil)
            (fun _ => rfl)
        · intro _
          exact List.nodup_nil
      · intro label head tail ih_head ih_tail
        constructor
        · constructor
          · intro hcheck
            change ((decide (label ∉ tail.labels) && head.labelsCheck &&
              tail.labelsCheck) = true) at hcheck
            have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
            have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
            have hdec := hsplit2.1
            have hmem := of_decide_eq_true hdec
            have hhead := ih_head.mp hsplit2.2
            have htail := ih_tail.1.mp hsplit1.2
            exact GlobalType.Branches.LabelsWellFormed.cons hmem hhead htail
          · intro hwf
            cases hwf with
            | cons hmem hhead htail =>
              have hdec : decide (label ∉ tail.labels) = true :=
                decide_eq_true hmem
              have hhead_check := ih_head.mpr hhead
              have htail_check := ih_tail.1.mpr htail
              change ((decide (label ∉ tail.labels) && head.labelsCheck &&
                tail.labelsCheck) = true)
              rw [hdec, hhead_check, htail_check]
              rfl
        · intro hwf
          cases hwf with
          | cons hmem hhead htail =>
            exact List.nodup_cons.mpr ⟨hmem, ih_tail.2 htail⟩
    · apply GlobalType.Branches.rec
        (motive_1 := fun G => G.labelsCheck = true ↔ G.LabelsWellFormed)
        (motive_2 := fun bs => (bs.labelsCheck = true ↔
          bs.LabelsWellFormed) ∧ (bs.LabelsWellFormed → bs.labels.Nodup))
      · exact Iff.intro (fun _ => GlobalType.LabelsWellFormed.end)
          (fun _ => rfl)
      · intro sender receiver payload next ih
        constructor
        · intro hcheck
          change next.labelsCheck = true at hcheck
          exact GlobalType.LabelsWellFormed.msg (ih.mp hcheck)
        · intro hwf
          cases hwf with
          | msg hnext =>
            change next.labelsCheck = true
            exact ih.mpr hnext
      · intro sender receiver branches ih
        constructor
        · intro hcheck
          change ((!branches.labels.isEmpty &&
            decide branches.labels.Nodup && branches.labelsCheck) = true)
            at hcheck
          have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
          have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
          have ha := hsplit2.1
          have hbranches := ih.1.mp hsplit1.2
          have hne : branches ≠ .nil := by
            cases branches with
            | nil =>
              change (false = true) at ha
              cases ha
            | cons label head tail =>
              intro hcontra
              cases hcontra
          exact GlobalType.LabelsWellFormed.choice hne hbranches
        · intro hwf
          cases hwf with
          | choice hne hbranches =>
            have hcheck_branches := ih.1.mpr hbranches
            have hnodup := ih.2 hbranches
            have hdec : decide branches.labels.Nodup = true :=
              decide_eq_true hnodup
            have hisempty : (!branches.labels.isEmpty) = true := by
              cases branches with
              | nil =>
                cases hne rfl
              | cons label head tail =>
                rfl
            change ((!branches.labels.isEmpty &&
              decide branches.labels.Nodup && branches.labelsCheck) = true)
            rw [hisempty, hdec, hcheck_branches]
            rfl
      · constructor
        · exact Iff.intro (fun _ => GlobalType.Branches.LabelsWellFormed.nil)
            (fun _ => rfl)
        · intro _
          exact List.nodup_nil
      · intro label head tail ih_head ih_tail
        constructor
        · constructor
          · intro hcheck
            change ((decide (label ∉ tail.labels) && head.labelsCheck &&
              tail.labelsCheck) = true) at hcheck
            have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
            have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
            have hdec := hsplit2.1
            have hmem := of_decide_eq_true hdec
            have hhead := ih_head.mp hsplit2.2
            have htail := ih_tail.1.mp hsplit1.2
            exact GlobalType.Branches.LabelsWellFormed.cons hmem hhead htail
          · intro hwf
            cases hwf with
            | cons hmem hhead htail =>
              have hdec : decide (label ∉ tail.labels) = true :=
                decide_eq_true hmem
              have hhead_check := ih_head.mpr hhead
              have htail_check := ih_tail.1.mpr htail
              change ((decide (label ∉ tail.labels) && head.labelsCheck &&
                tail.labelsCheck) = true)
              rw [hdec, hhead_check, htail_check]
              rfl
        · intro hwf
          cases hwf with
          | cons hmem hhead htail =>
            exact List.nodup_cons.mpr ⟨hmem, ih_tail.2 htail⟩
  exact key.1 G

/-- The Boolean checker decides label well-formedness of branch lists. -/
theorem GlobalType.Branches.labelsCheck_iff {P S L : Type} [DecidableEq L]
    (branches : GlobalType.Branches P S L) :
    branches.labelsCheck = true ↔ branches.LabelsWellFormed := by
  have key : (∀ G : GlobalType P S L,
    G.labelsCheck = true ↔ G.LabelsWellFormed) ∧
    (∀ bs : GlobalType.Branches P S L,
      (bs.labelsCheck = true ↔ bs.LabelsWellFormed) ∧
        (bs.LabelsWellFormed → bs.labels.Nodup)) := by
    refine ⟨fun G => ?_, fun bs => ?_⟩
    · apply GlobalType.rec
        (motive_1 := fun G => G.labelsCheck = true ↔ G.LabelsWellFormed)
        (motive_2 := fun bs => (bs.labelsCheck = true ↔
          bs.LabelsWellFormed) ∧ (bs.LabelsWellFormed → bs.labels.Nodup))
      · exact Iff.intro (fun _ => GlobalType.LabelsWellFormed.end)
          (fun _ => rfl)
      · intro sender receiver payload next ih
        constructor
        · intro hcheck
          change next.labelsCheck = true at hcheck
          exact GlobalType.LabelsWellFormed.msg (ih.mp hcheck)
        · intro hwf
          cases hwf with
          | msg hnext =>
            change next.labelsCheck = true
            exact ih.mpr hnext
      · intro sender receiver branches ih
        constructor
        · intro hcheck
          change ((!branches.labels.isEmpty &&
            decide branches.labels.Nodup && branches.labelsCheck) = true)
            at hcheck
          have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
          have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
          have ha := hsplit2.1
          have hbranches := ih.1.mp hsplit1.2
          have hne : branches ≠ .nil := by
            cases branches with
            | nil =>
              change (false = true) at ha
              cases ha
            | cons label head tail =>
              intro hcontra
              cases hcontra
          exact GlobalType.LabelsWellFormed.choice hne hbranches
        · intro hwf
          cases hwf with
          | choice hne hbranches =>
            have hcheck_branches := ih.1.mpr hbranches
            have hnodup := ih.2 hbranches
            have hdec : decide branches.labels.Nodup = true :=
              decide_eq_true hnodup
            have hisempty : (!branches.labels.isEmpty) = true := by
              cases branches with
              | nil =>
                cases hne rfl
              | cons label head tail =>
                rfl
            change ((!branches.labels.isEmpty &&
              decide branches.labels.Nodup && branches.labelsCheck) = true)
            rw [hisempty, hdec, hcheck_branches]
            rfl
      · constructor
        · exact Iff.intro (fun _ => GlobalType.Branches.LabelsWellFormed.nil)
            (fun _ => rfl)
        · intro _
          exact List.nodup_nil
      · intro label head tail ih_head ih_tail
        constructor
        · constructor
          · intro hcheck
            change ((decide (label ∉ tail.labels) && head.labelsCheck &&
              tail.labelsCheck) = true) at hcheck
            have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
            have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
            have hdec := hsplit2.1
            have hmem := of_decide_eq_true hdec
            have hhead := ih_head.mp hsplit2.2
            have htail := ih_tail.1.mp hsplit1.2
            exact GlobalType.Branches.LabelsWellFormed.cons hmem hhead htail
          · intro hwf
            cases hwf with
            | cons hmem hhead htail =>
              have hdec : decide (label ∉ tail.labels) = true :=
                decide_eq_true hmem
              have hhead_check := ih_head.mpr hhead
              have htail_check := ih_tail.1.mpr htail
              change ((decide (label ∉ tail.labels) && head.labelsCheck &&
                tail.labelsCheck) = true)
              rw [hdec, hhead_check, htail_check]
              rfl
        · intro hwf
          cases hwf with
          | cons hmem hhead htail =>
            exact List.nodup_cons.mpr ⟨hmem, ih_tail.2 htail⟩
    · apply GlobalType.Branches.rec
        (motive_1 := fun G => G.labelsCheck = true ↔ G.LabelsWellFormed)
        (motive_2 := fun bs => (bs.labelsCheck = true ↔
          bs.LabelsWellFormed) ∧ (bs.LabelsWellFormed → bs.labels.Nodup))
      · exact Iff.intro (fun _ => GlobalType.LabelsWellFormed.end)
          (fun _ => rfl)
      · intro sender receiver payload next ih
        constructor
        · intro hcheck
          change next.labelsCheck = true at hcheck
          exact GlobalType.LabelsWellFormed.msg (ih.mp hcheck)
        · intro hwf
          cases hwf with
          | msg hnext =>
            change next.labelsCheck = true
            exact ih.mpr hnext
      · intro sender receiver branches ih
        constructor
        · intro hcheck
          change ((!branches.labels.isEmpty &&
            decide branches.labels.Nodup && branches.labelsCheck) = true)
            at hcheck
          have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
          have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
          have ha := hsplit2.1
          have hbranches := ih.1.mp hsplit1.2
          have hne : branches ≠ .nil := by
            cases branches with
            | nil =>
              change (false = true) at ha
              cases ha
            | cons label head tail =>
              intro hcontra
              cases hcontra
          exact GlobalType.LabelsWellFormed.choice hne hbranches
        · intro hwf
          cases hwf with
          | choice hne hbranches =>
            have hcheck_branches := ih.1.mpr hbranches
            have hnodup := ih.2 hbranches
            have hdec : decide branches.labels.Nodup = true :=
              decide_eq_true hnodup
            have hisempty : (!branches.labels.isEmpty) = true := by
              cases branches with
              | nil =>
                cases hne rfl
              | cons label head tail =>
                rfl
            change ((!branches.labels.isEmpty &&
              decide branches.labels.Nodup && branches.labelsCheck) = true)
            rw [hisempty, hdec, hcheck_branches]
            rfl
      · constructor
        · exact Iff.intro (fun _ => GlobalType.Branches.LabelsWellFormed.nil)
            (fun _ => rfl)
        · intro _
          exact List.nodup_nil
      · intro label head tail ih_head ih_tail
        constructor
        · constructor
          · intro hcheck
            change ((decide (label ∉ tail.labels) && head.labelsCheck &&
              tail.labelsCheck) = true) at hcheck
            have hsplit1 := (Bool.and_eq_true _ _).mp hcheck
            have hsplit2 := (Bool.and_eq_true _ _).mp hsplit1.1
            have hdec := hsplit2.1
            have hmem := of_decide_eq_true hdec
            have hhead := ih_head.mp hsplit2.2
            have htail := ih_tail.1.mp hsplit1.2
            exact GlobalType.Branches.LabelsWellFormed.cons hmem hhead htail
          · intro hwf
            cases hwf with
            | cons hmem hhead htail =>
              have hdec : decide (label ∉ tail.labels) = true :=
                decide_eq_true hmem
              have hhead_check := ih_head.mpr hhead
              have htail_check := ih_tail.1.mpr htail
              change ((decide (label ∉ tail.labels) && head.labelsCheck &&
                tail.labelsCheck) = true)
              rw [hdec, hhead_check, htail_check]
              rfl
        · intro hwf
          cases hwf with
          | cons hmem hhead htail =>
            exact List.nodup_cons.mpr ⟨hmem, ih_tail.2 htail⟩
  exact (key.2 branches).1

/-- Well-formed global types: label-well-formed and projectable at every
participant (coherence specialized to the finite participant-addressed
fragment). -/
def GlobalType.WellFormed {P S L : Type} [DecidableEq P] [DecidableEq S]
    [DecidableEq L] (G : GlobalType P S L) : Prop :=
  G.LabelsWellFormed ∧ ∀ peer ∈ G.participants, (G.project peer).isSome

/-- Well-formedness of finite global types is decidable. -/
instance GlobalType.decidableWellFormed {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] :
    DecidablePred (GlobalType.WellFormed (P := P) (S := S) (L := L)) := by
  intro G
  have hdec1 : Decidable (G.LabelsWellFormed) :=
    decidable_of_iff (G.labelsCheck = true)
      (GlobalType.labelsCheck_iff G)
  have hdec2 : Decidable (∀ peer ∈ G.participants,
    (G.project peer).isSome) :=
    Finset.decidableDforallFinset
  change Decidable (G.LabelsWellFormed ∧
    ∀ peer ∈ G.participants, (G.project peer).isSome)
  exact @instDecidableAnd _ _ hdec1 hdec2

mutual
/-- Forget peers: erase a local type to a binary branching type. -/
def LocalType.erase {P S L : Type} : LocalType P S L → BranchingType S L
  | .end => .end
  | .send _ payload next => .send payload next.erase
  | .recv _ payload next => .recv payload next.erase
  | .select _ branches => .select branches.erase
  | .branch _ branches => .branch branches.erase

/-- Forget peers in a local branch list. -/
def LocalType.Branches.erase {P S L : Type} :
    LocalType.Branches P S L → BranchingType.Branches S L
  | .nil => .nil
  | .cons label head tail => .cons label head.erase tail.erase
end

/-- Erasure preserves local well-formedness. -/
theorem LocalType.WellFormed.erase {P S L : Type} {t : LocalType P S L} :
    t.WellFormed → t.erase.WellFormed := by
  have labels_erase : ∀ bs : LocalType.Branches P S L,
    bs.erase.labels = bs.labels := by
    apply LocalType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.erase.labels = bs.labels)
    · trivial
    · intro peer payload next ih
      trivial
    · intro peer payload next ih
      trivial
    · intro peer branches ih
      trivial
    · intro peer branches ih
      trivial
    · rfl
    · intro label head tail ih_head ih_tail
      change (label :: tail.erase.labels) = (label :: tail.labels)
      rw [ih_tail]
  have key : ∀ (t : LocalType P S L) (h : t.WellFormed),
    t.erase.WellFormed := by
    apply LocalType.WellFormed.rec
      (motive_1 := fun t _ => t.erase.WellFormed)
      (motive_2 := fun bs _ => bs.erase.WellFormed)
    · exact BranchingType.WellFormed.end
    · intro peer payload next h ih
      exact BranchingType.WellFormed.send ih
    · intro peer payload next h ih
      exact BranchingType.WellFormed.recv ih
    · intro peer branches h ih
      exact BranchingType.WellFormed.select ih
    · intro peer branches h ih
      exact BranchingType.WellFormed.branch ih
    · exact BranchingType.Branches.WellFormed.nil
    · intro label head tail hmem h1 h2 ih1 ih2
      have hmem2 : label ∉ tail.erase.labels := by
        rw [labels_erase tail]
        exact hmem
      exact BranchingType.Branches.WellFormed.cons hmem2 ih1 ih2
  intro h
  exact key t h

mutual
/-- Every interaction of the global type is between the two named peers. -/
inductive GlobalType.TwoParty {P S L : Type} (p q : P) :
    GlobalType P S L → Prop where
  | end : GlobalType.TwoParty p q .end
  | msg {sender receiver : P} {payload : S} {next : GlobalType P S L} :
    (sender = p ∧ receiver = q) ∨ (sender = q ∧ receiver = p) →
    GlobalType.TwoParty p q next →
      GlobalType.TwoParty p q (.msg sender receiver payload next)
  | choice {sender receiver : P} {branches : GlobalType.Branches P S L} :
    (sender = p ∧ receiver = q) ∨ (sender = q ∧ receiver = p) →
    GlobalType.Branches.TwoParty p q branches →
      GlobalType.TwoParty p q (.choice sender receiver branches)

/-- Every interaction in the branch list is between the two named peers. -/
inductive GlobalType.Branches.TwoParty {P S L : Type} (p q : P) :
    GlobalType.Branches P S L → Prop where
  | nil : GlobalType.Branches.TwoParty p q .nil
  | cons {label : L} {head : GlobalType P S L}
    {tail : GlobalType.Branches P S L} :
    GlobalType.TwoParty p q head →
    GlobalType.Branches.TwoParty p q tail →
    GlobalType.Branches.TwoParty p q (.cons label head tail)
end

/-- Two-party projections erase to dual binary types (project-specific
bridge statement; no source theorem states it). -/
theorem GlobalType.project_erase_dual {P S L : Type} [DecidableEq P]
    [DecidableEq S] [DecidableEq L] {p q : P} (hne : p ≠ q)
    {G : GlobalType P S L} (hG : G.TwoParty p q) :
    ∃ tp tq : LocalType P S L, G.project p = some tp ∧ G.project q = some tq ∧
      tp.erase = tq.erase.dual := by
  have key : ∀ (p q : P), p ≠ q →
    ∀ (G : GlobalType P S L) (hG : G.TwoParty p q),
      ∃ tp tq : LocalType P S L, G.project p = some tp ∧
        G.project q = some tq ∧ tp.erase = tq.erase.dual := by
    intro p q hne
    apply GlobalType.TwoParty.rec
      (motive_1 := fun G _ => ∃ tp tq : LocalType P S L,
        G.project p = some tp ∧ G.project q = some tq ∧
          tp.erase = tq.erase.dual)
      (motive_2 := fun bs _ => ∃ bsp bsq : LocalType.Branches P S L,
        bs.projectBranches p = some bsp ∧
          bs.projectBranches q = some bsq ∧ bsp.erase = bsq.erase.dual)
    · exact ⟨LocalType.end, LocalType.end, rfl, rfl, rfl⟩
    · intro sender receiver payload next hside hnext ih
      cases hside with
      | inl h =>
        have hsender := h.1
        have hreceiver := h.2
        subst sender
        subst receiver
        have ⟨tp_next, tq_next, h_next_p, h_next_q, h_ih⟩ := ih
        have h_proj_p : GlobalType.project (GlobalType.msg p q payload next) p =
          some (LocalType.send q payload tp_next) := by
          change (if p = p then
            (if p = q then none else
              (next.project p).map (LocalType.send q payload)) else _) = _
          rw [ite_eq_left rfl, ite_eq_right hne, h_next_p, Option.map_some]
        have hqp : q ≠ p := fun h => hne h.symm
        have h_proj_q : GlobalType.project (GlobalType.msg p q payload next) q =
          some (LocalType.recv p payload tq_next) := by
          change (if q = p then _ else
            (if q = q then (next.project q).map (LocalType.recv p payload)
              else _)) = _
          rw [ite_eq_right hqp, ite_eq_left rfl, h_next_q, Option.map_some]
        have h_erase : (LocalType.send q payload tp_next).erase =
          (LocalType.recv p payload tq_next).erase.dual := by
          change BranchingType.send payload tp_next.erase =
            BranchingType.send payload (tq_next.erase.dual)
          rw [h_ih]
        exact ⟨_, _, h_proj_p, h_proj_q, h_erase⟩
      | inr h =>
        have hsender := h.1
        have hreceiver := h.2
        subst sender
        subst receiver
        have ⟨tp_next, tq_next, h_next_p, h_next_q, h_ih⟩ := ih
        have hpq : p ≠ q := hne
        have h_proj_p : GlobalType.project (GlobalType.msg q p payload next) p =
          some (LocalType.recv q payload tp_next) := by
          change (if p = q then _ else
            (if p = p then (next.project p).map (LocalType.recv q payload)
              else _)) = _
          rw [ite_eq_right hpq, ite_eq_left rfl, h_next_p, Option.map_some]
        have h_proj_q : GlobalType.project (GlobalType.msg q p payload next) q =
          some (LocalType.send p payload tq_next) := by
          change (if q = q then
            (if q = p then none else
              (next.project q).map (LocalType.send p payload)) else _) = _
          have hqp2 : q ≠ p := fun h => hne h.symm
          rw [ite_eq_left rfl, ite_eq_right hqp2, h_next_q, Option.map_some]
        have h_erase : (LocalType.recv q payload tp_next).erase =
          (LocalType.send p payload tq_next).erase.dual := by
          change BranchingType.recv payload tp_next.erase =
            BranchingType.recv payload (tq_next.erase.dual)
          rw [h_ih]
        exact ⟨_, _, h_proj_p, h_proj_q, h_erase⟩
    · intro sender receiver branches hside hbranches ih
      cases hside with
      | inl h =>
        have hsender := h.1
        have hreceiver := h.2
        subst sender
        subst receiver
        have ⟨bsp, bsq, h_b_p, h_b_q, h_ih⟩ := ih
        have h_proj_p : GlobalType.project (GlobalType.choice p q branches) p =
          some (LocalType.select q bsp) := by
          change (if p = p then
            (if p = q then none else
              (branches.projectBranches p).map (LocalType.select q)) else _) = _
          rw [ite_eq_left rfl, ite_eq_right hne, h_b_p, Option.map_some]
        have hqp : q ≠ p := fun h => hne h.symm
        have h_proj_q : GlobalType.project (GlobalType.choice p q branches) q =
          some (LocalType.branch p bsq) := by
          change (if q = p then _ else
            (if q = q then (branches.projectBranches q).map (LocalType.branch p)
              else _)) = _
          rw [ite_eq_right hqp, ite_eq_left rfl, h_b_q, Option.map_some]
        have h_erase : (LocalType.select q bsp).erase =
          (LocalType.branch p bsq).erase.dual := by
          change BranchingType.select bsp.erase =
            BranchingType.select (bsq.erase.dual)
          rw [h_ih]
        exact ⟨_, _, h_proj_p, h_proj_q, h_erase⟩
      | inr h =>
        have hsender := h.1
        have hreceiver := h.2
        subst sender
        subst receiver
        have ⟨bsp, bsq, h_b_p, h_b_q, h_ih⟩ := ih
        have hpq : p ≠ q := hne
        have h_proj_p : GlobalType.project (GlobalType.choice q p branches) p =
          some (LocalType.branch q bsp) := by
          change (if p = q then _ else
            (if p = p then (branches.projectBranches p).map (LocalType.branch q)
              else _)) = _
          rw [ite_eq_right hpq, ite_eq_left rfl, h_b_p, Option.map_some]
        have h_proj_q : GlobalType.project (GlobalType.choice q p branches) q =
          some (LocalType.select p bsq) := by
          change (if q = q then
            (if q = p then none else
              (branches.projectBranches q).map (LocalType.select p)) else _) = _
          have hqp2 : q ≠ p := fun h => hne h.symm
          rw [ite_eq_left rfl, ite_eq_right hqp2, h_b_q, Option.map_some]
        have h_erase : (LocalType.branch q bsp).erase =
          (LocalType.select p bsq).erase.dual := by
          change BranchingType.branch bsp.erase =
            BranchingType.branch (bsq.erase.dual)
          rw [h_ih]
        exact ⟨_, _, h_proj_p, h_proj_q, h_erase⟩
    · exact ⟨LocalType.Branches.nil, LocalType.Branches.nil, rfl, rfl, rfl⟩
    · intro label head tail hhead htail ih_head ih_tail
      have ⟨tp_hp, tq_hq, h_hp_p, h_hq_q, h_ih_h⟩ := ih_head
      have ⟨bsp_tp, bsq_tq, h_tp_p, h_tq_q, h_ih_t⟩ := ih_tail
      have h_proj_p : GlobalType.Branches.projectBranches
        (GlobalType.Branches.cons label head tail) p =
        some (LocalType.Branches.cons label tp_hp bsp_tp) := by
        change (match head.project p, tail.projectBranches p with
          | some hp, some tp => some (LocalType.Branches.cons label hp tp)
          | _, _ => none) = _
        rw [h_hp_p, h_tp_p]
      have h_proj_q : GlobalType.Branches.projectBranches
        (GlobalType.Branches.cons label head tail) q =
        some (LocalType.Branches.cons label tq_hq bsq_tq) := by
        change (match head.project q, tail.projectBranches q with
          | some hq, some tq => some (LocalType.Branches.cons label hq tq)
          | _, _ => none) = _
        rw [h_hq_q, h_tq_q]
      have h_erase : (LocalType.Branches.cons label tp_hp bsp_tp).erase =
        (LocalType.Branches.cons label tq_hq bsq_tq).erase.dual := by
        change BranchingType.Branches.cons label tp_hp.erase bsp_tp.erase =
          BranchingType.Branches.cons label (tq_hq.erase.dual)
            (bsq_tq.erase.dual)
        rw [h_ih_h, h_ih_t]
      exact ⟨_, _, h_proj_p, h_proj_q, h_erase⟩
  exact key p q hne G hG

end Cslib.SessionTypes
