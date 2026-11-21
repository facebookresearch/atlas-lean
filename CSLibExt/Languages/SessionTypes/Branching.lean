/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Endpoint.FiniteBridge
public import Mathlib.Data.Finmap

/-!
# Binary session types with labelled branching

Finite fragment of Honda, Vasconcelos and Kubo, ESOP 1998, Section 5
(Definitions 5.1-5.2, Figure 1): one abstract payload sort per send and
receive, internal and external labelled choice, and inaction. Excludes
recursion, `⊥`, delegation, tuple payloads and shared sorts. Branch lists
are ordered association lists; only the `WellFormed` distinct-label
fragment represents source brace choices.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

mutual
/-- Finite branching type: `send`/`recv` one sort (Def 5.1 output/input),
`select` internal choice, `branch` external choice, `end` inaction `1`.
Excludes recursion, `⊥`, delegation and tuple payloads. -/
inductive BranchingType (S L : Type) where
  | end : BranchingType S L
  | send (payload : S) (next : BranchingType S L) : BranchingType S L
  | recv (payload : S) (next : BranchingType S L) : BranchingType S L
  | select (branches : BranchingType.Branches S L) : BranchingType S L
  | branch (branches : BranchingType.Branches S L) : BranchingType S L
deriving DecidableEq

/-- Ordered branch association list; only `WellFormed` lists are source choices. -/
inductive BranchingType.Branches (S L : Type) where
  | nil : BranchingType.Branches S L
  | cons (label : L) (head : BranchingType S L)
    (tail : BranchingType.Branches S L) : BranchingType.Branches S L
deriving DecidableEq
end

/-- Association-list entries of a branch list, in order. -/
def BranchingType.Branches.entries {S L : Type}
    (branches : BranchingType.Branches S L) : List (L × BranchingType S L) :=
  match branches with
  | .nil => ([] : List (L × BranchingType S L))
  | .cons label head tail => (label, head) :: tail.entries

/-- Labels of a branch list, in order. -/
def BranchingType.Branches.labels {S L : Type}
    (branches : BranchingType.Branches S L) : List L :=
  branches.entries.map Prod.fst

/-- First match on the raw ordered list, or `none` if absent. -/
def BranchingType.Branches.lookup {S L : Type} [DecidableEq L]
    (branches : BranchingType.Branches S L) (label : L) : Option (BranchingType S L) :=
  match branches with
  | .nil => (none : Option (BranchingType S L))
  | .cons entryLabel head tail =>
    if label = entryLabel then some head else tail.lookup label

mutual
/-- Well-formed types: continuations and branch lists are well formed. -/
inductive BranchingType.WellFormed {S L : Type} : BranchingType S L → Prop where
  | end : BranchingType.WellFormed .end
  | send {payload : S} {next : BranchingType S L} :
    BranchingType.WellFormed next →
      BranchingType.WellFormed (.send payload next)
  | recv {payload : S} {next : BranchingType S L} :
    BranchingType.WellFormed next →
      BranchingType.WellFormed (.recv payload next)
  | select {branches : BranchingType.Branches S L} :
    BranchingType.Branches.WellFormed branches →
      BranchingType.WellFormed (.select branches)
  | branch {branches : BranchingType.Branches S L} :
    BranchingType.Branches.WellFormed branches →
      BranchingType.WellFormed (.branch branches)

/-- Well-formed branch lists: distinct labels, well-formed continuations. -/
inductive BranchingType.Branches.WellFormed {S L : Type} :
    BranchingType.Branches S L → Prop where
  | nil : BranchingType.Branches.WellFormed .nil
  | cons {label : L} {head : BranchingType S L}
    {tail : BranchingType.Branches S L} : label ∉ tail.labels →
    BranchingType.WellFormed head →
    BranchingType.Branches.WellFormed tail →
    BranchingType.Branches.WellFormed (.cons label head tail)
end

/-- Well-formed branch lists have duplicate-free labels. -/
theorem BranchingType.Branches.labels_nodup_of_wellFormed {S L : Type}
    (branches : BranchingType.Branches S L)
    (h : branches.WellFormed) : branches.labels.Nodup := by
  exact BranchingType.Branches.rec (motive_1 := fun _ => True)
    (motive_2 := fun bs => bs.WellFormed → bs.labels.Nodup) trivial
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ => List.nodup_nil)
    (fun l hd tail _ ih2 hw => by cases hw with
      | cons hnotin _ htail =>
        have heq : (BranchingType.Branches.cons l hd tail).labels = l :: tail.labels := rfl
        rw [heq]; exact List.nodup_cons.mpr ⟨hnotin, ih2 htail⟩) branches h

mutual
/-- Def 5.1 co-typing; no `⊥` in this fragment. -/
def BranchingType.dual {S L : Type} : BranchingType S L → BranchingType S L
  | .end => .end
  | .send payload next => .recv payload (BranchingType.dual next)
  | .recv payload next => .send payload (BranchingType.dual next)
  | .select branches => .branch (BranchingType.Branches.dual branches)
  | .branch branches => .select (BranchingType.Branches.dual branches)

/-- Dualize every continuation in a branch list, preserving labels. -/
def BranchingType.Branches.dual {S L : Type} :
    BranchingType.Branches S L → BranchingType.Branches S L
  | .nil => .nil
  | .cons label head tail =>
    .cons label (BranchingType.dual head) (BranchingType.Branches.dual tail)
end

/-- Duality is involutive on branching types. -/
theorem BranchingType.dual_dual {S L : Type} (t : BranchingType S L) :
    t.dual.dual = t := by
  refine BranchingType.rec (motive_1 := fun t => t.dual.dual = t)
    (motive_2 := fun bs => bs.dual.dual = bs) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · rfl
  · intro _ _ ih; simp [BranchingType.dual, ih]
  · intro _ _ ih; simp [BranchingType.dual, ih]
  · intro _ ih; simp [BranchingType.dual, ih]
  · intro _ ih; simp [BranchingType.dual, ih]
  · rfl
  · intro _ _ _ ih1 ih2; simp [BranchingType.Branches.dual, ih1, ih2]

/-- Duality is involutive on branch lists. -/
theorem BranchingType.Branches.dual_dual {S L : Type}
    (branches : BranchingType.Branches S L) : branches.dual.dual = branches := by
  refine BranchingType.Branches.rec (motive_1 := fun t => t.dual.dual = t)
    (motive_2 := fun bs => bs.dual.dual = bs) ?_ ?_ ?_ ?_ ?_ ?_ ?_ branches
  · rfl
  · intro _ _ ih; simp [BranchingType.dual, ih]
  · intro _ _ ih; simp [BranchingType.dual, ih]
  · intro _ ih; simp [BranchingType.dual, ih]
  · intro _ ih; simp [BranchingType.dual, ih]
  · rfl
  · intro _ _ _ ih1 ih2; simp [BranchingType.Branches.dual, ih1, ih2]

/-- Dual of a well-formed type is well formed. -/
theorem BranchingType.WellFormed.dual {S L : Type} (t : BranchingType S L)
    (h : t.WellFormed) : t.dual.WellFormed := by
  have hlab : ∀ bs : BranchingType.Branches S L, bs.dual.labels = bs.labels := by
    intro bs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.dual.labels = bs.labels) ?_ ?_ ?_ ?_ ?_ ?_ ?_ bs
    · trivial
    · intro _ _ _; trivial
    · intro _ _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
    · rfl
    · intro l hd tail _ ih2; simpa [BranchingType.Branches.dual, BranchingType.Branches.entries,
        BranchingType.Branches.labels] using ih2
  refine BranchingType.rec (motive_1 := fun t => t.WellFormed → t.dual.WellFormed)
    (motive_2 := fun bs => bs.WellFormed → bs.dual.WellFormed) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t h
  · intro _; exact BranchingType.WellFormed.end
  · intro _ _ ih hw; cases hw with | send h' => exact BranchingType.WellFormed.recv (ih h')
  · intro _ _ ih hw; cases hw with | recv h' => exact BranchingType.WellFormed.send (ih h')
  · intro _ ih hw; cases hw with | select h' => exact BranchingType.WellFormed.branch (ih h')
  · intro _ ih hw; cases hw with | branch h' => exact BranchingType.WellFormed.select (ih h')
  · intro _; exact BranchingType.Branches.WellFormed.nil
  · intro l hd tail ih1 ih2 hw; cases hw with | cons hn hh ht =>
      exact BranchingType.Branches.WellFormed.cons (by rw [hlab tail]; exact hn) (ih1 hh) (ih2 ht)

/-- Dual of a well-formed branch list is well formed. -/
theorem BranchingType.Branches.WellFormed.dual {S L : Type}
    (branches : BranchingType.Branches S L)
    (h : branches.WellFormed) : branches.dual.WellFormed := by
  have hlab : ∀ bs : BranchingType.Branches S L, bs.dual.labels = bs.labels := by
    intro bs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.dual.labels = bs.labels) ?_ ?_ ?_ ?_ ?_ ?_ ?_ bs
    · trivial
    · intro _ _ _; trivial
    · intro _ _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
    · rfl
    · intro l hd tail _ ih2; simpa [BranchingType.Branches.dual, BranchingType.Branches.entries,
        BranchingType.Branches.labels] using ih2
  refine BranchingType.Branches.rec (motive_1 := fun t => t.WellFormed → t.dual.WellFormed)
    (motive_2 := fun bs => bs.WellFormed → bs.dual.WellFormed) ?_ ?_ ?_ ?_ ?_ ?_ ?_ branches h
  · intro _; exact BranchingType.WellFormed.end
  · intro _ _ ih hw; cases hw with | send h' => exact BranchingType.WellFormed.recv (ih h')
  · intro _ _ ih hw; cases hw with | recv h' => exact BranchingType.WellFormed.send (ih h')
  · intro _ ih hw; cases hw with | select h' => exact BranchingType.WellFormed.branch (ih h')
  · intro _ ih hw; cases hw with | branch h' => exact BranchingType.WellFormed.select (ih h')
  · intro _; exact BranchingType.Branches.WellFormed.nil
  · intro l hd tail ih1 ih2 hw; cases hw with | cons hn hh ht =>
      exact BranchingType.Branches.WellFormed.cons (by rw [hlab tail]; exact hn) (ih1 hh) (ih2 ht)

/-- Embed the payload-free `SessionType` with one passive sort. -/
def BranchingType.ofSessionType {S L : Type} (passive : S)
    (s : SessionType) : BranchingType S L :=
  match s with
  | .end => .end
  | .send next =>
    .send passive (BranchingType.ofSessionType passive next)
  | .recv next =>
    .recv passive (BranchingType.ofSessionType passive next)

/-- Embedding commutes with duality. -/
theorem BranchingType.ofSessionType_dual {S L : Type} (passive : S) (s : SessionType) :
    BranchingType.ofSessionType (L := L) passive s.dual =
      (BranchingType.ofSessionType (L := L) passive s).dual := by
  induction s with
  | «end» => rfl
  | send n ih => simp [BranchingType.ofSessionType,
    BranchingType.dual, SessionType.dual, ih]
  | recv n ih => simp [BranchingType.ofSessionType, BranchingType.dual, SessionType.dual, ih]

/-- Embedded old protocols are well formed. -/
theorem BranchingType.WellFormed.ofSessionType {S L : Type} (passive : S) (s : SessionType) :
    (BranchingType.ofSessionType (L := L) passive s).WellFormed := by
  induction s with
  | «end» => exact BranchingType.WellFormed.end
  | send _ ih => exact BranchingType.WellFormed.send ih
  | recv _ ih => exact BranchingType.WellFormed.recv ih

/-- Embedding at a passive sort is injective. -/
theorem BranchingType.ofSessionType_injective {S L : Type} (passive : S) :
    Function.Injective ((BranchingType.ofSessionType passive) :
      SessionType → BranchingType S L) := by
  intro s1 s2
  induction s1 generalizing s2 with
  | «end» =>
    cases s2 with
    | «end» =>
      intro heq
      rfl
    | send _ =>
      intro heq
      simp [BranchingType.ofSessionType] at heq
    | recv _ =>
      intro heq
      simp [BranchingType.ofSessionType] at heq
  | send n1 ih =>
    cases s2 with
    | «end» =>
      intro heq
      simp [BranchingType.ofSessionType] at heq
    | send n2 =>
      intro heq
      simp only [BranchingType.ofSessionType] at heq
      injection heq with _ h
      exact congrArg SessionType.send (ih h)
    | recv _ =>
      intro heq
      simp [BranchingType.ofSessionType] at heq
  | recv n1 ih =>
    cases s2 with
    | «end» =>
      intro heq
      simp [BranchingType.ofSessionType] at heq
    | send _ =>
      intro heq
      simp [BranchingType.ofSessionType] at heq
    | recv n2 =>
      intro heq
      simp only [BranchingType.ofSessionType] at heq
      injection heq with _ h
      exact congrArg SessionType.recv (ih h)

/-- Partial map to `SessionType`; choices/non-passive sorts give `none`. -/
def BranchingType.toSessionType? {S L : Type} (passive : S) [DecidableEq S]
    (t : BranchingType S L) : Option SessionType :=
  match t with
  | .end => some SessionType.end
  | .send payload next =>
    if payload = passive then
      (BranchingType.toSessionType? passive next).map SessionType.send
    else (none : Option SessionType)
  | .recv payload next =>
    if payload = passive then
      (BranchingType.toSessionType? passive next).map SessionType.recv
    else (none : Option SessionType)
  | .select branches => let _ := branches; (none : Option SessionType)
  | .branch branches => let _ := branches; (none : Option SessionType)

/-- Partial map to `Protocol` via `toSessionType?` and `ofFinite`. -/
def BranchingType.toProtocol? {S L : Type} (passive : S) [DecidableEq S]
    (t : BranchingType S L) : Option Endpoint.Protocol :=
  (BranchingType.toSessionType? passive t).map Endpoint.Protocol.ofFinite

/-- Round trip from old syntax through the embedding. -/
theorem BranchingType.toSessionType?_ofSessionType {S L : Type} (passive : S)
    [DecidableEq S] (s : SessionType) : BranchingType.toSessionType? (L := L) passive
      (BranchingType.ofSessionType (L := L) passive s) = some s := by
  induction s with
  | «end» => rfl
  | send n ih => simp [BranchingType.ofSessionType, BranchingType.toSessionType?, ih]
  | recv n ih => simp [BranchingType.ofSessionType, BranchingType.toSessionType?, ih]

/-- Partial map commutes with duality where defined. -/
theorem BranchingType.toSessionType?_dual {S L : Type} (passive : S)
    [DecidableEq S] (t : BranchingType S L) :
    BranchingType.toSessionType? passive t.dual =
      (BranchingType.toSessionType? passive t).map SessionType.dual := by
  refine BranchingType.rec (motive_1 := fun t => BranchingType.toSessionType? passive t.dual =
      (BranchingType.toSessionType? passive t).map SessionType.dual)
    (motive_2 := fun _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · simp [BranchingType.dual, BranchingType.toSessionType?, SessionType.dual]
  · intro payload next ih; by_cases h : payload = passive
    · simp [BranchingType.dual, BranchingType.toSessionType?, h, ih]
      cases hX : BranchingType.toSessionType? passive next with
      | none => simp [hX]
      | some s => simp [hX, SessionType.dual]
    · simp [BranchingType.dual, BranchingType.toSessionType?, h]
  · intro payload next ih; by_cases h : payload = passive
    · simp [BranchingType.dual, BranchingType.toSessionType?, h, ih]
      cases hX : BranchingType.toSessionType? passive next with
      | none => simp [hX]
      | some s => simp [hX, SessionType.dual]
    · simp [BranchingType.dual, BranchingType.toSessionType?, h]
  · intro _ _; rfl
  · intro _ _; rfl
  · trivial
  · intro _ _ _ _ _; trivial

/-- Send with non-passive head sort is rejected. -/
theorem BranchingType.toSessionType?_send_of_ne {S L : Type} (passive : S)
    [DecidableEq S] (payload : S) (next : BranchingType S L)
    (h : payload ≠ passive) :
    BranchingType.toSessionType? passive (.send payload next) =
      (none : Option SessionType) := by
  simp [BranchingType.toSessionType?, h]

/-- Receive with non-passive head sort is rejected. -/
theorem BranchingType.toSessionType?_recv_of_ne {S L : Type} (passive : S)
    [DecidableEq S] (payload : S) (next : BranchingType S L)
    (h : payload ≠ passive) :
    BranchingType.toSessionType? passive (.recv payload next) =
      (none : Option SessionType) := by
  simp [BranchingType.toSessionType?, h]

/-- Triangle through `Protocol.ofFinite` on embedded old syntax. -/
theorem BranchingType.toProtocol?_ofSessionType {S L : Type} (passive : S)
    [DecidableEq S] (s : SessionType) : BranchingType.toProtocol? (L := L) passive
      (BranchingType.ofSessionType (L := L) passive s) = some (Endpoint.Protocol.ofFinite s) :=
  by simp [BranchingType.toProtocol?, BranchingType.toSessionType?_ofSessionType]

/-- Protocol map commutes with duality where defined. -/
theorem BranchingType.toProtocol?_dual {S L : Type} (passive : S)
    [DecidableEq S] (t : BranchingType S L) :
    BranchingType.toProtocol? passive t.dual =
      (BranchingType.toProtocol? passive t).map Endpoint.Protocol.dual :=
  by
    simp only [BranchingType.toProtocol?, BranchingType.toSessionType?_dual, Option.map_map]
    cases hX : BranchingType.toSessionType? passive t with
    | none => simp [hX]
    | some s => simp [hX, Endpoint.Protocol.ofFinite_dual]

/-- Type-level actions: send, receive, and labelled select/branch. -/
inductive BranchingType.Action (L : Type) where
  | send : BranchingType.Action L
  | recv : BranchingType.Action L
  | select (label : L) : BranchingType.Action L
  | branch (label : L) : BranchingType.Action L
deriving DecidableEq

/-- Dual actions swap send/receive and select/branch. -/
def BranchingType.Action.dual {L : Type} : BranchingType.Action L →
    BranchingType.Action L
  | .send => .recv
  | .recv => .send
  | .select label => .branch label
  | .branch label => .select label

/-- Type advancement by one action; choice uses entries membership. -/
inductive BranchingType.Advances {S L : Type} :
    BranchingType S L → BranchingType.Action L → BranchingType S L → Prop where
  | send {payload : S} {next : BranchingType S L} :
    BranchingType.Advances (BranchingType.send payload next)
      BranchingType.Action.send next
  | recv {payload : S} {next : BranchingType S L} :
    BranchingType.Advances (BranchingType.recv payload next)
      BranchingType.Action.recv next
  | select {branches : BranchingType.Branches S L} {label : L}
    {next : BranchingType S L} :
    (label, next) ∈ branches.entries →
      BranchingType.Advances (BranchingType.select branches)
        (BranchingType.Action.select label) next
  | branch {branches : BranchingType.Branches S L} {label : L}
    {next : BranchingType S L} :
    (label, next) ∈ branches.entries →
      BranchingType.Advances (BranchingType.branch branches)
        (BranchingType.Action.branch label) next

/-- Dual types advance by dual actions to dual continuations. -/
theorem BranchingType.Advances.dual {S L : Type} (t : BranchingType S L)
    (act : BranchingType.Action L) (u : BranchingType S L)
    (h : BranchingType.Advances t act u) :
    BranchingType.Advances t.dual act.dual u.dual := by
  have hent : ∀ bs : BranchingType.Branches S L, bs.dual.entries =
      bs.entries.map (fun p : L × BranchingType S L => (p.1, p.2.dual)) := fun bs =>
    BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.dual.entries =
        bs.entries.map (fun p : L × BranchingType S L => (p.1, p.2.dual))) trivial
      (fun _ _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ => trivial)
      (fun _ _ => trivial) rfl
      (fun l hd tail _ ih2 => by simp [BranchingType.Branches.dual,
        BranchingType.Branches.entries, ih2]) bs
  cases h with
  | send => exact BranchingType.Advances.recv
  | recv => exact BranchingType.Advances.send
  | select m => exact BranchingType.Advances.branch (by rw [hent _]; exact List.mem_map_of_mem m)
  | branch m => exact BranchingType.Advances.select (by rw [hent _]; exact List.mem_map_of_mem m)

/-- Advancement preserves well-formedness. -/
theorem BranchingType.Advances.wellFormed {S L : Type} (t : BranchingType S L)
    (act : BranchingType.Action L) (u : BranchingType S L)
    (hw : t.WellFormed) (h : BranchingType.Advances t act u) :
    u.WellFormed := by
  have hmemWf : ∀ bs : BranchingType.Branches S L, bs.WellFormed →
      ∀ p : L × BranchingType S L, p ∈ bs.entries → p.2.WellFormed := by
    intro bs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun bs => bs.WellFormed →
        ∀ p : L × BranchingType S L, p ∈ bs.entries → p.2.WellFormed) ?_ ?_ ?_ ?_ ?_ ?_ ?_ bs
    · trivial
    · intro _ _ _; trivial
    · intro _ _ _; trivial
    · intro _ _; trivial
    · intro _ _; trivial
    · intro _ _ hmem; simp [BranchingType.Branches.entries] at hmem
    · intro l hd tail _ ih2 hw p hmem; cases hw with | cons _ hhead htail =>
        simp only [BranchingType.Branches.entries, List.mem_cons] at hmem; cases hmem with
        | inl heq => rw [heq]; exact hhead
        | inr hm => exact ih2 htail p hm
  cases h with
  | send => cases hw with | send h' => exact h'
  | recv => cases hw with | recv h' => exact h'
  | select hmem => cases hw with | select hwbs => exact hmemWf _ hwbs _ hmem
  | branch hmem => cases hw with | branch hwbs => exact hmemWf _ hwbs _ hmem

/-- Finite context: `Nat`-keyed obligations; absence means no obligation. -/
abbrev BranchingContext (S L : Type) := Finmap (fun _ : Nat => BranchingType S L)

namespace BranchingContext
/-- Dualize every obligation, preserving keys. -/
def dual {S L : Type} (Γ : BranchingContext S L) : BranchingContext S L :=
  { entries := Γ.entries.map (fun x => ⟨x.1, x.2.dual⟩)
    nodupKeys := by
      apply Multiset.nodup_keys.mp
      have h : Γ.entries.keys.Nodup := Γ.nodupKeys.nodup_keys
      simpa [Multiset.keys, Multiset.map_map, Function.comp_def] using h }

/-- Disjoint ownership split: whole is the union with disjoint sides. -/
def Split {S L : Type} (Γ Δ Θ : BranchingContext S L) : Prop :=
  Γ = Δ ∪ Θ ∧ Finmap.Disjoint Δ Θ

/-- Advance channel `a` by one action, updating its obligation. -/
def Advances {S L : Type} (Γ : BranchingContext S L) (a : Nat)
    (act : BranchingType.Action L) (Δ : BranchingContext S L) : Prop :=
  ∃ t u, Γ.lookup a = some t ∧ BranchingType.Advances t act u ∧
    Δ = Γ.insert a u

/-- Dual preserves domain membership. -/
theorem mem_dual {S L : Type} (Γ : BranchingContext S L) (a : Nat) :
    a ∈ BranchingContext.dual Γ ↔ a ∈ Γ := by
  simp [Finmap.mem_def, BranchingContext.dual, Multiset.keys, Multiset.map_map]
/-- Lookup through dual dualizes the value. -/
theorem lookup_dual {S L : Type} (Γ : BranchingContext S L) (a : Nat) :
    (BranchingContext.dual Γ).lookup a =
      (Γ.lookup a).map BranchingType.dual := by
  cases h : Γ.lookup a with
  | none => simp [Finmap.lookup_eq_none.mpr (by rw [mem_dual]; exact Finmap.lookup_eq_none.mp h)]
  | some t =>
    have hmem := Finmap.lookup_eq_some_iff.mp h
    have hmem' : Sigma.mk a t.dual ∈ (BranchingContext.dual Γ).entries := by
      simp only [BranchingContext.dual]
      exact Multiset.mem_map_of_mem (fun x : Sigma (fun _ : Nat => BranchingType S L) =>
        (Sigma.mk x.1 x.2.dual : Sigma (fun _ : Nat => BranchingType S L))) hmem
    have hdual := Finmap.lookup_eq_some_iff.mpr hmem'; simp [hdual, h]
/-- Dual preserves disjointness. -/
theorem disjoint_dual {S L : Type} (Δ Θ : BranchingContext S L)
    (h : Finmap.Disjoint Δ Θ) :
    Finmap.Disjoint (BranchingContext.dual Δ)
      (BranchingContext.dual Θ) := by
  exact fun x hx1 hx2 => h x ((mem_dual _ _).mp hx1) ((mem_dual _ _).mp hx2)
/-- Dual preserves ownership splits. -/
theorem Split.dual {S L : Type} (Γ Δ Θ : BranchingContext S L)
    (h : Split Γ Δ Θ) :
    Split (BranchingContext.dual Γ) (BranchingContext.dual Δ)
      (BranchingContext.dual Θ) := by
  have hunion : BranchingContext.dual (Δ ∪ Θ) =
      BranchingContext.dual Δ ∪ BranchingContext.dual Θ := by
    apply Finmap.ext_lookup; intro x; by_cases hx : x ∈ Δ
    · have hx' : x ∈ BranchingContext.dual Δ := (mem_dual _ _).mpr hx
      simp [lookup_dual, Finmap.lookup_union_left hx, Finmap.lookup_union_left hx']
    · have hx' : x ∉ BranchingContext.dual Δ := by rw [mem_dual]; exact hx
      simp [lookup_dual, Finmap.lookup_union_right hx, Finmap.lookup_union_right hx']
  have heq : Γ = Δ ∪ Θ := h.1; have hdisj : Finmap.Disjoint Δ Θ := h.2; constructor
  · rw [heq, hunion]
  · exact disjoint_dual _ _ hdisj
/-- Advancement leaves other channels unchanged. -/
theorem Advances.lookup_of_ne {S L : Type} (Γ Δ : BranchingContext S L)
    (a b : Nat) (act : BranchingType.Action L)
    (h : Advances Γ a act Δ) (hne : b ≠ a) :
    Δ.lookup b = Γ.lookup b := by
  simp only [Advances] at h; obtain ⟨t, u, _, _, heq⟩ := h
  rw [heq]; exact Finmap.lookup_insert_of_ne _ hne
/-- Advancement preserves disjointness on the left. -/
theorem Advances.disjoint_left {S L : Type} (Γ Γ' Θ : BranchingContext S L)
    (a : Nat) (act : BranchingType.Action L)
    (hdisj : Finmap.Disjoint Γ Θ) (h : Advances Γ a act Γ') :
    Finmap.Disjoint Γ' Θ := by
  simp only [Advances] at h; obtain ⟨t, u, hlook, _, heq⟩ := h
  have ha : a ∈ Γ := Finmap.mem_of_lookup_eq_some hlook
  have h' : ∀ x : Nat, x ∈ Γ → x ∈ Θ → False := hdisj
  change ∀ x : Nat, x ∈ Γ' → x ∈ Θ → False; intro x hx1 hx2; rw [heq, Finmap.mem_insert] at hx1
  cases hx1 with | inl heq' => rw [heq'] at hx2; exact h' a ha hx2 | inr hmem => exact h' x hmem hx2
/-- Advancing the left side of a split advances the whole. -/
theorem Split.advance_left {S L : Type} (Γ Δ Δ' Θ : BranchingContext S L)
    (a : Nat) (act : BranchingType.Action L) (h : Split Γ Δ Θ)
    (hadv : Advances Δ a act Δ') :
    Advances Γ a act (Δ' ∪ Θ) ∧ Split (Δ' ∪ Θ) Δ' Θ := by
  have hadv0 := hadv; simp only [Advances] at hadv; obtain ⟨t, u, hlook, hadv_t, heq'⟩ := hadv
  have heq : Γ = Δ ∪ Θ := h.1; have hdisj : Finmap.Disjoint Δ Θ := h.2
  have ha : a ∈ Δ := Finmap.mem_of_lookup_eq_some hlook
  have hlookΓ : Γ.lookup a = some t := by rw [heq, Finmap.lookup_union_left ha]; exact hlook
  have htarget : Δ' ∪ Θ = Γ.insert a u := by rw [heq, Finmap.insert_union, ←heq']
  constructor
  · exact ⟨t, u, hlookΓ, hadv_t, htarget⟩
  · exact ⟨rfl, Advances.disjoint_left _ _ _ _ _ hdisj hadv0⟩
/-- Dual contexts advance by dual actions. -/
theorem Advances.dual {S L : Type} (Γ Δ : BranchingContext S L) (a : Nat)
    (act : BranchingType.Action L) (h : Advances Γ a act Δ) :
    Advances (BranchingContext.dual Γ) a act.dual
      (BranchingContext.dual Δ) := by
  have hins : ∀ (Γ : BranchingContext S L) (a : Nat) (u : BranchingType S L),
      BranchingContext.dual (Γ.insert a u) =
      (BranchingContext.dual Γ).insert a u.dual := fun Γ a u => by
    apply Finmap.ext_lookup; intro x; by_cases hx : x = a
    · subst hx; simp [lookup_dual, Finmap.lookup_insert]
    · simp [lookup_dual, Finmap.lookup_insert_of_ne _ hx]
  simp only [Advances] at h; obtain ⟨t, u, hlook, hadv_t, heq⟩ := h
  have hlook' : (BranchingContext.dual Γ).lookup a = some t.dual := by simp [lookup_dual, hlook]
  have hadv' := BranchingType.Advances.dual _ _ _ hadv_t; have heq' : BranchingContext.dual Δ =
      (BranchingContext.dual Γ).insert a u.dual := by rw [heq, hins]
  exact ⟨t.dual, u.dual, hlook', hadv', heq'⟩

end BranchingContext

end Cslib.SessionTypes
