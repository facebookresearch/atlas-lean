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

Finite fragment of the session types of Honda, Vasconcelos and Kubo, ESOP 1998,
Definition 5.1, with its co-type clauses: send and receive of one payload from an
abstract sort type `S`, internal and external choice over labels `L`, and inaction
`1` (`end`). Excludes recursion, the type `⊥` (a channel already composed with its
peer), delegation, tuple payloads, the sort grammar, and every process typing rule
of Figure 1. `BranchingContext` follows the paragraph after Definition 5.1: a typing
is a finite partial map from channels to types.

Project-specific, not from the source: `BranchingType.Advances` (one-step type
advancement) and `BranchingContext.Split` (union of contexts with disjoint domains,
which is not the compatible-map composition of Definition 5.2).

Branch lists are ordered association lists, so `=` and the derived `DecidableEq` are
syntactic and order-sensitive. A source brace choice is a `WellFormed` (distinct-label)
list up to `BranchingType.PermEquiv`, which reorders branches at any depth.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

mutual
/-- Finite branching type: `send`/`recv` one sort (Def 5.1 output/input),
`select` internal choice, `branch` external choice, `end` inaction `1`.
Excludes recursion, the type `⊥`, delegation and tuple payloads. Equality is
syntactic; compare choices with `PermEquiv`. -/
inductive BranchingType (S L : Type) where
  | end : BranchingType S L
  | send (payload : S) (next : BranchingType S L) : BranchingType S L
  | recv (payload : S) (next : BranchingType S L) : BranchingType S L
  | select (branches : BranchingType.Branches S L) : BranchingType S L
  | branch (branches : BranchingType.Branches S L) : BranchingType S L
deriving DecidableEq

/-- Ordered branch association list. A source choice is a `WellFormed` list up to
`PermEquiv`; branch order is not significant there. -/
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
/-- Def 5.1 co-type; the type `⊥`, which has no co-type, is not in this fragment. -/
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

mutual
/-- One reordering step on branching types: a step in a send or recv continuation,
or in the branch list of a select or branch. -/
inductive BranchingType.SwapStep {S L : Type} :
    BranchingType S L → BranchingType S L → Prop where
  /-- Step inside a send continuation; the payload is fixed. -/
  | send {payload : S} {next next' : BranchingType S L} :
    BranchingType.SwapStep next next' →
      BranchingType.SwapStep (.send payload next) (.send payload next')
  /-- Step inside a recv continuation; the payload is fixed. -/
  | recv {payload : S} {next next' : BranchingType S L} :
    BranchingType.SwapStep next next' →
      BranchingType.SwapStep (.recv payload next) (.recv payload next')
  /-- Step inside the branch list of a select. -/
  | select {branches branches' : BranchingType.Branches S L} :
    BranchingType.Branches.SwapStep branches branches' →
      BranchingType.SwapStep (.select branches) (.select branches')
  /-- Step inside the branch list of a branch. -/
  | branch {branches branches' : BranchingType.Branches S L} :
    BranchingType.Branches.SwapStep branches branches' →
      BranchingType.SwapStep (.branch branches) (.branch branches')

/-- One reordering step on branch lists: swap the first two entries with distinct
labels, or step inside the head continuation or the tail. -/
inductive BranchingType.Branches.SwapStep {S L : Type} :
    BranchingType.Branches S L → BranchingType.Branches S L → Prop where
  /-- Swap the first two entries when their labels differ. -/
  | swap {label1 label2 : L} {head1 head2 : BranchingType S L}
    {tail : BranchingType.Branches S L} :
    label1 ≠ label2 →
      BranchingType.Branches.SwapStep
        (.cons label1 head1 (.cons label2 head2 tail))
        (.cons label2 head2 (.cons label1 head1 tail))
  /-- Step inside the head continuation; head label and tail are fixed. -/
  | head {label : L} {head head' : BranchingType S L}
    {tail : BranchingType.Branches S L} :
    BranchingType.SwapStep head head' →
      BranchingType.Branches.SwapStep
        (.cons label head tail) (.cons label head' tail)
  /-- Step inside the tail; the head entry is fixed. -/
  | tail {label : L} {head : BranchingType S L}
    {tail tail' : BranchingType.Branches S L} :
    BranchingType.Branches.SwapStep tail tail' →
      BranchingType.Branches.SwapStep
        (.cons label head tail) (.cons label head tail')
end

/-- Source equality of brace choices; reorders distinct-label branches at any depth. -/
def BranchingType.PermEquiv {S L : Type}
    (t u : BranchingType S L) : Prop :=
  Relation.EqvGen BranchingType.SwapStep t u

/-- Source equality of brace choices; reorders distinct-label branches at any depth. -/
def BranchingType.Branches.PermEquiv {S L : Type}
    (bs cs : BranchingType.Branches S L) : Prop :=
  Relation.EqvGen BranchingType.Branches.SwapStep bs cs

/-- PermEquiv on types is reflexive. -/
theorem BranchingType.PermEquiv.refl {S L : Type}
    (t : BranchingType S L) : BranchingType.PermEquiv t t := by
  exact Relation.EqvGen.refl _

/-- PermEquiv on types is symmetric. -/
theorem BranchingType.PermEquiv.symm {S L : Type}
    {t u : BranchingType S L} :
    BranchingType.PermEquiv t u → BranchingType.PermEquiv u t := by
  intro h
  exact Relation.EqvGen.symm _ _ h

/-- PermEquiv on types is transitive. -/
theorem BranchingType.PermEquiv.trans {S L : Type}
    {t u v : BranchingType S L} :
    BranchingType.PermEquiv t u → BranchingType.PermEquiv u v →
      BranchingType.PermEquiv t v := by
  intro h1 h2
  exact Relation.EqvGen.trans _ _ _ h1 h2

/-- PermEquiv on branch lists is reflexive. -/
theorem BranchingType.Branches.PermEquiv.refl {S L : Type}
    (branches : BranchingType.Branches S L) :
    BranchingType.Branches.PermEquiv branches branches := by
  exact Relation.EqvGen.refl _

/-- PermEquiv on branch lists is symmetric. -/
theorem BranchingType.Branches.PermEquiv.symm {S L : Type}
    {bs cs : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv bs cs →
      BranchingType.Branches.PermEquiv cs bs := by
  intro h
  exact Relation.EqvGen.symm _ _ h

/-- PermEquiv on branch lists is transitive. -/
theorem BranchingType.Branches.PermEquiv.trans {S L : Type}
    {bs cs ds : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv bs cs →
      BranchingType.Branches.PermEquiv cs ds →
        BranchingType.Branches.PermEquiv bs ds := by
  intro h1 h2
  exact Relation.EqvGen.trans _ _ _ h1 h2

/-- PermEquiv is congruent under send. -/
theorem BranchingType.PermEquiv.send {S L : Type}
    {payload : S} {next next' : BranchingType S L} :
    BranchingType.PermEquiv next next' →
      BranchingType.PermEquiv (.send payload next)
        (.send payload next') := by
  intro h
  induction h with
  | rel x y hstep =>
    exact Relation.EqvGen.rel _ _ (BranchingType.SwapStep.send hstep)
  | refl x => exact BranchingType.PermEquiv.refl _
  | symm x y _ ih => exact BranchingType.PermEquiv.symm ih
  | trans x y z _ _ ih1 ih2 =>
    exact BranchingType.PermEquiv.trans ih1 ih2

/-- PermEquiv is congruent under recv. -/
theorem BranchingType.PermEquiv.recv {S L : Type}
    {payload : S} {next next' : BranchingType S L} :
    BranchingType.PermEquiv next next' →
      BranchingType.PermEquiv (.recv payload next)
        (.recv payload next') := by
  intro h
  induction h with
  | rel x y hstep =>
    exact Relation.EqvGen.rel _ _ (BranchingType.SwapStep.recv hstep)
  | refl x => exact BranchingType.PermEquiv.refl _
  | symm x y _ ih => exact BranchingType.PermEquiv.symm ih
  | trans x y z _ _ ih1 ih2 =>
    exact BranchingType.PermEquiv.trans ih1 ih2

/-- PermEquiv is congruent under select. -/
theorem BranchingType.PermEquiv.select {S L : Type}
    {branches branches' : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv branches branches' →
      BranchingType.PermEquiv (.select branches)
        (.select branches') := by
  intro h
  induction h with
  | rel x y hstep =>
    exact Relation.EqvGen.rel _ _ (BranchingType.SwapStep.select hstep)
  | refl x => exact BranchingType.PermEquiv.refl _
  | symm x y _ ih => exact BranchingType.PermEquiv.symm ih
  | trans x y z _ _ ih1 ih2 =>
    exact BranchingType.PermEquiv.trans ih1 ih2

/-- PermEquiv is congruent under branch. -/
theorem BranchingType.PermEquiv.branch {S L : Type}
    {branches branches' : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv branches branches' →
      BranchingType.PermEquiv (.branch branches)
        (.branch branches') := by
  intro h
  induction h with
  | rel x y hstep =>
    exact Relation.EqvGen.rel _ _ (BranchingType.SwapStep.branch hstep)
  | refl x => exact BranchingType.PermEquiv.refl _
  | symm x y _ ih => exact BranchingType.PermEquiv.symm ih
  | trans x y z _ _ ih1 ih2 =>
    exact BranchingType.PermEquiv.trans ih1 ih2

/-- Branch list PermEquiv is congruent under cons. -/
theorem BranchingType.Branches.PermEquiv.cons {S L : Type}
    {label : L} {head head' : BranchingType S L}
    {tail tail' : BranchingType.Branches S L} :
    BranchingType.PermEquiv head head' →
      BranchingType.Branches.PermEquiv tail tail' →
        BranchingType.Branches.PermEquiv (.cons label head tail)
          (.cons label head' tail') := by
  intro hh ht
  have keyH : ∀ {a b : BranchingType S L},
      BranchingType.PermEquiv a b →
        BranchingType.Branches.PermEquiv
          (.cons label a tail) (.cons label b tail) := by
    intro a b hab
    induction hab with
    | rel x y hstep =>
      exact Relation.EqvGen.rel _ _
        (BranchingType.Branches.SwapStep.head hstep)
    | refl x => exact BranchingType.Branches.PermEquiv.refl _
    | symm x y _ ih => exact BranchingType.Branches.PermEquiv.symm ih
    | trans x y z _ _ ih1 ih2 =>
      exact BranchingType.Branches.PermEquiv.trans ih1 ih2
  have keyT : ∀ {t t' : BranchingType.Branches S L},
      BranchingType.Branches.PermEquiv t t' →
        BranchingType.Branches.PermEquiv
          (.cons label head' t) (.cons label head' t') := by
    intro t t' htt
    induction htt with
    | rel x y hstep =>
      exact Relation.EqvGen.rel _ _
        (BranchingType.Branches.SwapStep.tail hstep)
    | refl x => exact BranchingType.Branches.PermEquiv.refl _
    | symm x y _ ih => exact BranchingType.Branches.PermEquiv.symm ih
    | trans x y z _ _ ih1 ih2 =>
      exact BranchingType.Branches.PermEquiv.trans ih1 ih2
  exact BranchingType.Branches.PermEquiv.trans (keyH hh) (keyT ht)

/-- Duplicate-free label lists with permuted entries are PermEquiv. -/
theorem BranchingType.Branches.PermEquiv.of_perm {S L : Type}
    {bs cs : BranchingType.Branches S L} :
    bs.labels.Nodup → cs.labels.Nodup →
      List.Perm bs.entries cs.entries →
        BranchingType.Branches.PermEquiv bs cs := by
  have bubble : ∀ (cs : BranchingType.Branches S L) (l : L)
      (x : BranchingType S L),
      (l, x) ∈ cs.entries → cs.labels.Nodup →
        ∃ cs', BranchingType.Branches.PermEquiv cs
          (BranchingType.Branches.cons l x cs') ∧
          List.Perm cs.entries ((l, x) :: cs'.entries) := by
    intro cs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun cs => ∀ (l : L) (x : BranchingType S L),
        (l, x) ∈ cs.entries → cs.labels.Nodup →
          ∃ cs', BranchingType.Branches.PermEquiv cs
            (BranchingType.Branches.cons l x cs') ∧
            List.Perm cs.entries ((l, x) :: cs'.entries))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ cs
    · exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro l x hmem hnodup
      simp only [BranchingType.Branches.entries, List.not_mem_nil] at hmem
    · intro l' x' t' _ ih l x hmem hnodup
      simp only [BranchingType.Branches.entries, List.mem_cons,
        Prod.mk.injEq] at hmem
      have hlab : (BranchingType.Branches.cons l' x' t').labels =
        l' :: t'.labels := rfl
      rw [hlab] at hnodup
      obtain ⟨hnotin, hntail⟩ := List.nodup_cons.mp hnodup
      cases hmem with
      | inl heq =>
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨t', BranchingType.Branches.PermEquiv.refl _,
          List.Perm.refl _⟩
      | inr hmem2 =>
        obtain ⟨u, hu, hup⟩ := ih l x hmem2 hntail
        have hmem_lbl : l ∈ t'.labels :=
          List.mem_map_of_mem (f := Prod.fst) hmem2
        have hne : l' ≠ l := by
          intro heq
          rw [heq] at hnotin
          exact hnotin hmem_lbl
        have hperm : BranchingType.Branches.PermEquiv
            (BranchingType.Branches.cons l' x' t')
            (BranchingType.Branches.cons l x
              (BranchingType.Branches.cons l' x' u)) :=
          BranchingType.Branches.PermEquiv.trans
            (BranchingType.Branches.PermEquiv.cons
              (BranchingType.PermEquiv.refl x') hu)
            (Relation.EqvGen.rel _ _
              (BranchingType.Branches.SwapStep.swap hne))
        have hentries : List.Perm
            (BranchingType.Branches.cons l' x' t').entries
            ((l, x) ::
              (BranchingType.Branches.cons l' x' u).entries) :=
          (List.Perm.cons _ hup).trans (List.Perm.swap _ _ _)
        exact ⟨BranchingType.Branches.cons l' x' u, hperm, hentries⟩
  intro hnb hnc hp
  refine BranchingType.Branches.rec (motive_1 := fun _ => True)
    (motive_2 := fun bs => ∀ cs : BranchingType.Branches S L,
      bs.labels.Nodup → cs.labels.Nodup →
        List.Perm bs.entries cs.entries →
          BranchingType.Branches.PermEquiv bs cs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ bs cs hnb hnc hp
  · exact True.intro
  · intro _ _ _; exact True.intro
  · intro _ _ _; exact True.intro
  · intro _ _; exact True.intro
  · intro _ _; exact True.intro
  · intro cs hnb hnc hp
    have hempty : cs.entries = [] := List.Perm.eq_nil hp.symm
    cases cs with
    | nil => exact BranchingType.Branches.PermEquiv.refl _
    | cons l x t =>
      simp only [BranchingType.Branches.entries] at hempty
      cases hempty
  · intro label head tail _ ih cs hnb hnc hp
    have hmem : (label, head) ∈ cs.entries :=
      hp.subset (by
        simp only [BranchingType.Branches.entries, List.mem_cons]
        exact Or.inl True.intro)
    obtain ⟨cs', hcs, hup⟩ := bubble cs label head hmem hnc
    have htail : List.Perm tail.entries cs'.entries :=
      List.Perm.cons_inv (hp.trans hup)
    have hlab_bs : (BranchingType.Branches.cons label head tail).labels =
      label :: tail.labels := rfl
    rw [hlab_bs] at hnb
    have hntail : tail.labels.Nodup := (List.nodup_cons.mp hnb).2
    have hlab_perm : List.Perm cs.labels (label :: cs'.labels) :=
      List.Perm.map Prod.fst hup
    have hnod_cons : (label :: cs'.labels).Nodup :=
      (List.Perm.nodup_iff hlab_perm).mp hnc
    have hntail_cs' : cs'.labels.Nodup :=
      (List.nodup_cons.mp hnod_cons).2
    have htail_equiv : BranchingType.Branches.PermEquiv tail cs' :=
      ih cs' hntail hntail_cs' htail
    have hcons_equiv : BranchingType.Branches.PermEquiv
        (BranchingType.Branches.cons label head tail)
        (BranchingType.Branches.cons label head cs') :=
      BranchingType.Branches.PermEquiv.cons
        (BranchingType.PermEquiv.refl head) htail_equiv
    exact BranchingType.Branches.PermEquiv.trans hcons_equiv
      (BranchingType.Branches.PermEquiv.symm hcs)

/-- For well-formed lists, PermEquiv iff labels permute and lookups agree. -/
theorem BranchingType.Branches.PermEquiv.iff_lookup {S L : Type}
    [DecidableEq L] {bs cs : BranchingType.Branches S L} :
    bs.WellFormed → cs.WellFormed →
      (BranchingType.Branches.PermEquiv bs cs ↔
        List.Perm bs.labels cs.labels ∧
          ∀ label : L, Option.Rel BranchingType.PermEquiv
            (bs.lookup label) (cs.lookup label)) := by
  have labels_perm_local : ∀ {bs cs : BranchingType.Branches S L},
      BranchingType.Branches.PermEquiv bs cs →
        List.Perm bs.labels cs.labels := by
    intro bs cs h
    have step_labels : ∀ {bs cs : BranchingType.Branches S L},
        BranchingType.Branches.SwapStep bs cs →
          List.Perm bs.labels cs.labels := by
      intro bs cs hstep
      refine BranchingType.Branches.SwapStep.rec
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun bs cs _ => List.Perm bs.labels cs.labels)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro l1 l2 h1 h2 t _hne
        change List.Perm (l1 :: l2 :: t.labels) (l2 :: l1 :: t.labels)
        exact List.Perm.swap _ _ _
      · intro lb hd hd' tail _h _ih
        change List.Perm (lb :: tail.labels) (lb :: tail.labels)
        exact List.Perm.refl _
      · intro lb hd tail tail' _h ih
        change List.Perm (lb :: tail.labels) (lb :: tail'.labels)
        exact List.Perm.cons _ ih
    induction h with
    | rel x y hstep => exact step_labels hstep
    | refl x => exact List.Perm.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have lookup_rel_local : ∀ {bs cs : BranchingType.Branches S L} (l : L),
      BranchingType.Branches.PermEquiv bs cs →
        Option.Rel BranchingType.PermEquiv (bs.lookup l)
          (cs.lookup l) := by
    intro bs cs l h
    have step_lookup : ∀ {bs cs : BranchingType.Branches S L},
        BranchingType.Branches.SwapStep bs cs →
          Option.Rel BranchingType.PermEquiv (bs.lookup l)
            (cs.lookup l) := by
      intro bs cs hstep
      refine BranchingType.Branches.SwapStep.rec
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun bs cs _ => Option.Rel BranchingType.PermEquiv
          (bs.lookup l) (cs.lookup l)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro l1 l2 h1 h2 t hne
        by_cases e1 : l = l1
        · by_cases e2 : l = l2
          · exact absurd (e1.symm.trans e2) hne
          · simp only [BranchingType.Branches.lookup, ite_eq_left e1, ite_eq_right e2]
            exact Option.Rel.some (BranchingType.PermEquiv.refl h1)
        · by_cases e2 : l = l2
          · simp only [BranchingType.Branches.lookup, ite_eq_right e1, ite_eq_left e2]
            exact Option.Rel.some (BranchingType.PermEquiv.refl h2)
          · simp only [BranchingType.Branches.lookup, ite_eq_right e1, ite_eq_right e2]
            cases ht : t.lookup l with
            | none => exact Option.Rel.none
            | some v =>
              exact Option.Rel.some (BranchingType.PermEquiv.refl v)
      · intro lb hd hd' tail h _ih
        by_cases e : l = lb
        · simp only [BranchingType.Branches.lookup, ite_eq_left e]
          exact Option.Rel.some (Relation.EqvGen.rel _ _ h)
        · simp only [BranchingType.Branches.lookup, ite_eq_right e]
          cases ht : tail.lookup l with
          | none => exact Option.Rel.none
          | some v =>
            exact Option.Rel.some (BranchingType.PermEquiv.refl v)
      · intro lb hd tail tail' _h ih
        by_cases e : l = lb
        · simp only [BranchingType.Branches.lookup, ite_eq_left e]
          exact Option.Rel.some (BranchingType.PermEquiv.refl hd)
        · simp only [BranchingType.Branches.lookup, ite_eq_right e]
          exact ih
    induction h with
    | rel x y hstep => exact step_lookup hstep
    | refl x =>
      cases hx : x.lookup l with
      | none => exact Option.Rel.none
      | some v => exact Option.Rel.some (BranchingType.PermEquiv.refl v)
    | symm x y _ ih =>
      cases hx : x.lookup l with
      | none =>
        cases hy : y.lookup l with
        | none => exact Option.Rel.none
        | some t =>
          have hr := ih
          rw [hx, hy] at hr
          cases hr
      | some s =>
        cases hy : y.lookup l with
        | none =>
          have hr := ih
          rw [hx, hy] at hr
          cases hr
        | some t =>
          have hr := ih
          rw [hx, hy] at hr
          cases hr with
          | some hinner =>
            exact Option.Rel.some (BranchingType.PermEquiv.symm hinner)
    | trans x y z _ _ ih1 ih2 =>
      cases hx : x.lookup l with
      | none =>
        cases hy : y.lookup l with
        | none =>
          cases hz : z.lookup l with
          | none => exact Option.Rel.none
          | some u =>
            have hr := ih2
            rw [hy, hz] at hr
            cases hr
        | some v =>
          have hr := ih1
          rw [hx, hy] at hr
          cases hr
      | some s =>
        cases hy : y.lookup l with
        | none =>
          have hr := ih1
          rw [hx, hy] at hr
          cases hr
        | some v =>
          cases hz : z.lookup l with
          | none =>
            have hr := ih2
            rw [hy, hz] at hr
            cases hr
          | some u =>
            have hr1 := ih1
            rw [hx, hy] at hr1
            have hr2 := ih2
            rw [hy, hz] at hr2
            cases hr1 with
            | some hinner1 =>
              cases hr2 with
              | some hinner2 =>
                exact Option.Rel.some
                  (BranchingType.PermEquiv.trans hinner1 hinner2)
  have lookup_mem : ∀ (cs : BranchingType.Branches S L) (l : L)
      (x : BranchingType S L),
      cs.lookup l = some x → (l, x) ∈ cs.entries := by
    intro cs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun cs => ∀ (l : L) (x : BranchingType S L),
        cs.lookup l = some x → (l, x) ∈ cs.entries)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ cs
    · exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro l x hlook
      simp only [BranchingType.Branches.lookup] at hlook
      cases hlook
    · intro l' x' t' _ ih l x hlook
      by_cases e : l = l'
      · simp only [BranchingType.Branches.lookup, ite_eq_left e] at hlook
        cases hlook
        rw [e]
        simp only [BranchingType.Branches.entries, List.mem_cons]
        exact Or.inl True.intro
      · simp only [BranchingType.Branches.lookup, ite_eq_right e] at hlook
        have hmem_tail := ih l x hlook
        simp only [BranchingType.Branches.entries, List.mem_cons]
        exact Or.inr hmem_tail
  have lookup_none : ∀ (cs : BranchingType.Branches S L) (l : L),
      l ∉ cs.labels → cs.lookup l = none := by
    intro cs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun cs => ∀ (l : L),
        l ∉ cs.labels → cs.lookup l = none)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ cs
    · exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro l _
      exact rfl
    · intro l' x' t' _ ih l hnotin
      have hlab : (BranchingType.Branches.cons l' x' t').labels =
        l' :: t'.labels := rfl
      rw [hlab] at hnotin
      have hne : l ≠ l' := fun heq =>
        hnotin (List.mem_cons.mpr (Or.inl heq))
      have hnotin_tail : l ∉ t'.labels := fun hm =>
        hnotin (List.mem_cons.mpr (Or.inr hm))
      simp only [BranchingType.Branches.lookup, ite_eq_right hne]
      exact ih l hnotin_tail
  have bubble_wf : ∀ (cs : BranchingType.Branches S L) (l : L)
      (x : BranchingType S L),
      cs.WellFormed → (l, x) ∈ cs.entries →
        ∃ cs', BranchingType.Branches.PermEquiv cs
          (BranchingType.Branches.cons l x cs') ∧
          List.Perm cs.entries ((l, x) :: cs'.entries) ∧
          cs'.WellFormed := by
    intro cs
    refine BranchingType.Branches.rec (motive_1 := fun _ => True)
      (motive_2 := fun cs => ∀ (l : L) (x : BranchingType S L),
        cs.WellFormed → (l, x) ∈ cs.entries →
          ∃ cs', BranchingType.Branches.PermEquiv cs
            (BranchingType.Branches.cons l x cs') ∧
            List.Perm cs.entries ((l, x) :: cs'.entries) ∧
            cs'.WellFormed)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ cs
    · exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro _ _; exact True.intro
    · intro l x hw hmem
      simp only [BranchingType.Branches.entries, List.not_mem_nil] at hmem
    · intro l' x' t' _ ih l x hw hmem
      cases hw with
      | cons hnotin hwhead hwtail =>
        simp only [BranchingType.Branches.entries, List.mem_cons,
          Prod.mk.injEq] at hmem
        cases hmem with
        | inl heq =>
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨t', BranchingType.Branches.PermEquiv.refl _,
            List.Perm.refl _, hwtail⟩
        | inr hmem2 =>
          obtain ⟨u, hu, hup, hwu⟩ := ih l x hwtail hmem2
          have hmem_lbl : l ∈ t'.labels :=
            List.mem_map_of_mem (f := Prod.fst) hmem2
          have hne : l' ≠ l := by
            intro heq
            rw [heq] at hnotin
            exact hnotin hmem_lbl
          have hperm : BranchingType.Branches.PermEquiv
              (BranchingType.Branches.cons l' x' t')
              (BranchingType.Branches.cons l x
                (BranchingType.Branches.cons l' x' u)) :=
            BranchingType.Branches.PermEquiv.trans
              (BranchingType.Branches.PermEquiv.cons
                (BranchingType.PermEquiv.refl x') hu)
              (Relation.EqvGen.rel _ _
                (BranchingType.Branches.SwapStep.swap hne))
          have hentries : List.Perm
              (BranchingType.Branches.cons l' x' t').entries
              ((l, x) ::
                (BranchingType.Branches.cons l' x' u).entries) :=
            (List.Perm.cons _ hup).trans (List.Perm.swap _ _ _)
          have hmap_u : List.Perm t'.labels (l :: u.labels) :=
            List.Perm.map Prod.fst hup
          have hnot : l' ∉ u.labels := by
            intro hlu
            have hmc : l' ∈ l :: u.labels :=
              List.mem_cons.mpr (Or.inr hlu)
            exact hnotin (hmap_u.symm.subset hmc)
          have hwcs' : (BranchingType.Branches.cons l' x' u).WellFormed :=
            BranchingType.Branches.WellFormed.cons hnot hwhead hwu
          exact ⟨BranchingType.Branches.cons l' x' u, hperm, hentries,
            hwcs'⟩
  intro hw hwc
  refine ⟨fun h => ⟨labels_perm_local h,
    fun label => lookup_rel_local label h⟩, ?_⟩
  intro hback
  obtain ⟨hlab, hlook⟩ := hback
  refine BranchingType.Branches.rec (motive_1 := fun _ => True)
    (motive_2 := fun bs => ∀ cs : BranchingType.Branches S L,
      bs.WellFormed → cs.WellFormed →
        List.Perm bs.labels cs.labels →
          (∀ label : L, Option.Rel BranchingType.PermEquiv
            (bs.lookup label) (cs.lookup label)) →
          BranchingType.Branches.PermEquiv bs cs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ bs cs hw hwc hlab hlook
  · exact True.intro
  · intro _ _ _; exact True.intro
  · intro _ _ _; exact True.intro
  · intro _ _; exact True.intro
  · intro _ _; exact True.intro
  · intro cs hw hwc hlab hlook
    have hempty : cs.labels = [] := List.Perm.eq_nil hlab.symm
    cases cs with
    | nil => exact BranchingType.Branches.PermEquiv.refl _
    | cons l x t =>
      have hlab_cons : (BranchingType.Branches.cons l x t).labels =
        l :: t.labels := rfl
      rw [hlab_cons] at hempty
      cases hempty
  · intro label head tail _ ih cs hw hwc hlab hlook
    cases hw with
    | cons hnotin _ hwtail =>
      have hbs_lookup : (BranchingType.Branches.cons label head tail).lookup
          label = some head := ite_eq_left rfl
      obtain ⟨head', hcs_lookup, hhead⟩ :
          ∃ head' : BranchingType S L,
            cs.lookup label = some head' ∧
              BranchingType.PermEquiv head head' := by
        have hrel := hlook label
        rw [hbs_lookup] at hrel
        cases hcs : cs.lookup label with
        | none =>
          rw [hcs] at hrel
          cases hrel
        | some head' =>
          rw [hcs] at hrel
          cases hrel with
          | some hhead => exact ⟨head', rfl, hhead⟩
      have hmem_cs : (label, head') ∈ cs.entries :=
        lookup_mem cs label head' hcs_lookup
      obtain ⟨cs', hcs, hup, hwcs'⟩ :=
        bubble_wf cs label head' hwc hmem_cs
      have hplab : List.Perm cs.labels (label :: cs'.labels) :=
        List.Perm.map Prod.fst hup
      have hlab_cons : (BranchingType.Branches.cons label head tail).labels =
        label :: tail.labels := rfl
      rw [hlab_cons] at hlab
      have hlab' : List.Perm tail.labels cs'.labels :=
        List.Perm.cons_inv (hlab.trans hplab)
      have hlook' : ∀ l : L, Option.Rel BranchingType.PermEquiv
          (tail.lookup l) (cs'.lookup l) := by
        intro l
        by_cases e : l = label
        · rw [e]
          have htail_none : tail.lookup label = none :=
            lookup_none tail label hnotin
          have hncs : cs.labels.Nodup :=
            BranchingType.Branches.labels_nodup_of_wellFormed cs hwc
          have hnod_cons : (label :: cs'.labels).Nodup :=
            (List.Perm.nodup_iff hplab).mp hncs
          have hnotin_cs' : label ∉ cs'.labels :=
            (List.nodup_cons.mp hnod_cons).1
          have hcs'_none : cs'.lookup label = none :=
            lookup_none cs' label hnotin_cs'
          rw [htail_none, hcs'_none]
          exact Option.Rel.none
        · have e1 : (BranchingType.Branches.cons label head tail).lookup l =
              tail.lookup l := by
            simp only [BranchingType.Branches.lookup, ite_eq_right e]
          have e2 : (BranchingType.Branches.cons label head' cs').lookup l =
              cs'.lookup l := by
            simp only [BranchingType.Branches.lookup, ite_eq_right e]
          have r1 := hlook l
          rw [e1] at r1
          have r2 := lookup_rel_local l hcs
          rw [e2] at r2
          cases ht : tail.lookup l with
          | none =>
            cases hcm : cs.lookup l with
            | none =>
              cases hc' : cs'.lookup l with
              | none =>
                exact Option.Rel.none
              | some v' =>
                rw [hcm, hc'] at r2
                cases r2
            | some v =>
              rw [ht, hcm] at r1
              cases r1
          | some v =>
            cases hcm : cs.lookup l with
            | none =>
              rw [ht, hcm] at r1
              cases r1
            | some w =>
              cases hc' : cs'.lookup l with
              | none =>
                rw [hcm, hc'] at r2
                cases r2
              | some v' =>
                rw [ht, hcm] at r1
                rw [hcm, hc'] at r2
                cases r1 with
                | some h1 =>
                  cases r2 with
                  | some h2 =>
                    exact Option.Rel.some
                      (BranchingType.PermEquiv.trans h1 h2)
      have htail_equiv : BranchingType.Branches.PermEquiv tail cs' :=
        ih cs' hwtail hwcs' hlab' hlook'
      have hcons_equiv : BranchingType.Branches.PermEquiv
          (BranchingType.Branches.cons label head tail)
          (BranchingType.Branches.cons label head' cs') :=
        BranchingType.Branches.PermEquiv.cons hhead htail_equiv
      exact BranchingType.Branches.PermEquiv.trans hcons_equiv
        (BranchingType.Branches.PermEquiv.symm hcs)

/-- PermEquiv branch lists have permuted labels. -/
theorem BranchingType.Branches.PermEquiv.labels_perm {S L : Type}
    {bs cs : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv bs cs →
      List.Perm bs.labels cs.labels := by
    have step_labels : ∀ {bs cs : BranchingType.Branches S L},
        BranchingType.Branches.SwapStep bs cs →
          List.Perm bs.labels cs.labels := by
      intro bs cs hstep
      refine BranchingType.Branches.SwapStep.rec
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun bs cs _ => List.Perm bs.labels cs.labels)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro l1 l2 h1 h2 t _hne
        show List.Perm (l1 :: l2 :: t.labels) (l2 :: l1 :: t.labels)
        exact List.Perm.swap _ _ _
      · intro lb hd hd' tail _h _ih
        show List.Perm (lb :: tail.labels) (lb :: tail.labels)
        exact List.Perm.refl _
      · intro lb hd tail tail' _h ih
        show List.Perm (lb :: tail.labels) (lb :: tail'.labels)
        exact List.Perm.cons _ ih
    intro h
    induction h with
    | rel x y hstep => exact step_labels hstep
    | refl x => exact List.Perm.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Each entry has a same-label PermEquiv entry in the other list. -/
theorem BranchingType.Branches.PermEquiv.exists_mem {S L : Type}
    {bs cs : BranchingType.Branches S L}
    {label : L} {head : BranchingType S L} :
    BranchingType.Branches.PermEquiv bs cs → (label, head) ∈ bs.entries →
      ∃ head' : BranchingType S L, (label, head') ∈ cs.entries ∧
        BranchingType.PermEquiv head head' := by
    have step_mem : ∀ {bs cs : BranchingType.Branches S L},
        BranchingType.Branches.SwapStep bs cs →
          (∀ (l : L) (hd : BranchingType S L), (l, hd) ∈ bs.entries →
            ∃ hd' : BranchingType S L, (l, hd') ∈ cs.entries ∧
              BranchingType.PermEquiv hd hd') ∧
          (∀ (l : L) (hd : BranchingType S L), (l, hd) ∈ cs.entries →
            ∃ hd' : BranchingType S L, (l, hd') ∈ bs.entries ∧
              BranchingType.PermEquiv hd hd') := by
      intro bs cs hstep
      refine BranchingType.Branches.SwapStep.rec
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun bs cs _ =>
          (∀ (l : L) (hd : BranchingType S L), (l, hd) ∈ bs.entries →
            ∃ hd' : BranchingType S L, (l, hd') ∈ cs.entries ∧
              BranchingType.PermEquiv hd hd') ∧
          (∀ (l : L) (hd : BranchingType S L), (l, hd) ∈ cs.entries →
            ∃ hd' : BranchingType S L, (l, hd') ∈ bs.entries ∧
              BranchingType.PermEquiv hd hd')) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
      · intro _ _ _ _ _; exact True.intro
      · intro _ _ _ _ _; exact True.intro
      · intro _ _ _ _; exact True.intro
      · intro _ _ _ _; exact True.intro
      · intro label1 label2 head1 head2 tail _hne
        refine ⟨?_, ?_⟩
        · intro l hd hmem
          simp only [BranchingType.Branches.entries, List.mem_cons] at hmem
          cases hmem with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine ⟨hd, ?_, BranchingType.PermEquiv.refl hd⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inr (Or.inl True.intro)
          | inr hmem2 =>
            cases hmem2 with
            | inl heq =>
              simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
              refine ⟨hd, ?_, BranchingType.PermEquiv.refl hd⟩
              simp only [BranchingType.Branches.entries, List.mem_cons]
              exact Or.inl True.intro
            | inr hmem3 =>
              refine ⟨hd, ?_, BranchingType.PermEquiv.refl hd⟩
              simp only [BranchingType.Branches.entries, List.mem_cons]
              exact Or.inr (Or.inr hmem3)
        · intro l hd hmem
          simp only [BranchingType.Branches.entries, List.mem_cons] at hmem
          cases hmem with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine ⟨hd, ?_, BranchingType.PermEquiv.refl hd⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inr (Or.inl True.intro)
          | inr hmem2 =>
            cases hmem2 with
            | inl heq =>
              simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
              refine ⟨hd, ?_, BranchingType.PermEquiv.refl hd⟩
              simp only [BranchingType.Branches.entries, List.mem_cons]
              exact Or.inl True.intro
            | inr hmem3 =>
              refine ⟨hd, ?_, BranchingType.PermEquiv.refl hd⟩
              simp only [BranchingType.Branches.entries, List.mem_cons]
              exact Or.inr (Or.inr hmem3)
      · intro label srcHead tgtHead tail h _ih
        refine ⟨?_, ?_⟩
        · intro l hd0 hmem
          simp only [BranchingType.Branches.entries, List.mem_cons] at hmem
          cases hmem with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine ⟨tgtHead, ?_, Relation.EqvGen.rel _ _ h⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inl True.intro
          | inr hmem2 =>
            refine ⟨hd0, ?_, BranchingType.PermEquiv.refl hd0⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inr hmem2
        · intro l hd0 hmem
          simp only [BranchingType.Branches.entries, List.mem_cons] at hmem
          cases hmem with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine ⟨srcHead, ?_, BranchingType.PermEquiv.symm
              (Relation.EqvGen.rel _ _ h)⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inl True.intro
          | inr hmem2 =>
            refine ⟨hd0, ?_, BranchingType.PermEquiv.refl hd0⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inr hmem2
      · intro label head tail tail' _h ih
        refine ⟨?_, ?_⟩
        · intro l hd0 hmem
          simp only [BranchingType.Branches.entries, List.mem_cons] at hmem
          cases hmem with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine ⟨hd0, ?_, BranchingType.PermEquiv.refl hd0⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inl True.intro
          | inr hmem2 =>
            obtain ⟨hd1, hm, hr⟩ := ih.1 l hd0 hmem2
            refine ⟨hd1, ?_, hr⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inr hm
        · intro l hd0 hmem
          simp only [BranchingType.Branches.entries, List.mem_cons] at hmem
          cases hmem with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            refine ⟨hd0, ?_, BranchingType.PermEquiv.refl hd0⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inl True.intro
          | inr hmem2 =>
            obtain ⟨hd1, hm, hr⟩ := ih.2 l hd0 hmem2
            refine ⟨hd1, ?_, hr⟩
            simp only [BranchingType.Branches.entries, List.mem_cons]
            exact Or.inr hm
    have key : ∀ {bs cs : BranchingType.Branches S L},
        BranchingType.Branches.PermEquiv bs cs →
          (∀ (l : L) (hd : BranchingType S L), (l, hd) ∈ bs.entries →
            ∃ hd' : BranchingType S L, (l, hd') ∈ cs.entries ∧
              BranchingType.PermEquiv hd hd') ∧
          (∀ (l : L) (hd : BranchingType S L), (l, hd) ∈ cs.entries →
            ∃ hd' : BranchingType S L, (l, hd') ∈ bs.entries ∧
              BranchingType.PermEquiv hd hd') := by
      intro bs cs h
      induction h with
      | rel x y hstep => exact step_mem hstep
      | refl x =>
        constructor
        · intro l hd hmem
          exact ⟨hd, hmem, BranchingType.PermEquiv.refl hd⟩
        · intro l hd hmem
          exact ⟨hd, hmem, BranchingType.PermEquiv.refl hd⟩
      | symm x y _ ih => exact ⟨ih.2, ih.1⟩
      | trans x y z _ _ ih1 ih2 =>
        constructor
        · intro l hd hmem
          obtain ⟨m, hm2, r1⟩ := ih1.1 l hd hmem
          obtain ⟨m2, hm3, r2⟩ := ih2.1 l m hm2
          exact ⟨m2, hm3, BranchingType.PermEquiv.trans r1 r2⟩
        · intro l hd hmem
          obtain ⟨m, hm2, r1⟩ := ih2.2 l hd hmem
          obtain ⟨m2, hm3, r2⟩ := ih1.2 l m hm2
          exact ⟨m2, hm3, BranchingType.PermEquiv.trans r1 r2⟩
    intro h hmem
    exact (key h).1 label head hmem

/-- PermEquiv branch lists have related lookups at every label. -/
theorem BranchingType.Branches.PermEquiv.lookup_rel {S L : Type}
    [DecidableEq L] {bs cs : BranchingType.Branches S L}
    {label : L} :
    BranchingType.Branches.PermEquiv bs cs →
      Option.Rel BranchingType.PermEquiv (bs.lookup label)
        (cs.lookup label) := by
    have step_lookup : ∀ {bs cs : BranchingType.Branches S L},
        BranchingType.Branches.SwapStep bs cs →
          Option.Rel BranchingType.PermEquiv (bs.lookup label)
            (cs.lookup label) := by
      intro bs cs hstep
      refine BranchingType.Branches.SwapStep.rec
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun bs cs _ => Option.Rel BranchingType.PermEquiv
          (bs.lookup label) (cs.lookup label)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro l1 l2 h1 h2 t hne
        by_cases e1 : label = l1
        · by_cases e2 : label = l2
          · exact absurd (e1.symm.trans e2) hne
          · simp only [BranchingType.Branches.lookup, if_pos e1, if_neg e2]
            exact Option.Rel.some (BranchingType.PermEquiv.refl h1)
        · by_cases e2 : label = l2
          · simp only [BranchingType.Branches.lookup, if_neg e1, if_pos e2]
            exact Option.Rel.some (BranchingType.PermEquiv.refl h2)
          · simp only [BranchingType.Branches.lookup, if_neg e1, if_neg e2]
            cases ht : t.lookup label with
            | none => exact Option.Rel.none
            | some v =>
              exact Option.Rel.some (BranchingType.PermEquiv.refl v)
      · intro lb hd hd' tail h _ih
        by_cases e : label = lb
        · simp only [BranchingType.Branches.lookup, if_pos e]
          exact Option.Rel.some (Relation.EqvGen.rel _ _ h)
        · simp only [BranchingType.Branches.lookup, if_neg e]
          cases ht : tail.lookup label with
          | none => exact Option.Rel.none
          | some v =>
            exact Option.Rel.some (BranchingType.PermEquiv.refl v)
      · intro lb hd tail tail' _h ih
        by_cases e : label = lb
        · simp only [BranchingType.Branches.lookup, if_pos e]
          exact Option.Rel.some (BranchingType.PermEquiv.refl hd)
        · simp only [BranchingType.Branches.lookup, if_neg e]
          exact ih
    intro h
    induction h with
    | rel x y hstep => exact step_lookup hstep
    | refl x =>
      cases hx : x.lookup label with
      | none => exact Option.Rel.none
      | some v => exact Option.Rel.some (BranchingType.PermEquiv.refl v)
    | symm x y _ ih =>
      cases hx : x.lookup label with
      | none =>
        cases hy : y.lookup label with
        | none => exact Option.Rel.none
        | some t =>
          have hr := ih
          rw [hx, hy] at hr
          cases hr
      | some s =>
        cases hy : y.lookup label with
        | none =>
          have hr := ih
          rw [hx, hy] at hr
          cases hr
        | some t =>
          have hr := ih
          rw [hx, hy] at hr
          cases hr with
          | some hinner =>
            exact Option.Rel.some (BranchingType.PermEquiv.symm hinner)
    | trans x y z _ _ ih1 ih2 =>
      cases hx : x.lookup label with
      | none =>
        cases hy : y.lookup label with
        | none =>
          cases hz : z.lookup label with
          | none => exact Option.Rel.none
          | some u =>
            have hr := ih2
            rw [hy, hz] at hr
            cases hr
        | some v =>
          have hr := ih1
          rw [hx, hy] at hr
          cases hr
      | some s =>
        cases hy : y.lookup label with
        | none =>
          have hr := ih1
          rw [hx, hy] at hr
          cases hr
        | some v =>
          cases hz : z.lookup label with
          | none =>
            have hr := ih2
            rw [hy, hz] at hr
            cases hr
          | some u =>
            have hr1 := ih1
            rw [hx, hy] at hr1
            have hr2 := ih2
            rw [hy, hz] at hr2
            cases hr1 with
            | some hinner1 =>
              cases hr2 with
              | some hinner2 =>
                exact Option.Rel.some
                  (BranchingType.PermEquiv.trans hinner1 hinner2)

/-- PermEquiv on types is preserved by duality. -/
theorem BranchingType.PermEquiv.dual {S L : Type}
    {t u : BranchingType S L} :
    BranchingType.PermEquiv t u →
      BranchingType.PermEquiv t.dual u.dual := by
  have step_dual : ∀ {t u : BranchingType S L}, BranchingType.SwapStep t u →
      BranchingType.PermEquiv t.dual u.dual := by
    intro t u hstep
    refine BranchingType.SwapStep.rec
      (motive_1 := fun t u _ => BranchingType.PermEquiv t.dual u.dual)
      (motive_2 := fun bs cs _ => BranchingType.Branches.PermEquiv bs.dual cs.dual)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
    · intro payload next next' step ih
      change BranchingType.PermEquiv (.recv payload next.dual) (.recv payload next'.dual)
      exact BranchingType.PermEquiv.recv ih
    · intro payload next next' step ih
      change BranchingType.PermEquiv (.send payload next.dual) (.send payload next'.dual)
      exact BranchingType.PermEquiv.send ih
    · intro branches branches' step ih
      change BranchingType.PermEquiv (.branch branches.dual) (.branch branches'.dual)
      exact BranchingType.PermEquiv.branch ih
    · intro branches branches' step ih
      change BranchingType.PermEquiv (.select branches.dual) (.select branches'.dual)
      exact BranchingType.PermEquiv.select ih
    · intro label1 label2 head1 head2 tail hne
      change BranchingType.Branches.PermEquiv
        (.cons label1 head1.dual (.cons label2 head2.dual tail.dual))
        (.cons label2 head2.dual (.cons label1 head1.dual tail.dual))
      exact Relation.EqvGen.rel _ _
        (BranchingType.Branches.SwapStep.swap hne)
    · intro label head head' tail step ih
      change BranchingType.Branches.PermEquiv (.cons label head.dual tail.dual)
        (.cons label head'.dual tail.dual)
      exact BranchingType.Branches.PermEquiv.cons ih
        (BranchingType.Branches.PermEquiv.refl _)
    · intro label head tail tail' step ih
      change BranchingType.Branches.PermEquiv (.cons label head.dual tail.dual)
        (.cons label head.dual tail'.dual)
      exact BranchingType.Branches.PermEquiv.cons
        (BranchingType.PermEquiv.refl _) ih
  intro h
  induction h with
  | rel x y hstep => exact step_dual hstep
  | refl x => exact BranchingType.PermEquiv.refl _
  | symm x y _ ih => exact BranchingType.PermEquiv.symm ih
  | trans x y z _ _ ih1 ih2 => exact BranchingType.PermEquiv.trans ih1 ih2

/-- PermEquiv on branch lists is preserved by duality. -/
theorem BranchingType.Branches.PermEquiv.dual {S L : Type}
    {bs cs : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv bs cs →
      BranchingType.Branches.PermEquiv bs.dual cs.dual := by
  have step_dual : ∀ {bs cs : BranchingType.Branches S L},
      BranchingType.Branches.SwapStep bs cs →
      BranchingType.Branches.PermEquiv bs.dual cs.dual := by
    intro bs cs hstep
    refine BranchingType.Branches.SwapStep.rec
      (motive_1 := fun t u _ => BranchingType.PermEquiv t.dual u.dual)
      (motive_2 := fun bs cs _ => BranchingType.Branches.PermEquiv bs.dual cs.dual)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
    · intro payload next next' step ih
      change BranchingType.PermEquiv (.recv payload next.dual) (.recv payload next'.dual)
      exact BranchingType.PermEquiv.recv ih
    · intro payload next next' step ih
      change BranchingType.PermEquiv (.send payload next.dual) (.send payload next'.dual)
      exact BranchingType.PermEquiv.send ih
    · intro branches branches' step ih
      change BranchingType.PermEquiv (.branch branches.dual) (.branch branches'.dual)
      exact BranchingType.PermEquiv.branch ih
    · intro branches branches' step ih
      change BranchingType.PermEquiv (.select branches.dual) (.select branches'.dual)
      exact BranchingType.PermEquiv.select ih
    · intro label1 label2 head1 head2 tail hne
      change BranchingType.Branches.PermEquiv
        (.cons label1 head1.dual (.cons label2 head2.dual tail.dual))
        (.cons label2 head2.dual (.cons label1 head1.dual tail.dual))
      exact Relation.EqvGen.rel _ _
        (BranchingType.Branches.SwapStep.swap hne)
    · intro label head head' tail step ih
      change BranchingType.Branches.PermEquiv (.cons label head.dual tail.dual)
        (.cons label head'.dual tail.dual)
      exact BranchingType.Branches.PermEquiv.cons ih
        (BranchingType.Branches.PermEquiv.refl _)
    · intro label head tail tail' step ih
      change BranchingType.Branches.PermEquiv (.cons label head.dual tail.dual)
        (.cons label head.dual tail'.dual)
      exact BranchingType.Branches.PermEquiv.cons
        (BranchingType.PermEquiv.refl _) ih
  intro h
  induction h with
  | rel x y hstep => exact step_dual hstep
  | refl x => exact BranchingType.Branches.PermEquiv.refl _
  | symm x y _ ih => exact BranchingType.Branches.PermEquiv.symm ih
  | trans x y z _ _ ih1 ih2 => exact BranchingType.Branches.PermEquiv.trans ih1 ih2

/-- Well-formedness of types is invariant under PermEquiv. -/
theorem BranchingType.WellFormed.permEquiv {S L : Type}
    {t u : BranchingType S L} :
    BranchingType.PermEquiv t u → (t.WellFormed ↔ u.WellFormed) := by
  have step_wf : ∀ {t u : BranchingType S L}, BranchingType.SwapStep t u →
      (t.WellFormed ↔ u.WellFormed) := by
    intro t u hstep
    refine BranchingType.SwapStep.rec
      (motive_1 := fun t u _ => (t.WellFormed ↔ u.WellFormed))
      (motive_2 := fun bs cs _ => (bs.WellFormed ↔ cs.WellFormed))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
    · intro payload next next' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | send h => exact BranchingType.WellFormed.send (ih.mp h)
      · intro hw
        cases hw with
        | send h => exact BranchingType.WellFormed.send (ih.mpr h)
    · intro payload next next' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | recv h => exact BranchingType.WellFormed.recv (ih.mp h)
      · intro hw
        cases hw with
        | recv h => exact BranchingType.WellFormed.recv (ih.mpr h)
    · intro branches branches' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | select h => exact BranchingType.WellFormed.select (ih.mp h)
      · intro hw
        cases hw with
        | select h => exact BranchingType.WellFormed.select (ih.mpr h)
    · intro branches branches' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | branch h => exact BranchingType.WellFormed.branch (ih.mp h)
      · intro hw
        cases hw with
        | branch h => exact BranchingType.WellFormed.branch (ih.mpr h)
    · intro label1 label2 head1 head2 tail hne
      have hlab1 : (BranchingType.Branches.cons label1 head1 tail).labels
          = label1 :: tail.labels := rfl
      have hlab2 : (BranchingType.Branches.cons label2 head2 tail).labels
          = label2 :: tail.labels := rfl
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | cons h1not hw1 hwrest =>
          cases hwrest with
          | cons h2not hw2 hwt =>
            rw [hlab2] at h1not
            simp only [List.mem_cons] at h1not
            have h1tail : label1 ∉ tail.labels := fun hm => h1not (Or.inr hm)
            have hne21 : label2 ≠ label1 := fun he => hne he.symm
            have hout : label2 ∉
                (BranchingType.Branches.cons label1 head1 tail).labels := by
              rw [hlab1]
              intro hm
              simp only [List.mem_cons] at hm
              cases hm with
              | inl he => exact hne21 he
              | inr hm2 => exact h2not hm2
            exact BranchingType.Branches.WellFormed.cons hout hw2
              (BranchingType.Branches.WellFormed.cons h1tail hw1 hwt)
      · intro hw
        cases hw with
        | cons h2not hw2 hwrest =>
          cases hwrest with
          | cons h1not hw1 hwt =>
            rw [hlab1] at h2not
            simp only [List.mem_cons] at h2not
            have h2tail : label2 ∉ tail.labels := fun hm => h2not (Or.inr hm)
            have hout : label1 ∉
                (BranchingType.Branches.cons label2 head2 tail).labels := by
              rw [hlab2]
              intro hm
              simp only [List.mem_cons] at hm
              cases hm with
              | inl he => exact hne he
              | inr hm2 => exact h1not hm2
            exact BranchingType.Branches.WellFormed.cons hout hw1
              (BranchingType.Branches.WellFormed.cons h2tail hw2 hwt)
    · intro label head head' tail step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          exact BranchingType.Branches.WellFormed.cons hnotin (ih.mp hwhead) hwtail
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          exact BranchingType.Branches.WellFormed.cons hnotin (ih.mpr hwhead) hwtail
    · intro label head tail tail' step ih
      have hp : BranchingType.Branches.PermEquiv tail tail' :=
        Relation.EqvGen.rel _ _ step
      have hlab := hp.labels_perm
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          have hnotin' : label ∉ tail'.labels :=
            fun hm => hnotin (hlab.symm.subset hm)
          exact BranchingType.Branches.WellFormed.cons hnotin' hwhead (ih.mp hwtail)
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          have hnotin' : label ∉ tail.labels :=
            fun hm => hnotin (hlab.subset hm)
          exact BranchingType.Branches.WellFormed.cons hnotin' hwhead (ih.mpr hwtail)
  intro h
  induction h with
  | rel x y hstep => exact step_wf hstep
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Well-formedness of branch lists is invariant under PermEquiv. -/
theorem BranchingType.Branches.WellFormed.permEquiv {S L : Type}
    {bs cs : BranchingType.Branches S L} :
    BranchingType.Branches.PermEquiv bs cs →
      (bs.WellFormed ↔ cs.WellFormed) := by
  have step_wf : ∀ {bs cs : BranchingType.Branches S L},
      BranchingType.Branches.SwapStep bs cs →
      (bs.WellFormed ↔ cs.WellFormed) := by
    intro bs cs hstep
    refine BranchingType.Branches.SwapStep.rec
      (motive_1 := fun t u _ => (t.WellFormed ↔ u.WellFormed))
      (motive_2 := fun bs cs _ => (bs.WellFormed ↔ cs.WellFormed))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
    · intro payload next next' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | send h => exact BranchingType.WellFormed.send (ih.mp h)
      · intro hw
        cases hw with
        | send h => exact BranchingType.WellFormed.send (ih.mpr h)
    · intro payload next next' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | recv h => exact BranchingType.WellFormed.recv (ih.mp h)
      · intro hw
        cases hw with
        | recv h => exact BranchingType.WellFormed.recv (ih.mpr h)
    · intro branches branches' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | select h => exact BranchingType.WellFormed.select (ih.mp h)
      · intro hw
        cases hw with
        | select h => exact BranchingType.WellFormed.select (ih.mpr h)
    · intro branches branches' step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | branch h => exact BranchingType.WellFormed.branch (ih.mp h)
      · intro hw
        cases hw with
        | branch h => exact BranchingType.WellFormed.branch (ih.mpr h)
    · intro label1 label2 head1 head2 tail hne
      have hlab1 : (BranchingType.Branches.cons label1 head1 tail).labels
          = label1 :: tail.labels := rfl
      have hlab2 : (BranchingType.Branches.cons label2 head2 tail).labels
          = label2 :: tail.labels := rfl
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | cons h1not hw1 hwrest =>
          cases hwrest with
          | cons h2not hw2 hwt =>
            rw [hlab2] at h1not
            simp only [List.mem_cons] at h1not
            have h1tail : label1 ∉ tail.labels := fun hm => h1not (Or.inr hm)
            have hne21 : label2 ≠ label1 := fun he => hne he.symm
            have hout : label2 ∉
                (BranchingType.Branches.cons label1 head1 tail).labels := by
              rw [hlab1]
              intro hm
              simp only [List.mem_cons] at hm
              cases hm with
              | inl he => exact hne21 he
              | inr hm2 => exact h2not hm2
            exact BranchingType.Branches.WellFormed.cons hout hw2
              (BranchingType.Branches.WellFormed.cons h1tail hw1 hwt)
      · intro hw
        cases hw with
        | cons h2not hw2 hwrest =>
          cases hwrest with
          | cons h1not hw1 hwt =>
            rw [hlab1] at h2not
            simp only [List.mem_cons] at h2not
            have h2tail : label2 ∉ tail.labels := fun hm => h2not (Or.inr hm)
            have hout : label1 ∉
                (BranchingType.Branches.cons label2 head2 tail).labels := by
              rw [hlab2]
              intro hm
              simp only [List.mem_cons] at hm
              cases hm with
              | inl he => exact hne he
              | inr hm2 => exact h1not hm2
            exact BranchingType.Branches.WellFormed.cons hout hw1
              (BranchingType.Branches.WellFormed.cons h2tail hw2 hwt)
    · intro label head head' tail step ih
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          exact BranchingType.Branches.WellFormed.cons hnotin (ih.mp hwhead) hwtail
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          exact BranchingType.Branches.WellFormed.cons hnotin (ih.mpr hwhead) hwtail
    · intro label head tail tail' step ih
      have hp : BranchingType.Branches.PermEquiv tail tail' :=
        Relation.EqvGen.rel _ _ step
      have hlab := hp.labels_perm
      refine ⟨?_, ?_⟩
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          have hnotin' : label ∉ tail'.labels :=
            fun hm => hnotin (hlab.symm.subset hm)
          exact BranchingType.Branches.WellFormed.cons hnotin' hwhead (ih.mp hwtail)
      · intro hw
        cases hw with
        | cons hnotin hwhead hwtail =>
          have hnotin' : label ∉ tail.labels :=
            fun hm => hnotin (hlab.subset hm)
          exact BranchingType.Branches.WellFormed.cons hnotin' hwhead (ih.mpr hwtail)
  intro h
  induction h with
  | rel x y hstep => exact step_wf hstep
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

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

/-- Embedding reflects and preserves equality as PermEquiv. -/
theorem BranchingType.ofSessionType_permEquiv_iff {S L : Type}
    (passive : S) (s1 s2 : SessionType) :
    BranchingType.PermEquiv
        (BranchingType.ofSessionType (L := L) passive s1)
        (BranchingType.ofSessionType (L := L) passive s2) ↔
      s1 = s2 := by
  have key : ∀ (s : SessionType) {u : BranchingType S L},
      BranchingType.PermEquiv
        (BranchingType.ofSessionType (L := L) passive s) u →
        u = BranchingType.ofSessionType (L := L) passive s := by
    intro s
    induction s with
    | «end» =>
      have step_iff : ∀ {x y : BranchingType S L},
          BranchingType.SwapStep x y →
          (x = BranchingType.ofSessionType (L := L) passive SessionType.end ↔
            y = BranchingType.ofSessionType (L := L) passive SessionType.end) := by
        intro x y hstep
        constructor
        · intro hx
          subst hx
          simp only [BranchingType.ofSessionType] at hstep
          cases hstep
        · intro hy
          subst hy
          simp only [BranchingType.ofSessionType] at hstep
          cases hstep
      intro u h
      have key_iff : ∀ {x y : BranchingType S L},
          BranchingType.PermEquiv x y →
          (x = BranchingType.ofSessionType (L := L) passive SessionType.end ↔
            y = BranchingType.ofSessionType (L := L) passive SessionType.end) := by
        intro x y hxy
        induction hxy with
        | rel x y hstep => exact step_iff hstep
        | refl x => exact Iff.rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
      exact (key_iff h).1 rfl
    | send n ihn =>
      have step_iff : ∀ {x y : BranchingType S L},
          BranchingType.SwapStep x y →
          (x = BranchingType.ofSessionType (L := L) passive (SessionType.send n) ↔
            y = BranchingType.ofSessionType (L := L) passive (SessionType.send n)) := by
        intro x y hstep
        constructor
        · intro hx
          subst hx
          simp only [BranchingType.ofSessionType] at hstep
          cases hstep with
          | send hsub =>
            have hv := ihn (Relation.EqvGen.rel _ _ hsub)
            subst hv
            rfl
        · intro hy
          subst hy
          simp only [BranchingType.ofSessionType] at hstep
          cases hstep with
          | send hsub =>
            have hv := ihn (Relation.EqvGen.rel _ _ hsub).symm
            subst hv
            rfl
      intro u h
      have key_iff : ∀ {x y : BranchingType S L}, BranchingType.PermEquiv x y →
          (x = BranchingType.ofSessionType (L := L) passive (SessionType.send n) ↔
            y = BranchingType.ofSessionType (L := L) passive (SessionType.send n)) := by
        intro x y hxy
        induction hxy with
        | rel x y hstep => exact step_iff hstep
        | refl x => exact Iff.rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
      exact (key_iff h).1 rfl
    | recv n ihn =>
      have step_iff : ∀ {x y : BranchingType S L},
          BranchingType.SwapStep x y →
          (x = BranchingType.ofSessionType (L := L) passive (SessionType.recv n) ↔
            y = BranchingType.ofSessionType (L := L) passive (SessionType.recv n)) := by
        intro x y hstep
        constructor
        · intro hx
          subst hx
          simp only [BranchingType.ofSessionType] at hstep
          cases hstep with
          | recv hsub =>
            have hv := ihn (Relation.EqvGen.rel _ _ hsub)
            subst hv
            rfl
        · intro hy
          subst hy
          simp only [BranchingType.ofSessionType] at hstep
          cases hstep with
          | recv hsub =>
            have hv := ihn (Relation.EqvGen.rel _ _ hsub).symm
            subst hv
            rfl
      intro u h
      have key_iff : ∀ {x y : BranchingType S L}, BranchingType.PermEquiv x y →
          (x = BranchingType.ofSessionType (L := L) passive (SessionType.recv n) ↔
            y = BranchingType.ofSessionType (L := L) passive (SessionType.recv n)) := by
        intro x y hxy
        induction hxy with
        | rel x y hstep => exact step_iff hstep
        | refl x => exact Iff.rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
      exact (key_iff h).1 rfl
  constructor
  · intro h
    exact (BranchingType.ofSessionType_injective passive (key s1 h)).symm
  · intro h
    exact h ▸ BranchingType.PermEquiv.refl _

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

/-- The SessionType projection agrees on PermEquiv types. -/
theorem BranchingType.toSessionType?_eq_of_permEquiv {S L : Type}
    (passive : S) [DecidableEq S]
    {t u : BranchingType S L} :
    BranchingType.PermEquiv t u →
      BranchingType.toSessionType? passive t =
        BranchingType.toSessionType? passive u := by
  have step : ∀ {t u : BranchingType S L}, BranchingType.SwapStep t u →
      BranchingType.toSessionType? passive t =
        BranchingType.toSessionType? passive u := by
    intro t u hstep
    refine BranchingType.SwapStep.rec
      (motive_1 := fun t u _ => BranchingType.toSessionType? passive t =
        BranchingType.toSessionType? passive u)
      (motive_2 := fun _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
    · intro payload next next' step ih
      by_cases h : payload = passive
      · simp only [BranchingType.toSessionType?, ite_eq_left h, ih]
      · simp only [BranchingType.toSessionType?, ite_eq_right h]
    · intro payload next next' step ih
      by_cases h : payload = passive
      · simp only [BranchingType.toSessionType?, ite_eq_left h, ih]
      · simp only [BranchingType.toSessionType?, ite_eq_right h]
    · intro branches branches' step ih
      rfl
    · intro branches branches' step ih
      rfl
    · intro _ _ _ _ _ _
      trivial
    · intro _ _ _ _ _ _
      trivial
    · intro _ _ _ _ _ _
      trivial
  intro h
  induction h with
  | rel x y hstep => exact step hstep
  | refl x => exact rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- The Protocol projection agrees on PermEquiv types. -/
theorem BranchingType.toProtocol?_eq_of_permEquiv {S L : Type}
    (passive : S) [DecidableEq S]
    {t u : BranchingType S L} :
    BranchingType.PermEquiv t u →
      BranchingType.toProtocol? passive t =
        BranchingType.toProtocol? passive u := by
  intro h
  simp only [BranchingType.toProtocol?,
    BranchingType.toSessionType?_eq_of_permEquiv passive h]

/-- Project-specific type-level actions: send, receive, and labelled select/branch. -/
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

/-- Project-specific one-step type advancement (not a source definition); a choice
advances to the continuation of any entry with the chosen label. -/
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

/-- Type advancement simulates across PermEquiv with the same action. -/
theorem BranchingType.Advances.permEquiv_sim {S L : Type}
    {t t' : BranchingType S L} {act : BranchingType.Action L}
    {u : BranchingType S L} :
    BranchingType.PermEquiv t t' → BranchingType.Advances t act u →
      ∃ u' : BranchingType S L, BranchingType.Advances t' act u' ∧
        BranchingType.PermEquiv u u' := by
  have step_sim : ∀ {t t' : BranchingType S L}, BranchingType.SwapStep t t' →
      (∀ {act : BranchingType.Action L} {u : BranchingType S L},
        BranchingType.Advances t act u →
        ∃ u', BranchingType.Advances t' act u' ∧ BranchingType.PermEquiv u u') ∧
      (∀ {act : BranchingType.Action L} {u' : BranchingType S L},
        BranchingType.Advances t' act u' →
        ∃ u, BranchingType.Advances t act u ∧ BranchingType.PermEquiv u' u) := by
    intro t t' hstep
    refine BranchingType.SwapStep.rec
      (motive_1 := fun t t' _ => (∀ {act : BranchingType.Action L}
        {u : BranchingType S L}, BranchingType.Advances t act u →
        ∃ u', BranchingType.Advances t' act u' ∧ BranchingType.PermEquiv u u') ∧
        (∀ {act : BranchingType.Action L} {u' : BranchingType S L},
        BranchingType.Advances t' act u' →
        ∃ u, BranchingType.Advances t act u ∧ BranchingType.PermEquiv u' u))
      (motive_2 := fun _ _ _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstep
    · intro payload next next' step ih
      refine ⟨?_, ?_⟩
      · intro act u hAdv
        cases hAdv with
        | send =>
          exact ⟨next', BranchingType.Advances.send,
            Relation.EqvGen.rel _ _ step⟩
      · intro act u' hAdv
        cases hAdv with
        | send =>
          exact ⟨next, BranchingType.Advances.send,
            BranchingType.PermEquiv.symm (Relation.EqvGen.rel _ _ step)⟩
    · intro payload next next' step ih
      refine ⟨?_, ?_⟩
      · intro act u hAdv
        cases hAdv with
        | recv =>
          exact ⟨next', BranchingType.Advances.recv,
            Relation.EqvGen.rel _ _ step⟩
      · intro act u' hAdv
        cases hAdv with
        | recv =>
          exact ⟨next, BranchingType.Advances.recv,
            BranchingType.PermEquiv.symm (Relation.EqvGen.rel _ _ step)⟩
    · intro branches branches' step ih
      refine ⟨?_, ?_⟩
      · intro act u hAdv
        cases hAdv with
        | select hmem =>
          have hpe : BranchingType.Branches.PermEquiv branches branches' :=
            Relation.EqvGen.rel _ _ step
          obtain ⟨nxt, hmem', hperm⟩ :=
            BranchingType.Branches.PermEquiv.exists_mem hpe hmem
          exact ⟨nxt, BranchingType.Advances.select hmem', hperm⟩
      · intro act u' hAdv
        cases hAdv with
        | select hmem =>
          have hpe : BranchingType.Branches.PermEquiv branches branches' :=
            Relation.EqvGen.rel _ _ step
          obtain ⟨nxt, hmem', hperm⟩ :=
            BranchingType.Branches.PermEquiv.exists_mem hpe.symm hmem
          exact ⟨nxt, BranchingType.Advances.select hmem', hperm⟩
    · intro branches branches' step ih
      refine ⟨?_, ?_⟩
      · intro act u hAdv
        cases hAdv with
        | branch hmem =>
          have hpe : BranchingType.Branches.PermEquiv branches branches' :=
            Relation.EqvGen.rel _ _ step
          obtain ⟨nxt, hmem', hperm⟩ :=
            BranchingType.Branches.PermEquiv.exists_mem hpe hmem
          exact ⟨nxt, BranchingType.Advances.branch hmem', hperm⟩
      · intro act u' hAdv
        cases hAdv with
        | branch hmem =>
          have hpe : BranchingType.Branches.PermEquiv branches branches' :=
            Relation.EqvGen.rel _ _ step
          obtain ⟨nxt, hmem', hperm⟩ :=
            BranchingType.Branches.PermEquiv.exists_mem hpe.symm hmem
          exact ⟨nxt, BranchingType.Advances.branch hmem', hperm⟩
    · intro label1 label2 head1 head2 tail hne
      exact True.intro
    · intro label head head' tail step ih
      exact True.intro
    · intro label head tail tail' step ih
      exact True.intro
  have key : ∀ {t t' : BranchingType S L}, BranchingType.PermEquiv t t' →
      (∀ {act : BranchingType.Action L} {u : BranchingType S L},
        BranchingType.Advances t act u →
        ∃ u', BranchingType.Advances t' act u' ∧ BranchingType.PermEquiv u u') ∧
      (∀ {act : BranchingType.Action L} {u' : BranchingType S L},
        BranchingType.Advances t' act u' →
        ∃ u, BranchingType.Advances t act u ∧ BranchingType.PermEquiv u' u) := by
    intro t t' h
    induction h with
    | rel x y hstep => exact step_sim hstep
    | refl x =>
      refine ⟨?_, ?_⟩
      · intro act u hAdv
        exact ⟨u, hAdv, BranchingType.PermEquiv.refl u⟩
      · intro act u' hAdv
        exact ⟨u', hAdv, BranchingType.PermEquiv.refl u'⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih1 ih2 =>
      refine ⟨?_, ?_⟩
      · intro act u hAdv
        obtain ⟨u1, hAdv1, hpe1⟩ := ih1.1 hAdv
        obtain ⟨u2, hAdv2, hpe2⟩ := ih2.1 hAdv1
        exact ⟨u2, hAdv2, BranchingType.PermEquiv.trans hpe1 hpe2⟩
      · intro act u2 hAdv
        obtain ⟨u1, hAdv1, hpe1⟩ := ih2.2 hAdv
        obtain ⟨u0, hAdv0, hpe0⟩ := ih1.2 hAdv1
        exact ⟨u0, hAdv0, BranchingType.PermEquiv.trans hpe1 hpe0⟩
  intro h hAdv
  exact (key h).1 hAdv

/-- Finite partial map from `Nat` channels to types, as the typings in the paragraph
after Def 5.1; absence means no obligation. -/
abbrev BranchingContext (S L : Type) := Finmap (fun _ : Nat => BranchingType S L)

namespace BranchingContext
/-- Dualize every obligation, preserving keys. -/
def dual {S L : Type} (Γ : BranchingContext S L) : BranchingContext S L :=
  { entries := Γ.entries.map (fun x => ⟨x.1, x.2.dual⟩)
    nodupKeys := by
      apply Multiset.nodup_keys.mp
      have h : Γ.entries.keys.Nodup := Γ.nodupKeys.nodup_keys
      simpa [Multiset.keys, Multiset.map_map, Function.comp_def] using h }

/-- Pointwise source equality of contexts; lookups are related at every channel. -/
def PermEquiv {S L : Type} (Γ Δ : BranchingContext S L) : Prop :=
  ∀ a : Nat, Option.Rel BranchingType.PermEquiv (Γ.lookup a) (Δ.lookup a)

/-- Context PermEquiv is reflexive. -/
theorem PermEquiv.refl {S L : Type}
    (Γ : BranchingContext S L) :
    BranchingContext.PermEquiv Γ Γ := by
  intro a
  cases hg : Γ.lookup a with
  | none => exact Option.Rel.none
  | some t => exact Option.Rel.some (BranchingType.PermEquiv.refl t)

/-- Context PermEquiv is symmetric. -/
theorem PermEquiv.symm {S L : Type}
    {Γ Δ : BranchingContext S L} :
    BranchingContext.PermEquiv Γ Δ →
      BranchingContext.PermEquiv Δ Γ := by
  intro h a
  cases hg : Γ.lookup a with
  | none =>
    cases hd : Δ.lookup a with
    | none => exact Option.Rel.none
    | some t =>
      have hr := h a
      rw [hg, hd] at hr
      cases hr
  | some s =>
    cases hd : Δ.lookup a with
    | none =>
      have hr := h a
      rw [hg, hd] at hr
      cases hr
    | some t =>
      have hr := h a
      rw [hg, hd] at hr
      cases hr with
      | some hinner =>
        exact Option.Rel.some (BranchingType.PermEquiv.symm hinner)

/-- Context PermEquiv is transitive. -/
theorem PermEquiv.trans {S L : Type}
    {Γ Δ Θ : BranchingContext S L} :
    BranchingContext.PermEquiv Γ Δ →
      BranchingContext.PermEquiv Δ Θ →
        BranchingContext.PermEquiv Γ Θ := by
  intro h1 h2 a
  cases hg : Γ.lookup a with
  | none =>
    cases hd : Δ.lookup a with
    | none =>
      cases ht : Θ.lookup a with
      | none => exact Option.Rel.none
      | some u =>
        have hr := h2 a
        rw [hd, ht] at hr
        cases hr
    | some v =>
      have hr := h1 a
      rw [hg, hd] at hr
      cases hr
  | some s =>
    cases hd : Δ.lookup a with
    | none =>
      have hr := h1 a
      rw [hg, hd] at hr
      cases hr
    | some v =>
      cases ht : Θ.lookup a with
      | none =>
        have hr := h2 a
        rw [hd, ht] at hr
        cases hr
      | some u =>
        have hr1 := h1 a
        rw [hg, hd] at hr1
        have hr2 := h2 a
        rw [hd, ht] at hr2
        cases hr1 with
        | some hinner1 =>
          cases hr2 with
          | some hinner2 =>
            exact Option.Rel.some
              (BranchingType.PermEquiv.trans hinner1 hinner2)

/-- Context PermEquiv is preserved by duality. -/
theorem PermEquiv.dual {S L : Type}
    {Γ Δ : BranchingContext S L} :
    BranchingContext.PermEquiv Γ Δ →
      BranchingContext.PermEquiv (BranchingContext.dual Γ)
        (BranchingContext.dual Δ) := by
  have mem_dual_local : ∀ (Γ : BranchingContext S L) (a : Nat),
      a ∈ BranchingContext.dual Γ ↔ a ∈ Γ := by
    intro Γ a
    simp only [Finmap.mem_def, BranchingContext.dual, Multiset.keys,
      Multiset.map_map, Function.comp_def]
  have lookup_dual_local : ∀ (Γ : BranchingContext S L) (a : Nat),
      (BranchingContext.dual Γ).lookup a =
        (Γ.lookup a).map BranchingType.dual := by
    intro Γ a
    cases h : Γ.lookup a with
    | none =>
      simp only [Option.map_none]
      exact Finmap.lookup_eq_none.mpr (by
        rw [mem_dual_local]
        exact Finmap.lookup_eq_none.mp h)
    | some t =>
      have hmem := Finmap.lookup_eq_some_iff.mp h
      have hmem' : Sigma.mk a t.dual ∈ (BranchingContext.dual Γ).entries := by
        simp only [BranchingContext.dual]
        exact Multiset.mem_map_of_mem (fun x : Sigma (fun _ : Nat => BranchingType S L) =>
          (Sigma.mk x.1 x.2.dual : Sigma (fun _ : Nat => BranchingType S L))) hmem
      have hdual := Finmap.lookup_eq_some_iff.mpr hmem'
      rw [hdual, Option.map_some]
  intro h a
  rw [lookup_dual_local, lookup_dual_local]
  cases hg : Γ.lookup a with
  | none =>
    cases hd : Δ.lookup a with
    | none => exact Option.Rel.none
    | some t =>
      have hr := h a
      rw [hg, hd] at hr
      cases hr
  | some s =>
    cases hd : Δ.lookup a with
    | none =>
      have hr := h a
      rw [hg, hd] at hr
      cases hr
    | some t =>
      have hr := h a
      rw [hg, hd] at hr
      cases hr with
      | some hinner =>
        exact Option.Rel.some (BranchingType.PermEquiv.dual hinner)

/-- Project-specific disjoint ownership split: the whole is `PermEquiv` to the union of
two contexts with disjoint domains. Not the Def 5.2 composition, which marks shared
channels `⊥`. -/
def Split {S L : Type} (Γ Δ Θ : BranchingContext S L) : Prop :=
  BranchingContext.PermEquiv Γ (Δ ∪ Θ) ∧ Finmap.Disjoint Δ Θ

/-- Ownership splits transport across context PermEquiv. -/
theorem Split.permEquiv {S L : Type}
    {Γ Γ' Δ Δ' Θ Θ' : BranchingContext S L} :
    BranchingContext.PermEquiv Γ Γ' →
      BranchingContext.PermEquiv Δ Δ' →
        BranchingContext.PermEquiv Θ Θ' →
          Split Γ Δ Θ → Split Γ' Δ' Θ' := by
  intro hΓ hΔ hΘ hsplit
  obtain ⟨hS, hdisj⟩ := hsplit
  have hunion : BranchingContext.PermEquiv (Δ ∪ Θ) (Δ' ∪ Θ') := by
    intro b
    by_cases hb : b ∈ Δ
    · have hb' : b ∈ Δ' := by
        cases hd : Δ.lookup b with
        | none =>
          have hcon : b ∉ Δ := Finmap.lookup_eq_none.mp hd
          exact False.elim (hcon hb)
        | some v =>
          cases hd' : Δ'.lookup b with
          | none =>
            have hR := hΔ b
            rw [hd, hd'] at hR
            cases hR
          | some v' =>
            by_contra hn
            rw [Finmap.lookup_eq_none.mpr hn] at hd'
            cases hd'
      have hU : (Δ ∪ Θ).lookup b = Δ.lookup b :=
        Finmap.lookup_union_left hb
      have hU' : (Δ' ∪ Θ').lookup b = Δ'.lookup b :=
        Finmap.lookup_union_left hb'
      rw [hU, hU']
      exact hΔ b
    · have hΔnone : Δ.lookup b = none :=
        Finmap.lookup_eq_none.mpr hb
      cases hd' : Δ'.lookup b with
      | some v' =>
        have hR := hΔ b
        rw [hΔnone, hd'] at hR
        cases hR
      | none =>
        have hb' : b ∉ Δ' := Finmap.lookup_eq_none.mp hd'
        have hU : (Δ ∪ Θ).lookup b = Θ.lookup b :=
          Finmap.lookup_union_right hb
        have hU' : (Δ' ∪ Θ').lookup b = Θ'.lookup b :=
          Finmap.lookup_union_right hb'
        rw [hU, hU']
        exact hΘ b
  have hΓ' : BranchingContext.PermEquiv Γ' (Δ' ∪ Θ') :=
    hΓ.symm.trans (hS.trans hunion)
  have hdisj' : Finmap.Disjoint Δ' Θ' := by
    intro x hx1 hx2
    have hxΔ : x ∈ Δ := by
      cases hd : Δ.lookup x with
      | some v =>
        by_contra hn
        rw [Finmap.lookup_eq_none.mpr hn] at hd
        cases hd
      | none =>
        cases hd' : Δ'.lookup x with
        | none =>
          have hcon : x ∉ Δ' := Finmap.lookup_eq_none.mp hd'
          exact False.elim (hcon hx1)
        | some v' =>
          have hR := hΔ x
          rw [hd, hd'] at hR
          cases hR
    have hxΘ : x ∈ Θ := by
      cases ht : Θ.lookup x with
      | some v =>
        by_contra hn
        rw [Finmap.lookup_eq_none.mpr hn] at ht
        cases ht
      | none =>
        cases ht' : Θ'.lookup x with
        | none =>
          have hcon : x ∉ Θ' := Finmap.lookup_eq_none.mp ht'
          exact False.elim (hcon hx2)
        | some v' =>
          have hR := hΘ x
          rw [ht, ht'] at hR
          cases hR
    exact hdisj x hxΔ hxΘ
  exact ⟨hΓ', hdisj'⟩

/-- Project-specific: advance channel `a` by one action, updating its obligation; the
result is taken up to `PermEquiv`. -/
def Advances {S L : Type} (Γ : BranchingContext S L) (a : Nat)
    (act : BranchingType.Action L) (Δ : BranchingContext S L) : Prop :=
  ∃ t u, Γ.lookup a = some t ∧ BranchingType.Advances t act u ∧
    BranchingContext.PermEquiv Δ (Γ.insert a u)

/-- Context advancement transports across context PermEquiv. -/
theorem Advances.permEquiv {S L : Type}
    {Γ Γ' Δ Δ' : BranchingContext S L} (a : Nat)
    {act : BranchingType.Action L} :
    BranchingContext.PermEquiv Γ Γ' →
      BranchingContext.PermEquiv Δ Δ' →
        Advances Γ a act Δ → Advances Γ' a act Δ' := by
  intro hΓ hΔ h
  obtain ⟨t, u, hl, hty, hpe⟩ := h
  have hex : ∃ t', Γ'.lookup a = some t' ∧
      BranchingType.PermEquiv t t' := by
    cases hg' : Γ'.lookup a with
    | none =>
      have hGa := hΓ a
      rw [hl, hg'] at hGa
      cases hGa
    | some t' =>
      have hGa := hΓ a
      rw [hl, hg'] at hGa
      cases hGa with
      | some ht =>
        exact ⟨t', rfl, ht⟩
  obtain ⟨t', hl', ht't⟩ := hex
  obtain ⟨u', hadv', hu'⟩ :=
    BranchingType.Advances.permEquiv_sim ht't hty
  have hinsert : BranchingContext.PermEquiv (Γ.insert a u)
      (Γ'.insert a u') := by
    intro b
    by_cases hb : b = a
    · rw [hb]
      have hL : (Γ.insert a u).lookup a = some u :=
        Finmap.lookup_insert Γ
      have hR : (Γ'.insert a u').lookup a = some u' :=
        Finmap.lookup_insert Γ'
      rw [hL, hR]
      exact Option.Rel.some hu'
    · have hL : (Γ.insert a u).lookup b = Γ.lookup b :=
        Finmap.lookup_insert_of_ne Γ hb
      have hR : (Γ'.insert a u').lookup b = Γ'.lookup b :=
        Finmap.lookup_insert_of_ne Γ' hb
      rw [hL, hR]
      exact hΓ b
  exact ⟨t', u', hl', hadv', (hΔ.symm.trans (hpe.trans hinsert))⟩

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
  obtain ⟨hpe, hdisj⟩ := h
  have hunion : BranchingContext.PermEquiv (BranchingContext.dual (Δ ∪ Θ))
      (BranchingContext.dual Δ ∪ BranchingContext.dual Θ) := by
    intro a
    rw [lookup_dual]
    by_cases ha : a ∈ Δ
    · have hU : (Δ ∪ Θ).lookup a = Δ.lookup a := Finmap.lookup_union_left ha
      have ha' : a ∈ BranchingContext.dual Δ := (mem_dual Δ a).mpr ha
      have hU' : (BranchingContext.dual Δ ∪ BranchingContext.dual Θ).lookup a =
          (BranchingContext.dual Δ).lookup a := Finmap.lookup_union_left ha'
      have hD : (BranchingContext.dual Δ).lookup a =
          (Δ.lookup a).map BranchingType.dual := lookup_dual Δ a
      rw [hU, hU', hD]
      cases hd : Δ.lookup a with
      | none => exact Option.Rel.none
      | some v => exact Option.Rel.some (BranchingType.PermEquiv.refl _)
    · have hU : (Δ ∪ Θ).lookup a = Θ.lookup a := Finmap.lookup_union_right ha
      have ha' : a ∉ BranchingContext.dual Δ :=
        fun hcon => ha ((mem_dual Δ a).mp hcon)
      have hU' : (BranchingContext.dual Δ ∪ BranchingContext.dual Θ).lookup a =
          (BranchingContext.dual Θ).lookup a := Finmap.lookup_union_right ha'
      have hD : (BranchingContext.dual Θ).lookup a =
          (Θ.lookup a).map BranchingType.dual := lookup_dual Θ a
      rw [hU, hU', hD]
      cases ht : Θ.lookup a with
      | none => exact Option.Rel.none
      | some v => exact Option.Rel.some (BranchingType.PermEquiv.refl _)
  exact ⟨(PermEquiv.dual hpe).trans hunion, disjoint_dual Δ Θ hdisj⟩
/-- Advancement preserves every other channel up to permutation equivalence:
for `b ≠ a` the lookups are both absent or both present with `PermEquiv`
types. -/
theorem Advances.lookup_of_ne {S L : Type} (Γ Δ : BranchingContext S L)
    (a b : Nat) (act : BranchingType.Action L)
    (h : Advances Γ a act Δ) (hne : b ≠ a) :
    Option.Rel BranchingType.PermEquiv (Δ.lookup b)
      (Γ.lookup b) := by
  obtain ⟨t, u, hlook, hadv, hpe⟩ := h
  have hb := hpe b
  have hins : (Γ.insert a u).lookup b = Γ.lookup b :=
    Finmap.lookup_insert_of_ne Γ hne
  rw [hins] at hb
  exact hb
/-- Advancement preserves disjointness on the left. -/
theorem Advances.disjoint_left {S L : Type} (Γ Γ' Θ : BranchingContext S L)
    (a : Nat) (act : BranchingType.Action L)
    (hdisj : Finmap.Disjoint Γ Θ) (h : Advances Γ a act Γ') :
    Finmap.Disjoint Γ' Θ := by
  obtain ⟨t, u, hlook, _, hpe⟩ := h
  intro x hx1 hx2
  have hne1 : Γ'.lookup x ≠ none :=
    fun hnone => (Finmap.lookup_eq_none.mp hnone) hx1
  have hrel := hpe x
  cases hg' : Γ'.lookup x with
  | none =>
    exact hne1 hg'
  | some _ =>
    cases hins : (Γ.insert a u).lookup x with
    | none =>
      rw [hg', hins] at hrel
      cases hrel
    | some w =>
      have hmem : x ∈ Γ.insert a u := by
        by_contra hn
        rw [Finmap.lookup_eq_none.mpr hn] at hins
        cases hins
      have hor : x = a ∨ x ∈ Γ :=
        Finmap.mem_insert.mp hmem
      cases hor with
      | inl heq =>
        have hmemA : a ∈ Γ := by
          by_contra hn
          rw [Finmap.lookup_eq_none.mpr hn] at hlook
          cases hlook
        exact hdisj a hmemA (heq ▸ hx2)
      | inr hmemG =>
        exact hdisj x hmemG hx2
/-- If `Γ` splits into `Δ` and `Θ` and `Δ` advances at channel `a` by `act` to `Δ'`, then `Γ`
advances at `a` by `act` to `Δ' ∪ Θ`, and `Δ' ∪ Θ` splits into `Δ'` and `Θ`. -/
theorem Split.advance_left {S L : Type} (Γ Δ Δ' Θ : BranchingContext S L)
    (a : Nat) (act : BranchingType.Action L) (h : Split Γ Δ Θ)
    (hadv : Advances Δ a act Δ') :
    Advances Γ a act (Δ' ∪ Θ) ∧ Split (Δ' ∪ Θ) Δ' Θ := by
  obtain ⟨hΓ, hdisj⟩ := h
  obtain ⟨t, u, hlΔ, hty, hΔ'⟩ := hadv
  have haΔ : a ∈ Δ := by
    by_contra hn
    have := Finmap.lookup_eq_none.mpr hn
    rw [hlΔ] at this
    cases this
  have hU : (Δ ∪ Θ).lookup a = Δ.lookup a :=
    Finmap.lookup_union_left haΔ
  have hex : ∃ t0, Γ.lookup a = some t0 ∧
      BranchingType.PermEquiv t0 t := by
    cases hg : Γ.lookup a with
    | none =>
      have hΓa := hΓ a
      rw [hU, hlΔ, hg] at hΓa
      cases hΓa
    | some t0 =>
      have hΓa := hΓ a
      rw [hU, hlΔ, hg] at hΓa
      cases hΓa with
      | some ht0 =>
        exact ⟨t0, rfl, ht0⟩
  obtain ⟨t0, hΓlook, ht0⟩ := hex
  obtain ⟨u0, hadv0, hu0⟩ :=
    BranchingType.Advances.permEquiv_sim
      (BranchingType.PermEquiv.symm ht0) hty
  have hperm : BranchingContext.PermEquiv (Δ' ∪ Θ)
      (Γ.insert a u0) := by
    intro b
    by_cases heq : b = a
    · rw [heq]
      cases hd' : Δ'.lookup a with
      | none =>
        have hinsA : (Δ.insert a u).lookup a = some u :=
          Finmap.lookup_insert Δ
        have hR := hΔ' a
        rw [hinsA, hd'] at hR
        cases hR
      | some u1 =>
        have hinsA : (Δ.insert a u).lookup a = some u :=
          Finmap.lookup_insert Δ
        have hR := hΔ' a
        rw [hinsA, hd'] at hR
        cases hR with
        | some hu1 =>
          have haD : a ∈ Δ' := by
            by_contra hn
            have := Finmap.lookup_eq_none.mpr hn
            rw [hd'] at this
            cases this
          have hUL : (Δ' ∪ Θ).lookup a = Δ'.lookup a :=
            Finmap.lookup_union_left haD
          have hinsG : (Γ.insert a u0).lookup a = some u0 :=
            Finmap.lookup_insert Γ
          rw [hUL, hd', hinsG]
          have h12 : BranchingType.PermEquiv u1 u0 :=
            BranchingType.PermEquiv.trans hu1 hu0
          exact Option.Rel.some h12
    · have hne : b ≠ a := heq
      by_cases hb : b ∈ Δ'
      · have hbΔ : b ∈ Δ := by
          cases hd' : Δ'.lookup b with
          | none =>
            have hcon : b ∉ Δ' :=
              Finmap.lookup_eq_none.mp hd'
            exact False.elim (hcon hb)
          | some _ =>
            cases hd : Δ.lookup b with
            | none =>
              have hInsB : (Δ.insert a u).lookup b =
                  Δ.lookup b :=
                Finmap.lookup_insert_of_ne Δ hne
              have hR1 := hΔ' b
              rw [hInsB, hd', hd] at hR1
              cases hR1
            | some v2 =>
              by_contra hn
              rw [Finmap.lookup_eq_none.mpr hn] at hd
              cases hd
        cases hd' : Δ'.lookup b with
        | none =>
          have hcon : b ∉ Δ' :=
            Finmap.lookup_eq_none.mp hd'
          exact False.elim (hcon hb)
        | some v1 =>
          cases hd : Δ.lookup b with
          | none =>
            have hInsB : (Δ.insert a u).lookup b =
                Δ.lookup b :=
              Finmap.lookup_insert_of_ne Δ hne
            have hR1 := hΔ' b
            rw [hInsB, hd', hd] at hR1
            cases hR1
          | some v2 =>
            cases hg : Γ.lookup b with
            | none =>
              have hUΔ : (Δ ∪ Θ).lookup b = Δ.lookup b :=
                Finmap.lookup_union_left hbΔ
              have hR2 := hΓ b
              rw [hUΔ, hd, hg] at hR2
              cases hR2
            | some w =>
              have hUL' : (Δ' ∪ Θ).lookup b = Δ'.lookup b :=
                Finmap.lookup_union_left hb
              have hRHS : (Γ.insert a u0).lookup b =
                  Γ.lookup b :=
                Finmap.lookup_insert_of_ne Γ hne
              have hUΔ : (Δ ∪ Θ).lookup b = Δ.lookup b :=
                Finmap.lookup_union_left hbΔ
              have hInsB : (Δ.insert a u).lookup b =
                  Δ.lookup b :=
                Finmap.lookup_insert_of_ne Δ hne
              have hR1 := hΔ' b
              rw [hInsB, hd', hd] at hR1
              have hR2 := hΓ b
              rw [hUΔ, hd, hg] at hR2
              rw [hUL', hRHS, hd', hg]
              cases hR1 with
              | some h1 =>
                cases hR2 with
                | some h2 =>
                  have h2s : BranchingType.PermEquiv v2 w :=
                    BranchingType.PermEquiv.symm h2
                  have h12 : BranchingType.PermEquiv v1 w :=
                    BranchingType.PermEquiv.trans h1 h2s
                  exact Option.Rel.some h12
      · have hΔnone : Δ.lookup b = none := by
          cases hd : Δ.lookup b with
          | none =>
            exact rfl
          | some _ =>
            cases hd' : Δ'.lookup b with
            | none =>
              have hInsB : (Δ.insert a u).lookup b =
                  Δ.lookup b :=
                Finmap.lookup_insert_of_ne Δ hne
              have hR1 := hΔ' b
              rw [hInsB, hd, hd'] at hR1
              cases hR1
            | some v1 =>
              have hmem : b ∈ Δ' := by
                by_contra hn
                rw [Finmap.lookup_eq_none.mpr hn] at hd'
                cases hd'
              exact False.elim (hb hmem)
        have hbND : b ∉ Δ :=
          Finmap.lookup_eq_none.mp hΔnone
        cases ht : Θ.lookup b with
        | none =>
          cases hg : Γ.lookup b with
          | none =>
            have hUL'' : (Δ' ∪ Θ).lookup b = Θ.lookup b :=
              Finmap.lookup_union_right hb
            have hRHS : (Γ.insert a u0).lookup b =
                Γ.lookup b :=
              Finmap.lookup_insert_of_ne Γ hne
            rw [hUL'', hRHS, ht, hg]
            exact Option.Rel.none
          | some _ =>
            have hUΘ : (Δ ∪ Θ).lookup b = Θ.lookup b :=
              Finmap.lookup_union_right hbND
            have hR2 := hΓ b
            rw [hUΘ, ht, hg] at hR2
            cases hR2
        | some _ =>
          cases hg : Γ.lookup b with
          | none =>
            have hUΘ : (Δ ∪ Θ).lookup b = Θ.lookup b :=
              Finmap.lookup_union_right hbND
            have hR2 := hΓ b
            rw [hUΘ, ht, hg] at hR2
            cases hR2
          | some _ =>
            have hUL'' : (Δ' ∪ Θ).lookup b = Θ.lookup b :=
              Finmap.lookup_union_right hb
            have hRHS : (Γ.insert a u0).lookup b =
                Γ.lookup b :=
              Finmap.lookup_insert_of_ne Γ hne
            have hUΘ : (Δ ∪ Θ).lookup b = Θ.lookup b :=
              Finmap.lookup_union_right hbND
            have hR2 := hΓ b
            rw [hUΘ, ht, hg] at hR2
            rw [hUL'', hRHS, ht, hg]
            cases hR2 with
            | some hinner =>
              exact Option.Rel.some
                (BranchingType.PermEquiv.symm hinner)
  have hsplit : Split (Δ' ∪ Θ) Δ' Θ :=
    ⟨BranchingContext.PermEquiv.refl _,
      Advances.disjoint_left Δ Δ' Θ a act hdisj ⟨t, u, hlΔ, hty, hΔ'⟩⟩
  exact ⟨⟨t0, u0, hΓlook, hadv0, hperm⟩, hsplit⟩
/-- Dual contexts advance by dual actions. -/
theorem Advances.dual {S L : Type} (Γ Δ : BranchingContext S L) (a : Nat)
    (act : BranchingType.Action L) (h : Advances Γ a act Δ) :
    Advances (BranchingContext.dual Γ) a act.dual
      (BranchingContext.dual Δ) := by
  obtain ⟨t, u, hl, hty, hpe⟩ := h
  have hlook_d : (BranchingContext.dual Γ).lookup a = some t.dual := by
    rw [lookup_dual, hl, Option.map_some]
  have hperm_d : BranchingContext.PermEquiv (BranchingContext.dual Δ)
      ((BranchingContext.dual Γ).insert a u.dual) := by
    intro b
    rw [lookup_dual]
    by_cases hb : b = a
    · rw [hb]
      cases hd : Δ.lookup a with
      | none =>
        have hinsG : (Γ.insert a u).lookup a = some u :=
          Finmap.lookup_insert Γ
        have hR := hpe a
        rw [hinsG, hd] at hR
        cases hR
      | some _ =>
        have hinsG : (Γ.insert a u).lookup a = some u :=
          Finmap.lookup_insert Γ
        have hR := hpe a
        rw [hinsG, hd] at hR
        cases hR with
        | some hu1 =>
          have hinsR : ((BranchingContext.dual Γ).insert a u.dual).lookup a =
              some u.dual :=
            Finmap.lookup_insert (BranchingContext.dual Γ)
          rw [hinsR, Option.map_some]
          exact Option.Rel.some (BranchingType.PermEquiv.dual hu1)
    · have hne : b ≠ a := hb
      cases hd : Δ.lookup b with
      | none =>
        cases hg : Γ.lookup b with
        | none =>
          have hinsR : ((BranchingContext.dual Γ).insert a u.dual).lookup b =
              (BranchingContext.dual Γ).lookup b :=
            Finmap.lookup_insert_of_ne _ hne
          have hdualG : (BranchingContext.dual Γ).lookup b =
              (Γ.lookup b).map BranchingType.dual :=
            lookup_dual Γ b
          rw [hinsR, hdualG, hg]
          simp only [Option.map_none]
          exact Option.Rel.none
        | some _ =>
          have hinsG : (Γ.insert a u).lookup b = Γ.lookup b :=
            Finmap.lookup_insert_of_ne Γ hne
          have hR := hpe b
          rw [hinsG, hd, hg] at hR
          cases hR
      | some _ =>
        cases hg : Γ.lookup b with
        | none =>
          have hinsG : (Γ.insert a u).lookup b = Γ.lookup b :=
            Finmap.lookup_insert_of_ne Γ hne
          have hR := hpe b
          rw [hinsG, hd, hg] at hR
          cases hR
        | some _ =>
          have hinsR : ((BranchingContext.dual Γ).insert a u.dual).lookup b =
              (BranchingContext.dual Γ).lookup b :=
            Finmap.lookup_insert_of_ne _ hne
          have hdualG : (BranchingContext.dual Γ).lookup b =
              (Γ.lookup b).map BranchingType.dual :=
            lookup_dual Γ b
          have hinsG : (Γ.insert a u).lookup b = Γ.lookup b :=
            Finmap.lookup_insert_of_ne Γ hne
          have hR := hpe b
          rw [hinsG, hd, hg] at hR
          cases hR with
          | some hinner =>
            rw [hinsR, hdualG, hg]
            simp only [Option.map_some]
            exact Option.Rel.some
              (BranchingType.PermEquiv.dual hinner)
  exact ⟨t.dual, u.dual, hlook_d,
    BranchingType.Advances.dual t act u hty, hperm_d⟩

end BranchingContext

end Cslib.SessionTypes
