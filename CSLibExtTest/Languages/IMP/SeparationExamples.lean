/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Separation-logic examples: cell swap and in-place list reversal
-/
module

public import CSLibExt.Languages.IMP.SeparationAPI

/-!
# Canonical separation-logic examples

Two worked examples over the heap IMP separation logic:

* **Cell swap**: swapping the contents of two heap cells, proved for the
  two cells in isolation and then transported under an arbitrary frame by
  the frame rule.
* **List reversal** (Reynolds' example): an in-place reversal loop for a
  singly-linked list whose nodes store only their successor address
  (address `0` is null), verified against a list-segment predicate.

Variable conventions: swap keeps the two addresses in variables `0` and
`1` and uses `2`, `3` as scratch; reversal keeps the current pointer `i`
in variable `0`, the reversed prefix head `j` in variable `1`, and a
temporary `t` in variable `2`.
-/

@[expose] public section

namespace Cslib.IMP.Tests.SepExamples

open HAssertion

open scoped HAssertion

/-! ## Local packaging over the reversal witnesses -/

/-- The reversal stages carry five existential witnesses (head,
successor, frame head, tail list, accumulated list); package them by
nesting the generic `SepValid.exists`. -/
theorem SepValid.exists5
    {P Q : Nat → Nat → Nat → List Nat → List Nat → HAssertion}
    {c : HeapCmd}
    (hstep : ∀ x nxt j0 rem' rev,
      SepValid (P x nxt j0 rem' rev) c (Q x nxt j0 rem' rev)) :
    SepValid (fun s h => ∃ x nxt j0 rem' rev, P x nxt j0 rem' rev s h) c
      (fun s h => ∃ x nxt j0 rem' rev, Q x nxt j0 rem' rev s h) :=
  SepValid.exists fun x =>
    SepValid.exists fun nxt =>
      SepValid.exists fun j0 =>
        SepValid.exists fun rem' =>
          SepValid.exists fun rev => hstep x nxt j0 rem' rev

/-! ## Swapping two heap cells -/

/-- Swap the contents of the cells whose addresses sit in variables `0`
and `1`: read both cells into scratch variables `2` and `3`, then write
each value back into the other cell. -/
def swapCmd : HeapCmd :=
  .seq (.read 2 (.var 0))
    (.seq (.read 3 (.var 1))
      (.seq (.write (.var 0) (.var 3)) (.write (.var 1) (.var 2))))

/-- Unframed swap. No distinctness hypothesis on the addresses is needed:
when `x = y` the precondition `pointsTo x a ⋆ pointsTo x b` is
unsatisfiable, so the triple holds anyway. -/
theorem swap_two_cells {x y a b : Nat} :
    SepValid (fun s h => (s 0 = x ∧ s 1 = y) ∧
        (pointsTo x a ⋆ pointsTo y b) s h)
      swapCmd
      (fun s h => (s 0 = x ∧ s 1 = y) ∧
        (pointsTo x b ⋆ pointsTo y a) s h) := by
  have step1 : SepValid
      (fun s h => (s 0 = x ∧ s 1 = y) ∧
        (pointsTo x a ⋆ pointsTo y b) s h)
      (.read 2 (.var 0))
      (fun s h => (s 0 = x ∧ s 1 = y ∧ s 2 = a) ∧
        (pointsTo x a ⋆ pointsTo y b) s h) :=
    read_framed pointsTo_storeIrrel (by
      intro s hp
      obtain ⟨h0, h1⟩ := hp
      refine ⟨h0, ?_, ?_, ?_⟩
      · simp [h0]
      · simp [h1]
      · simp)
  have step2 : SepValid
      (fun s h => (s 0 = x ∧ s 1 = y ∧ s 2 = a) ∧
        (pointsTo x a ⋆ pointsTo y b) s h)
      (.read 3 (.var 1))
      (fun s h => (s 0 = x ∧ s 1 = y ∧ s 2 = a ∧ s 3 = b) ∧
        (pointsTo y b ⋆ pointsTo x a) s h) :=
    SepValid.consequence (entails_and_right HAssertion.star_comm)
      (read_framed pointsTo_storeIrrel (by
        intro s hp
        obtain ⟨h0, h1, h2⟩ := hp
        refine ⟨h1, ?_, ?_, ?_, ?_⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp))
      (HAssertion.entails_refl _)
  have step3 : SepValid
      (fun s h => (s 0 = x ∧ s 1 = y ∧ s 2 = a ∧ s 3 = b) ∧
        (pointsTo y b ⋆ pointsTo x a) s h)
      (.write (.var 0) (.var 3))
      (fun s h => (s 0 = x ∧ s 1 = y ∧ s 2 = a ∧ s 3 = b) ∧
        (pointsTo x b ⋆ pointsTo y b) s h) :=
    SepValid.consequence (entails_and_right HAssertion.star_comm)
      (write_framed pointsTo_storeIrrel (by
        intro s hp
        obtain ⟨h0, h1, h2, h3⟩ := hp
        exact ⟨⟨h0, h1, h2, h3⟩, h0, h3⟩))
      (HAssertion.entails_refl _)
  have step4 : SepValid
      (fun s h => (s 0 = x ∧ s 1 = y ∧ s 2 = a ∧ s 3 = b) ∧
        (pointsTo x b ⋆ pointsTo y b) s h)
      (.write (.var 1) (.var 2))
      (fun s h => (s 0 = x ∧ s 1 = y) ∧
        (pointsTo x b ⋆ pointsTo y a) s h) :=
    SepValid.consequence (entails_and_right HAssertion.star_comm)
      (write_framed pointsTo_storeIrrel (by
        intro s hp
        obtain ⟨h0, h1, h2, h3⟩ := hp
        exact ⟨⟨h0, h1⟩, h1, h2⟩))
      (entails_and_right HAssertion.star_comm)
  exact SepValid.seq step1 (SepValid.seq step2 (SepValid.seq step3 step4))

/-- Framed swap: the point of the example. The unframed triple plus
`SepValid.frame` gives the swap under any frame `R` that does not depend
on the variables `swapCmd` modifies (the scratch variables `2` and `3`;
this is automatic when `R` is store-irrelevant, e.g. built from
`pointsTo`). -/
theorem swap_two_cells_frame {x y a b : Nat} {R : HAssertion}
    (hR : ∀ ⦃s : State⦄ ⦃h : Heap⦄ ⦃s' : State⦄, R s h →
      (∀ v, v ∉ swapCmd.modVars → s' v = s v) → R s' h) :
    SepValid (fun s h => (s 0 = x ∧ s 1 = y) ∧
        (pointsTo x a ⋆ pointsTo y b ⋆ R) s h)
      swapCmd
      (fun s h => (s 0 = x ∧ s 1 = y) ∧
        (pointsTo x b ⋆ pointsTo y a ⋆ R) s h) :=
  SepValid.consequence
    ((entails_and_right
      (entails_of_eq HAssertion.star_assoc.symm)).trans
      (entails_of_eq star_and_left.symm))
    (SepValid.frame swap_two_cells hR)
    ((entails_of_eq star_and_left).trans
      (entails_and_right (entails_of_eq HAssertion.star_assoc)))

/-! ## Singly-linked lists over addresses -/

/-- List segment from `start` to `finish` through the node addresses
`xs`, in order. Each node `x` is a single heap cell holding the address
of the next node (or `finish` for the last node); nodes are never the
null address `0`. The empty segment is the empty heap with
`start = finish`. -/
def Lseg (start finish : Nat) : List Nat → HAssertion
  | [] => fun _ h => start = finish ∧ h = ∅
  | x :: xs => fun s h => start = x ∧ x ≠ 0 ∧
      ∃ nxt, (pointsTo x nxt ⋆ Lseg nxt finish xs) s h

/-- A null-terminated list: a segment ending at the null address `0`.
`IsList a xs` says the heap is exactly the chain of cells at the
addresses `xs`, entered at `a` (so `a` is the first address, or `0` when
`xs` is empty), each cell storing the next address, the last storing
`0`. -/
def IsList (head : Nat) (xs : List Nat) : HAssertion :=
  Lseg head 0 xs

theorem lseg_nil_iff {a f : Nat} {s : State} {h : Heap} :
    Lseg a f [] s h ↔ a = f ∧ h = ∅ :=
  Iff.rfl

theorem lseg_cons_iff {a f x : Nat} {xs : List Nat} {s : State}
    {h : Heap} :
    Lseg a f (x :: xs) s h ↔
      a = x ∧ x ≠ 0 ∧ ∃ nxt, (pointsTo x nxt ⋆ Lseg nxt f xs) s h :=
  Iff.rfl

theorem isList_nil_iff {a : Nat} {s : State} {h : Heap} :
    IsList a [] s h ↔ a = 0 ∧ h = ∅ :=
  lseg_nil_iff

theorem isList_cons_iff {a x : Nat} {xs : List Nat} {s : State}
    {h : Heap} :
    IsList a (x :: xs) s h ↔
      a = x ∧ x ≠ 0 ∧ ∃ nxt, (pointsTo x nxt ⋆ IsList nxt xs) s h :=
  lseg_cons_iff

/-- The entry address of a segment is forced: the first list address, or
the finish address for the empty segment. -/
theorem lseg_head_eq {a f : Nat} {xs : List Nat} {s : State} {h : Heap}
    (hl : Lseg a f xs s h) : a = xs.head?.getD f := by
  cases xs with
  | nil => exact (lseg_nil_iff.mp hl).1
  | cons x xs => exact (lseg_cons_iff.mp hl).1

/-- One-step unfolding of `IsList` in terms of the successor address
stored in the head cell: `IsList a (x :: xs)` is the cell `x ↦ next`
separated from `IsList next xs`, where `next` is the head of `xs`, or
`0` when `xs` is empty. -/
theorem isList_cons_headOr {a x : Nat} {xs : List Nat} {s : State}
    {h : Heap} :
    IsList a (x :: xs) s h ↔
      a = x ∧ x ≠ 0 ∧
        (pointsTo x (xs.head?.getD 0) ⋆
          IsList (xs.head?.getD 0) xs) s h := by
  constructor
  · intro hl
    obtain ⟨hax, hx0, nxt, hstar⟩ := isList_cons_iff.mp hl
    rw [HAssertion.star_def] at hstar
    obtain ⟨h₁, h₂, hd, heq, hp, hl2⟩ := hstar
    have hnxt : nxt = xs.head?.getD 0 := lseg_head_eq hl2
    subst hnxt
    refine ⟨hax, hx0, ?_⟩
    rw [HAssertion.star_def]
    exact ⟨h₁, h₂, hd, heq, hp, hl2⟩
  · intro hl
    obtain ⟨hax, hx0, hstar⟩ := hl
    exact isList_cons_iff.mpr ⟨hax, hx0, xs.head?.getD 0, hstar⟩

/-- Folding: a cell pointing at the head of a list extends the list. -/
theorem isList_cons_of_pointsTo {x j0 : Nat} {rev : List Nat}
    (hx0 : x ≠ 0) :
    (pointsTo x j0 ⋆ IsList j0 rev).Entails (IsList x (x :: rev)) := by
  intro s h hh
  exact isList_cons_iff.mpr ⟨rfl, hx0, j0, hh⟩

/-- List segments do not inspect the store. -/
theorem lseg_store_irrel :
    ∀ (xs : List Nat) (a f : Nat), StoreIrrel (Lseg a f xs) := by
  intro xs
  induction xs with
  | nil =>
      intro a f s s' h hl
      rwa [lseg_nil_iff] at hl ⊢
  | cons x xs ih =>
      intro a f s s' h hl
      obtain ⟨rfl, hx0, nxt, hstar⟩ := lseg_cons_iff.mp hl
      refine lseg_cons_iff.mpr ⟨rfl, hx0, nxt, ?_⟩
      rw [HAssertion.star_def] at hstar ⊢
      obtain ⟨h₁, h₂, hd, heq, hp, hl2⟩ := hstar
      exact ⟨h₁, h₂, hd, heq, hp, ih nxt f s s' h₂ hl2⟩

theorem isList_storeIrrel {a : Nat} {xs : List Nat} :
    StoreIrrel (IsList a xs) :=
  lseg_store_irrel xs a 0

/-- Adjacent segments concatenate. -/
theorem lseg_append {a b c : Nat} {xs ys : List Nat} :
    (Lseg a b xs ⋆ Lseg b c ys).Entails (Lseg a c (xs ++ ys)) := by
  induction xs generalizing a with
  | nil =>
      intro s h hh
      rw [HAssertion.star_def] at hh
      obtain ⟨h₁, h₂, _hd, heq, h1l, h2l⟩ := hh
      obtain ⟨hab, hh1⟩ := lseg_nil_iff.mp h1l
      subst hh1
      subst hab
      rwa [heq, Finmap.empty_union]
  | cons x xs ih =>
      intro s h hh
      rw [HAssertion.star_def] at hh
      obtain ⟨h₁, h₂, hd, heq, h1l, h2l⟩ := hh
      obtain ⟨rfl, hx0, nxt, hstar1⟩ := lseg_cons_iff.mp h1l
      obtain ⟨h₁₁, h₁₂, hd1, heq1, hp, hl12⟩ :=
        HAssertion.star_def.mp hstar1
      have ihapp : Lseg nxt c (xs ++ ys) s (h₁₂ ∪ h₂) := by
        apply ih
        rw [HAssertion.star_def]
        refine ⟨h₁₂, h₂, ?_, rfl, hl12, h2l⟩
        intro a' ha' ha'2
        exact hd a'
          (by rw [heq1, Finmap.mem_union]; exact Or.inr ha') ha'2
      refine lseg_cons_iff.mpr ⟨rfl, hx0, nxt, ?_⟩
      rw [HAssertion.star_def]
      refine ⟨h₁₁, h₁₂ ∪ h₂, ?_, ?_, hp, ihapp⟩
      · intro a' ha' ha'mem
        rw [Finmap.mem_union] at ha'mem
        cases ha'mem with
        | inl hm => exact hd1 a' ha' hm
        | inr hm =>
            exact hd a'
              (by rw [heq1, Finmap.mem_union]; exact Or.inl ha') hm
      · rw [heq, heq1, Finmap.union_assoc]

/-- A one-node list is a single cell storing null. -/
example (s : State) :
    IsList 5 [5] s (Finmap.singleton 5 0) := by
  rw [isList_cons_headOr]
  refine ⟨rfl, by decide, ?_⟩
  rw [HAssertion.star_def]
  exact ⟨Finmap.singleton 5 0, ∅, Heap.disjoint_empty_right _,
    Finmap.union_empty.symm, rfl, isList_nil_iff.mpr ⟨rfl, rfl⟩⟩

/-! ## In-place list reversal

Variables: `i = 0` points at the list still to process, `j = 1` at the
already-reversed prefix, `t = 2` is a temporary. The loop body is
`t := *i; *i := j; j := i; i := t`, run while `i ≠ 0`. -/

/-- One iteration of reversal: swing the head cell of the `i`-list onto
the front of the `j`-list. -/
def reverseBody : HeapCmd :=
  .seq (.read 2 (.var 0))
    (.seq (.write (.var 0) (.var 1))
      (.seq (.assign 1 (.var 0)) (.assign 0 (.var 2))))

/-- The loop guard `i ≠ 0`. -/
def reverseGuard : BExp := .not (.eq (.var 0) (.const 0))

/-- The reversal loop. -/
def reverseCmd : HeapCmd := .while reverseGuard reverseBody

theorem ne_of_guard_true {s : State}
    (h : reverseGuard.eval s = true) : s 0 ≠ 0 := by
  simp [reverseGuard, BExp.eval] at h
  exact of_decide_eq_false h

theorem eq_of_guard_false {s : State}
    (h : reverseGuard.eval s = false) : s 0 = 0 := by
  simp [reverseGuard, BExp.eval] at h
  exact of_decide_eq_true h

/-- Loop invariant: the heap splits into the unprocessed suffix `rem`
headed by `i` and the reversed processed prefix `rev` headed by `j`,
and together they account for the original list `xs0`. -/
def reverseInv (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ rem rev, rev.reverse ++ rem = xs0 ∧
    (IsList (s 0) rem ⋆ IsList (s 1) rev) s h

/-! The stages of one loop iteration, for a fixed head cell `x` storing
`nxt`, unprocessed tail `rem'`, reversed prefix `rev` headed by `j0`.
`RevS0` is the invariant with the head cell unfolded; `RevS1` has
`t = nxt`; `RevS2` has the head cell rewritten to point at `j0`;
`RevS3` folds it into a list headed by `x`; `RevS4` has `j = x`;
`RevS5` has `i = nxt`, ready to refold into the invariant. -/

def RevS0 (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ x nxt j0 rem' rev,
    (rev.reverse ++ (x :: rem') = xs0 ∧ x ≠ 0 ∧ s 0 = x ∧ s 1 = j0) ∧
    (pointsTo x nxt ⋆ (IsList nxt rem' ⋆ IsList j0 rev)) s h

def RevS1 (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ x nxt j0 rem' rev,
    (rev.reverse ++ (x :: rem') = xs0 ∧ x ≠ 0 ∧ s 0 = x ∧ s 1 = j0 ∧
      s 2 = nxt) ∧
    (pointsTo x nxt ⋆ (IsList nxt rem' ⋆ IsList j0 rev)) s h

def RevS2 (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ x nxt j0 rem' rev,
    (rev.reverse ++ (x :: rem') = xs0 ∧ x ≠ 0 ∧ s 0 = x ∧ s 1 = j0 ∧
      s 2 = nxt) ∧
    (pointsTo x j0 ⋆ (IsList nxt rem' ⋆ IsList j0 rev)) s h

def RevS3 (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ x nxt j0 rem' rev,
    (rev.reverse ++ (x :: rem') = xs0 ∧ x ≠ 0 ∧ s 0 = x ∧ s 1 = j0 ∧
      s 2 = nxt) ∧
    (IsList x (x :: rev) ⋆ IsList nxt rem') s h

def RevS4 (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ (x nxt _j0 : Nat) (rem' rev : List Nat),
    (rev.reverse ++ (x :: rem') = xs0 ∧ x ≠ 0 ∧ s 0 = x ∧ s 1 = x ∧
      s 2 = nxt) ∧
    (IsList x (x :: rev) ⋆ IsList nxt rem') s h

def RevS5 (xs0 : List Nat) : HAssertion :=
  fun s h => ∃ (x nxt _j0 : Nat) (rem' rev : List Nat),
    (rev.reverse ++ (x :: rem') = xs0 ∧ x ≠ 0 ∧ s 0 = nxt ∧ s 1 = x ∧
      s 2 = nxt) ∧
    (IsList x (x :: rev) ⋆ IsList nxt rem') s h

/-- Entering an iteration: a true guard means the `i`-list is nonempty,
so its head cell can be unfolded and split off. -/
theorem rev_pre_entails {xs0 : List Nat} :
    HAssertion.Entails
      (fun s h => reverseInv xs0 s h ∧ reverseGuard.eval s = true)
      (RevS0 xs0) := by
  intro s h hh
  obtain ⟨hI, hg⟩ := hh
  have hs0ne : s 0 ≠ 0 := ne_of_guard_true hg
  obtain ⟨(_ | ⟨x, rem'⟩), rev, hrel, hstar⟩ := hI
  · obtain ⟨h₁, _h₂, _hd, _heq, hrem, _hrev⟩ :=
      HAssertion.star_def.mp hstar
    exact absurd (isList_nil_iff.mp hrem).1 hs0ne
  · obtain ⟨h₁, h₂, hd, heq, hrem, hrev⟩ := HAssertion.star_def.mp hstar
    obtain ⟨hax, hx0, nxt, hsplit⟩ := isList_cons_iff.mp hrem
    refine ⟨x, nxt, s 1, rem', rev, ⟨hrel, hx0, hax, rfl⟩, ?_⟩
    have hcomb : ((pointsTo x nxt ⋆ IsList nxt rem') ⋆
        IsList (s 1) rev) s h :=
      HAssertion.star_def.mpr ⟨h₁, h₂, hd, heq, hsplit, hrev⟩
    exact (entails_of_eq HAssertion.star_assoc) hcomb

/-- `t := *i`: read the successor out of the head cell. -/
theorem rev_step1 {xs0 : List Nat} :
    SepValid (RevS0 xs0) (.read 2 (.var 0)) (RevS1 xs0) := by
  apply SepValid.exists5
  intro x nxt j0 rem' rev
  exact read_framed (star_storeIrrel isList_storeIrrel isList_storeIrrel)
    (by
      intro s hp
      obtain ⟨hrel, hx0, hs0, hs1⟩ := hp
      refine ⟨hs0, hrel, hx0, ?_, ?_, ?_⟩
      · simp [hs0]
      · simp [hs1]
      · simp)

/-- `*i := j`: point the head cell back at the reversed prefix. -/
theorem rev_step2 {xs0 : List Nat} :
    SepValid (RevS1 xs0) (.write (.var 0) (.var 1)) (RevS2 xs0) := by
  apply SepValid.exists5
  intro x nxt j0 rem' rev
  exact write_framed (star_storeIrrel isList_storeIrrel isList_storeIrrel)
    (by
      intro s hp
      exact ⟨hp, hp.2.2.1, hp.2.2.2.1⟩)

/-- Fold the rewritten head cell together with the old `j`-list into one
list headed by `x`, leaving the unprocessed tail separate. -/
theorem rev_fold_entails {xs0 : List Nat} :
    HAssertion.Entails (RevS2 xs0) (RevS3 xs0) := by
  intro s h hh
  obtain ⟨x, nxt, j0, rem', rev, hp, hheap⟩ := hh
  refine ⟨x, nxt, j0, rem', rev, hp, ?_⟩
  exact HAssertion.star_mono (isList_cons_of_pointsTo hp.2.1)
    (HAssertion.entails_refl _) (star_swap_right hheap)

/-- `j := i`: the folded list becomes the reversed prefix. -/
theorem rev_step3 {xs0 : List Nat} :
    SepValid (RevS3 xs0) (.assign 1 (.var 0)) (RevS4 xs0) := by
  apply SepValid.exists5
  intro x nxt j0 rem' rev
  exact assign_step (star_storeIrrel isList_storeIrrel isList_storeIrrel)
    (by
      intro s hp
      obtain ⟨hrel, hx0, hs0, _hs1, hs2⟩ := hp
      refine ⟨hrel, hx0, ?_, ?_, ?_⟩
      · simp [hs0]
      · simp [hs0]
      · simp [hs2])

/-- `i := t`: advance to the unprocessed tail. -/
theorem rev_step4 {xs0 : List Nat} :
    SepValid (RevS4 xs0) (.assign 0 (.var 2)) (RevS5 xs0) := by
  apply SepValid.exists5
  intro x nxt j0 rem' rev
  exact assign_step (star_storeIrrel isList_storeIrrel isList_storeIrrel)
    (by
      intro s hp
      obtain ⟨hrel, hx0, _hs0, hs1, hs2⟩ := hp
      refine ⟨hrel, hx0, ?_, ?_, ?_⟩
      · simp [hs2]
      · simp [hs1]
      · simp [hs2])

/-- Refold the final stage into the loop invariant, with `x` moved from
the unprocessed suffix to the front of the reversed prefix. -/
theorem rev_post_entails {xs0 : List Nat} :
    HAssertion.Entails (RevS5 xs0) (reverseInv xs0) := by
  intro s h hh
  obtain ⟨x, nxt, _j0, rem', rev, ⟨hrel, _hx0, hs0, hs1, _hs2⟩,
    hheap⟩ := hh
  refine ⟨rem', x :: rev, ?_, ?_⟩
  · simp only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    exact hrel
  · rw [hs0, hs1]
    exact HAssertion.star_comm hheap

/-- One loop iteration preserves the invariant. -/
theorem reverse_body {xs0 : List Nat} :
    SepValid (fun s h => reverseInv xs0 s h ∧
        reverseGuard.eval s = true)
      reverseBody (reverseInv xs0) := by
  refine SepValid.consequence rev_pre_entails ?_ rev_post_entails
  unfold reverseBody
  exact SepValid.seq rev_step1
    (SepValid.seq
      (SepValid.consequence (HAssertion.entails_refl _) rev_step2
        rev_fold_entails)
      (SepValid.seq rev_step3 rev_step4))

/-- **In-place list reversal is correct.** Starting with `i` at the head
of the list `xs0` and `j` null, the loop terminates (whenever it does;
validity here is fault-avoidance plus this postcondition on terminating
runs) with `i` null and `j` at the head of the reversed list, on exactly
the same heap cells with their links swung around. -/
theorem reverse_spec {head : Nat} {xs0 : List Nat} :
    SepValid (fun s h => (s 0 = head ∧ s 1 = 0) ∧ IsList head xs0 s h)
      reverseCmd
      (fun s h => s 0 = 0 ∧ IsList (s 1) xs0.reverse s h) := by
  refine SepValid.consequence ?_
    (SepValid.whileLoop (I := reverseInv xs0) (reverse_body (xs0 := xs0)))
    ?_
  · intro s h hh
    obtain ⟨⟨hs0, hs1⟩, hlist⟩ := hh
    refine ⟨xs0, [], by simp, ?_⟩
    rw [HAssertion.star_def]
    refine ⟨h, ∅, Heap.disjoint_empty_right h, Finmap.union_empty.symm,
      ?_, ?_⟩
    · rw [hs0]
      exact hlist
    · exact isList_nil_iff.mpr ⟨hs1, rfl⟩
  · intro s h hh
    obtain ⟨hI, hg⟩ := hh
    have hs0 : s 0 = 0 := eq_of_guard_false hg
    obtain ⟨(_ | ⟨x, rem'⟩), rev, hrel, hstar⟩ := hI
    · obtain ⟨h₁, h₂, _hd, heq, hrem, hrev⟩ := HAssertion.star_def.mp hstar
      obtain ⟨_h10, hh1⟩ := isList_nil_iff.mp hrem
      subst hh1
      have hr : rev.reverse = xs0 := by simpa using hrel
      have hrevEq : rev = xs0.reverse := by
        calc rev = rev.reverse.reverse :=
              (List.reverse_reverse rev).symm
          _ = xs0.reverse := by rw [hr]
      refine ⟨hs0, ?_⟩
      rw [← hrevEq]
      rwa [heq, Finmap.empty_union]
    · obtain ⟨h₁, _h₂, _hd, _heq, hrem, _hrev⟩ :=
        HAssertion.star_def.mp hstar
      obtain ⟨hax, hx0, _⟩ := isList_cons_iff.mp hrem
      have hx00 : x = 0 := by rw [← hax]; exact hs0
      exact absurd hx00 hx0

/-- Reversal under an arbitrary frame: the reversed list is computed in
its own footprint while any disjoint heap `R` (not depending on
variables `0`, `1`, `2`) rides along untouched. -/
theorem reverse_spec_frame {head : Nat} {xs0 : List Nat}
    {R : HAssertion}
    (hR : ∀ ⦃s : State⦄ ⦃h : Heap⦄ ⦃s' : State⦄, R s h →
      (∀ v, v ∉ reverseCmd.modVars → s' v = s v) → R s' h) :
    SepValid
      ((fun s h => (s 0 = head ∧ s 1 = 0) ∧ IsList head xs0 s h) ⋆ R)
      reverseCmd
      ((fun s h => s 0 = 0 ∧ IsList (s 1) xs0.reverse s h) ⋆ R) :=
  SepValid.frame reverse_spec hR

/-- Concrete end-to-end instance: reversing the two-node list `5 ↦ 7 ↦ 0`
yields `j = 7` and the heap `7 ↦ 5 ↦ 0`. -/
theorem reverse_two_nodes :
    SepValid (fun s h => s 0 = 5 ∧ s 1 = 0 ∧
        h = Finmap.singleton 5 7 ∪ Finmap.singleton 7 0)
      reverseCmd
      (fun s h => s 0 = 0 ∧ s 1 = 7 ∧
        h = Finmap.singleton 7 5 ∪ Finmap.singleton 5 0) := by
  refine SepValid.consequence ?_
    (reverse_spec (head := 5) (xs0 := [5, 7])) ?_
  · intro s h hh
    obtain ⟨hs0, hs1, rfl⟩ := hh
    refine ⟨⟨hs0, hs1⟩, ?_⟩
    rw [isList_cons_headOr]
    refine ⟨rfl, by decide, ?_⟩
    rw [HAssertion.star_def]
    refine ⟨Finmap.singleton 5 7, Finmap.singleton 7 0, ?_, rfl, rfl, ?_⟩
    · exact Heap.disjoint_singleton_left.mpr (by simp)
    · rw [isList_cons_headOr]
      refine ⟨rfl, by decide, ?_⟩
      rw [HAssertion.star_def]
      exact ⟨Finmap.singleton 7 0, ∅, Heap.disjoint_empty_right _,
        Finmap.union_empty.symm, rfl, isList_nil_iff.mpr ⟨rfl, rfl⟩⟩
  · intro s h hh
    obtain ⟨hs0, hlist⟩ := hh
    have hrev57 : ([5, 7] : List Nat).reverse = [7, 5] := rfl
    rw [hrev57] at hlist
    obtain ⟨hs1, _hne, nxt, hstar⟩ := isList_cons_iff.mp hlist
    obtain ⟨h₁, h₂, _hd, rfl, hp1, hl2⟩ := HAssertion.star_def.mp hstar
    obtain ⟨hnxt, _hne2, nxt2, hstar2⟩ := isList_cons_iff.mp hl2
    obtain ⟨h₂₁, h₂₂, _hd2, rfl, hp2, hl3⟩ := HAssertion.star_def.mp hstar2
    obtain ⟨hnxt2, rfl⟩ := isList_nil_iff.mp hl3
    have hp1' : h₁ = Finmap.singleton 7 nxt := hp1
    have hp2' : h₂₁ = Finmap.singleton 5 nxt2 := hp2
    subst hnxt
    subst hnxt2
    refine ⟨hs0, hs1, ?_⟩
    rw [hp1', hp2', Finmap.union_empty]

#print axioms reverse_spec
#print axioms swap_two_cells_frame

end Cslib.IMP.Tests.SepExamples
