/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.PriorityQueue
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic

/-!
# Pairing heaps: the book version (`Pairing_Heap_List2`)

The pairing-heap implementation of FDSA Chapter 23 §23.1 (the "modified
Okasaki" version: heaps are `Option` of `Hp`, so `Empty` only occurs at
the root), with the functional-correctness proof of §23.1.1, Exercise
23.1 (`mergePairs`), and the running-time functions of Appendix B §B.11.
The amortized analysis (size `sz`, potential `Φ`, the `ΔΦ` lemmas, the
`A_*` bounds, and the `Amortized` instantiation) lives in
`PairingHeap.Amortized`.

`getMin` is `Option`-valued: the book's `get_min` is partial on the empty
heap. The `Priority_Queue_Merge` specification is proved in three forms:
the strengthened single conjunction `priority_queue_merge`, the Isabelle
locale's form `priority_queue_merge_locale`, and the book's form
`priority_queue_merge_book` (Chapter 14, Figures 14.1–14.2).

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_List2.thy`) and `Amortized_Complexity`
(`Pairing_Heap_List2_Analysis.thy`), and Tobias Nipkow (ed.),
*Functional Data Structures and Algorithms: A Proof Assistant Approach*,
Chapter 23 (Pairing Heaps, pp. 257–264). Isabelle-derived names are kept
for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace PairingHeap
namespace List2

variable {α : Type u}

/-- Pairing heap node: a root value and a list of child heaps (book §23.1).
In Isabelle this is `datatype 'a hp = Hp 'a ('a hp list)`; in Lean the
constructor is `Hp.mk` (so `Hp.mk x hs` is the book's `Hp x hs`). -/
inductive Hp (α : Type u) where
  | mk : α → List (Hp α) → Hp α

/-- A (possibly empty) pairing heap: the book's `'a heap = 'a hp option`. -/
abbrev Heap (α : Type u) := Option (Hp α)

/-- The empty heap: the book's `empty = None`. -/
def empty : Heap α := none

/-- The children of a heap node: `hps (Hp.mk x hs) = hs`. -/
def hps : Hp α → List (Hp α)
  | .mk _ hs => hs

@[simp] theorem hps_mk (x : α) (hs : List (Hp α)) :
    hps (.mk x hs) = hs := rfl

/-- The root value of a heap node. -/
def root : Hp α → α
  | .mk x _ => x

@[simp] theorem root_mk (x : α) (hs : List (Hp α)) :
    root (.mk x hs) = x := rfl

/-! ### Size and the custom induction principle -/

/- Number of constructors in a heap / list of heaps (used for induction). -/
mutual
def sizeHp : Hp α → ℕ
  | .mk _ hs => 1 + sizeHpList hs
def sizeHpList : List (Hp α) → ℕ
  | [] => 0
  | h :: hs => sizeHp h + sizeHpList hs
end

theorem sizeHp_eq (x : α) (hs : List (Hp α)) :
    sizeHp (.mk x hs) = 1 + sizeHpList hs := rfl

theorem sizeHpList_nil : sizeHpList ([] : List (Hp α)) = 0 := rfl

theorem sizeHpList_cons (h : Hp α) (hs : List (Hp α)) :
    sizeHpList (h :: hs) = sizeHp h + sizeHpList hs := rfl

theorem sizeHp_pos (h : Hp α) : 0 < sizeHp h := by
  obtain ⟨x, hs⟩ := h
  rw [sizeHp_eq]; omega

theorem sizeHpList_le_of_mem {hs : List (Hp α)} {h : Hp α}
    (hmem : h ∈ hs) : sizeHp h ≤ sizeHpList hs := by
  induction hs with
  | nil => simp at hmem
  | cons h' hs ih =>
    simp only [List.mem_cons] at hmem
    rw [sizeHpList_cons]
    rcases hmem with rfl | hmem
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

theorem sizeHp_lt_of_mem (x : α) {hs : List (Hp α)} {h : Hp α}
    (hmem : h ∈ hs) : sizeHp h < sizeHp (.mk x hs) := by
  rw [sizeHp_eq]
  have := sizeHpList_le_of_mem hmem
  omega

/-- Induction principle for `Hp`: to prove `P h` for every heap, prove it
for `Hp.mk x hs` assuming `P` holds for every child in `hs`. Proved by
strong induction on `sizeHp` (Lean's `induction` tactic does not support
nested inductives). -/
theorem Hp_ind {P : Hp α → Prop}
    (step : ∀ (x : α) (hs : List (Hp α)), (∀ h ∈ hs, P h) → P (.mk x hs))
    (h : Hp α) : P h := by
  have key : ∀ n : ℕ, ∀ h : Hp α, sizeHp h ≤ n → P h := by
    intro n
    induction n with
    | zero =>
      intro h hh
      obtain ⟨x, hs⟩ := h
      rw [sizeHp_eq] at hh
      omega
    | succ n ih =>
      intro h hh
      obtain ⟨x, hs⟩ := h
      apply step
      intro h' hh'
      apply ih
      have hlt := sizeHp_lt_of_mem x hh'
      omega
  exact key (sizeHp h) h le_rfl

/-- Well-founded induction on lists of heaps, by total size
(`sizeHpList`): to prove `P hs`, prove it assuming `P` holds for all
lists of strictly smaller total size. Used for `szList` / `phiList`
lemmas whose recursion goes into children. -/
theorem List_size_ind {P : List (Hp α) → Prop}
    (step : ∀ hs : List (Hp α),
      (∀ hs' : List (Hp α), sizeHpList hs' < sizeHpList hs → P hs') → P hs)
    (hs : List (Hp α)) : P hs := by
  have key : ∀ n : ℕ, ∀ hs : List (Hp α), sizeHpList hs ≤ n → P hs := by
    intro n
    induction n with
    | zero =>
      intro hs hh
      apply step
      intro hs' hlt
      have : sizeHpList hs = 0 := by omega
      rw [this] at hlt; omega
    | succ n ih =>
      intro hs hh
      apply step
      intro hs' hlt
      apply ih
      omega
  exact key (sizeHpList hs) hs le_rfl

/-! ### Multiset abstraction -/

/- The multiset of elements of a heap / list of heaps (book `mset_hp`,
with `mset_hp (Hp x hs) = {#x#} + sum_list (map mset_hp hs)`). -/
mutual
def msetHp : Hp α → Multiset α
  | .mk x hs => x ::ₘ msetHpList hs
def msetHpList : List (Hp α) → Multiset α
  | [] => 0
  | h :: hs => msetHp h + msetHpList hs
end

theorem msetHp_eq (x : α) (hs : List (Hp α)) :
    msetHp (.mk x hs) = x ::ₘ msetHpList hs := rfl

theorem msetHpList_nil : msetHpList ([] : List (Hp α)) = 0 := rfl

theorem msetHpList_cons (h : Hp α) (hs : List (Hp α)) :
    msetHpList (h :: hs) = msetHp h + msetHpList hs := rfl

/-- The multiset of elements of a possibly-empty heap (book `mset_heap`). -/
def msetHeap : Heap α → Multiset α
  | none => 0
  | some h => msetHp h

@[simp] theorem msetHeap_none : msetHeap (none : Heap α) = 0 := rfl

@[simp] theorem msetHeap_some (h : Hp α) :
    msetHeap (some h) = msetHp h := rfl

theorem msetHp_ne_zero (h : Hp α) : msetHp h ≠ 0 := by
  induction h using Hp_ind with
  | step x hs _ =>
    rw [msetHp_eq]
    exact Multiset.cons_ne_zero

theorem msetHpList_mem {hs : List (Hp α)} {y : α} :
    y ∈ msetHpList hs ↔ ∃ h ∈ hs, y ∈ msetHp h := by
  induction hs with
  | nil => simp [msetHpList_nil]
  | cons h hs ih =>
    rw [msetHpList_cons, Multiset.mem_add, ih]
    constructor
    · rintro (hy | ⟨h', hh', hy⟩)
      · exact ⟨h, List.mem_cons_self, hy⟩
      · exact ⟨h', List.mem_cons_of_mem _ hh', hy⟩
    · rintro ⟨h', hh', hy⟩
      simp only [List.mem_cons] at hh'
      rcases hh' with rfl | hh'
      · exact Or.inl hy
      · exact Or.inr ⟨h', hh', hy⟩

theorem msetHp_mem {x y : α} {hs : List (Hp α)} :
    y ∈ msetHp (.mk x hs) ↔ y = x ∨ ∃ h ∈ hs, y ∈ msetHp h := by
  rw [msetHp_eq, Multiset.mem_cons, msetHpList_mem]

/-! ### Heap invariant -/

/- The heap property for one node and all its descendants (book `php`):
every child heap's elements are `≥` the root, recursively. Defined
mutually with `phpList`, which says `php` holds for every heap in a list.
This is exactly Isabelle's single definition
`php (Hp x hs) = (∀ h ∈ set hs, (∀ y ∈# mset_hp h, x ≤ y) ∧ php h)`,
with the two conjuncts separated into `php`/`phpList`: `∀` distributes
over `∧`, so the forms are equivalent (see `php_eq`). -/
mutual
def php [LinearOrder α] : Hp α → Prop
  | .mk x hs => (∀ h ∈ hs, ∀ y ∈ msetHp h, x ≤ y) ∧ phpList hs
def phpList [LinearOrder α] : List (Hp α) → Prop
  | [] => True
  | h :: hs => php h ∧ phpList hs
end

theorem php_eq [LinearOrder α] (x : α) (hs : List (Hp α)) :
    php (.mk x hs) ↔
      (∀ h ∈ hs, ∀ y ∈ msetHp h, x ≤ y) ∧ phpList hs := Iff.rfl

theorem phpList_nil [LinearOrder α] :
    phpList ([] : List (Hp α)) ↔ True := Iff.rfl

theorem phpList_cons [LinearOrder α] (h : Hp α) (hs : List (Hp α)) :
    phpList (h :: hs) ↔ php h ∧ phpList hs := Iff.rfl

theorem phpList_of_mem [LinearOrder α] {hs : List (Hp α)} {h : Hp α}
    (hmem : h ∈ hs) (hphp : phpList hs) : php h := by
  induction hs with
  | nil => simp at hmem
  | cons h' hs ih =>
    simp only [List.mem_cons] at hmem
    rw [phpList_cons] at hphp
    rcases hmem with rfl | hmem
    · exact hphp.1
    · exact ih hmem hphp.2

theorem phpList_cons_of [LinearOrder α] {h : Hp α} {hs : List (Hp α)}
    (hh : php h) (hhs : phpList hs) : phpList (h :: hs) := ⟨hh, hhs⟩

/-- The heap invariant for a possibly-empty heap (book `invar`). -/
def invar [LinearOrder α] : Heap α → Prop
  | none => True
  | some h => php h

@[simp] theorem invar_none [LinearOrder α] :
    invar (none : Heap α) ↔ True := Iff.rfl

@[simp] theorem invar_some [LinearOrder α] (h : Hp α) :
    invar (some h) ↔ php h := Iff.rfl

/-- `is_empty` of the `Priority_Queue` locale: `λq. q = empty`. -/
def isEmpty : Heap α → Prop := fun ho => ho = none

/-! ### Operations (book §23.1) -/

/-- `get_min`: the root of a non-empty heap, as an `Option` (the book's
`get_min` is partial on `None`; here it returns `none`). -/
def getMin : Heap α → Option α
  | none => none
  | some (.mk x _) => some x

@[simp] theorem getMin_none : getMin (none : Heap α) = none := rfl

@[simp] theorem getMin_some (x : α) (hs : List (Hp α)) :
    getMin (some (.mk x hs)) = some x := rfl

/-- `link`: attach the heap with the larger root under the heap with the
smaller root (book §23.1). -/
def link [LinearOrder α] : Hp α → Hp α → Hp α
  | .mk x1 hs1, .mk x2 hs2 =>
    if x1 < x2 then .mk x1 (.mk x2 hs2 :: hs1) else .mk x2 (.mk x1 hs1 :: hs2)

theorem link_eq_pos [LinearOrder α] {x1 x2 : α} {hs1 hs2 : List (Hp α)}
    (h : x1 < x2) :
    link (.mk x1 hs1) (.mk x2 hs2) = .mk x1 (.mk x2 hs2 :: hs1) := by
  simp [link, h]

theorem link_eq_neg [LinearOrder α] {x1 x2 : α} {hs1 hs2 : List (Hp α)}
    (h : ¬ x1 < x2) :
    link (.mk x1 hs1) (.mk x2 hs2) = .mk x2 (.mk x1 hs1 :: hs2) := by
  simp [link, h]

/-- `merge`: merge two heaps by linking their roots (book §23.1). -/
def merge [LinearOrder α] : Heap α → Heap α → Heap α
  | none, ho => ho
  | some h, none => some h
  | some h1, some h2 => some (link h1 h2)

@[simp] theorem merge_none_left [LinearOrder α] (ho : Heap α) :
    merge (none : Heap α) ho = ho := by
  cases ho <;> rfl

@[simp] theorem merge_none_right [LinearOrder α] (ho : Heap α) :
    merge ho (none : Heap α) = ho := by
  cases ho <;> rfl

theorem merge_some_some [LinearOrder α] (h1 h2 : Hp α) :
    merge (some h1) (some h2) = some (link h1 h2) := rfl

/-- `insert`: insert by linking a singleton heap (book §23.1). -/
def insert [LinearOrder α] (x : α) : Heap α → Heap α
  | none => some (.mk x [])
  | some h => some (link (.mk x []) h)

/-- `pass1`: link adjacent pairs of heaps (book §23.1, first pass of
`delMin`). -/
def pass1 [LinearOrder α] : List (Hp α) → List (Hp α)
  | h1 :: h2 :: hs => link h1 h2 :: pass1 hs
  | hs => hs

theorem pass1_nil [LinearOrder α] : pass1 ([] : List (Hp α)) = [] := rfl

theorem pass1_single [LinearOrder α] (h : Hp α) : pass1 [h] = [h] := rfl

theorem pass1_cons2 [LinearOrder α] (h1 h2 : Hp α) (hs : List (Hp α)) :
    pass1 (h1 :: h2 :: hs) = link h1 h2 :: pass1 hs := rfl

/-- `pass2`: link a list of heaps in a cascade, right to left (book §23.1,
second pass of `delMin`). -/
def pass2 [LinearOrder α] : List (Hp α) → Heap α
  | [] => none
  | h :: hs =>
    some (match pass2 hs with | none => h | some h' => link h h')

theorem pass2_nil [LinearOrder α] : pass2 ([] : List (Hp α)) = none := rfl

theorem pass2_cons [LinearOrder α] (h : Hp α) (hs : List (Hp α)) :
    pass2 (h :: hs) =
      some (match pass2 hs with | none => h | some h' => link h h') := rfl

theorem pass2_eq_none_iff [LinearOrder α] {hs : List (Hp α)} :
    pass2 hs = none ↔ hs = [] := by
  cases hs with
  | nil => simp [pass2_nil]
  | cons h hs => simp [pass2_cons]

theorem pass2_ne_none_of_ne_nil [LinearOrder α] {hs : List (Hp α)}
    (hne : hs ≠ []) : pass2 hs ≠ none := by
  intro hcontra
  rw [pass2_eq_none_iff] at hcontra
  exact hne hcontra

/-- If `pass2 hs = some h`, then `h` is the heap obtained by linking `hs`. -/
theorem pass2_some_exists [LinearOrder α] {hs : List (Hp α)} (hne : hs ≠ []) :
    ∃ h : Hp α, pass2 hs = some h := by
  cases hpass : pass2 hs with
  | none => exact absurd hpass (pass2_ne_none_of_ne_nil hne)
  | some h => exact ⟨h, rfl⟩

/-- `delMin`: delete the minimum (the root) by two-pass linking of its
children (book §23.1). -/
def delMin [LinearOrder α] : Heap α → Heap α
  | none => none
  | some (.mk _ hs) => pass2 (pass1 hs)

@[simp] theorem delMin_none [LinearOrder α] :
    delMin (none : Heap α) = none := rfl

theorem delMin_some [LinearOrder α] (x : α) (hs : List (Hp α)) :
    delMin (some (.mk x hs)) = pass2 (pass1 hs) := rfl

/-- `mergePairs` (Exercise 23.1): a single-pass version of
`pass2 ∘ pass1`, with no intermediate list. -/
def mergePairs [LinearOrder α] : List (Hp α) → Heap α
  | [] => none
  | [h] => some h
  | h1 :: h2 :: hs =>
    some (let h12 := link h1 h2
      match mergePairs hs with | none => h12 | some h => link h12 h)

theorem mergePairs_nil [LinearOrder α] :
    mergePairs ([] : List (Hp α)) = none := rfl

theorem mergePairs_single [LinearOrder α] (h : Hp α) :
    mergePairs [h] = some h := rfl

theorem mergePairs_cons2 [LinearOrder α] (h1 h2 : Hp α) (hs : List (Hp α)) :
    mergePairs (h1 :: h2 :: hs) =
      some (let h12 := link h1 h2
        match mergePairs hs with | none => h12 | some h => link h12 h) := rfl

/-! ### Running-time functions (book §23.2) -/

/-- Running-time functions, defined explicitly (Lean has no Isabelle
`time_fun` command), following the book's Appendix B §B.11 (Pairing
Heaps), which lists these equations verbatim. `link`, `insert`, and
`merge` are `0`, as in the AFP (`T_link_0`, `T_insert_0`, `T_merge_0`)
and in Appendix B ("`Tlink` and `Tmerge` are 0 everywhere").
`pass1`'s compiled cases are `[]`, `[h]`, `h1 :: h2 :: hs` (the
catch-all `pass1 hs = hs` splits into the first two), so all three cost
1 per unfolding, matching Appendix B's `Tpass1 (_ # _ # hs) =
Tpass1 hs + 1`, `Tpass1 _ = 1`; likewise `pass2` (`[]`, `h :: hs`)
matches `Tpass2 [] = 1`, `Tpass2 (_ # hs) = Tpass2 hs + 1`, and
`del_min` (non-recursive) charges only its callees, matching
`Tdel_min (Some (Hp _ hs)) = Tpass1 hs + Tpass2 (pass1 hs)`.
There is no AFP/book equation for `merge_pairs` — `TmergePairs`
follows the same convention as `Tpass1` for Exercise 23.1 part 2. -/
def Tlink : Hp α → Hp α → ℕ
  | _, _ => 0

def Tinsert : α → Heap α → ℕ
  | _, _ => 0

def Tmerge : Heap α → Heap α → ℕ
  | _, _ => 0

def Tpass1 : List (Hp α) → ℕ
  | [] => 1
  | _ :: [] => 1
  | _ :: _ :: hs => 1 + Tpass1 hs

def Tpass2 : List (Hp α) → ℕ
  | [] => 1
  | _ :: hs => 1 + Tpass2 hs

def TdelMin [LinearOrder α] : Heap α → ℕ
  | none => 0
  | some (.mk _ hs) => Tpass1 hs + Tpass2 (pass1 hs)

def TmergePairs : List (Hp α) → ℕ
  | [] => 1
  | _ :: [] => 1
  | _ :: _ :: hs => 1 + TmergePairs hs

theorem Tpass2_eq_length (hs : List (Hp α)) : Tpass2 hs = hs.length + 1 := by
  induction hs with
  | nil => rfl
  | cons _ hs ih =>
    change 1 + Tpass2 hs = hs.length + 1 + 1
    rw [ih]
    omega

theorem Tpass1_cons2 (h1 h2 : Hp α) (hs : List (Hp α)) :
    Tpass1 (h1 :: h2 :: hs) = 1 + Tpass1 hs := rfl

theorem TmergePairs_cons2 (h1 h2 : Hp α) (hs : List (Hp α)) :
    TmergePairs (h1 :: h2 :: hs) = 1 + TmergePairs hs := rfl

/-- The book's/AFP's bound `T_pass2 (pass1 hs) + T_pass1 hs ≤ 2 + |hs|`,
as an exact identity under the `time_fun` convention. -/
theorem Tpass2_pass1_add_Tpass1 [LinearOrder α] (hs : List (Hp α)) :
    Tpass2 (pass1 hs) + Tpass1 hs = hs.length + 2 := by
  induction hs using List_pair_ind with
  | nil => rfl
  | single h =>
    change Tpass2 (pass1 [h]) + Tpass1 [h] = 1 + 2
    rw [pass1_single]
    rw [Tpass2_eq_length]
    rfl
  | cons2 h1 h2 hs ih =>
    rw [pass1_cons2, show Tpass2 (link h1 h2 :: pass1 hs) = 1 + Tpass2 (pass1 hs) from rfl,
      Tpass1_cons2]
    have hlen : (h1 :: h2 :: hs).length = hs.length + 2 := rfl
    omega

theorem Tpass1_eq_length_div_two (hs : List (Hp α)) :
    Tpass1 hs = hs.length / 2 + 1 := by
  induction hs using List_pair_ind with
  | nil => simp [Tpass1]
  | single h => simp [Tpass1]
  | cons2 h1 h2 hs ih =>
    rw [Tpass1_cons2, ih]
    show 1 + (hs.length / 2 + 1) = (h1 :: h2 :: hs).length / 2 + 1
    have hlen : (h1 :: h2 :: hs).length = hs.length + 2 := rfl
    omega

theorem TmergePairs_eq_length_div_two (hs : List (Hp α)) :
    TmergePairs hs = hs.length / 2 + 1 := by
  induction hs using List_pair_ind with
  | nil => simp [TmergePairs]
  | single h => simp [TmergePairs]
  | cons2 h1 h2 hs ih =>
    rw [TmergePairs_cons2, ih]
    show 1 + (hs.length / 2 + 1) = (h1 :: h2 :: hs).length / 2 + 1
    have hlen : (h1 :: h2 :: hs).length = hs.length + 2 := rfl
    omega

/-! ### Correctness: multiset lemmas -/

theorem msetHp_link [LinearOrder α] (h1 h2 : Hp α) :
    msetHp (link h1 h2) = msetHp h1 + msetHp h2 := by
  obtain ⟨x1, hs1⟩ := h1
  obtain ⟨x2, hs2⟩ := h2
  by_cases hc : x1 < x2
  · rw [link_eq_pos hc, msetHp_eq, msetHpList_cons, msetHp_eq, msetHp_eq]
    simp only [← Multiset.singleton_add]
    ac_rfl
  · rw [link_eq_neg hc, msetHp_eq, msetHpList_cons, msetHp_eq, msetHp_eq]
    simp only [← Multiset.singleton_add]
    ac_rfl

theorem msetHpList_singleton (h : Hp α) : msetHpList [h] = msetHp h := by
  rw [msetHpList_cons, msetHpList_nil, add_zero]

theorem mset_merge [LinearOrder α] (ho1 ho2 : Heap α) :
    msetHeap (merge ho1 ho2) = msetHeap ho1 + msetHeap ho2 := by
  cases ho1 with
  | none => simp [merge_none_left]
  | some h1 =>
    cases ho2 with
    | none => rw [merge_none_right]; simp
    | some h2 => simp [merge_some_some, msetHp_link]

theorem mset_insert [LinearOrder α] (x : α) (ho : Heap α) :
    msetHeap (insert x ho) = {x} + msetHeap ho := by
  cases ho with
  | none =>
    change msetHeap (some (.mk x [])) = {x} + msetHeap none
    rw [msetHeap_some, msetHeap_none, msetHp_eq, msetHpList_nil, ← Multiset.singleton_add, add_zero]
  | some h =>
    change msetHeap (some (link (.mk x []) h)) = {x} + msetHeap h
    rw [msetHeap_some, msetHp_link, msetHp_eq, msetHpList_nil, ← Multiset.singleton_add, add_zero]
    rw [msetHeap_some]

theorem msetHpList_pass1 [LinearOrder α] (hs : List (Hp α)) :
    msetHpList (pass1 hs) = msetHpList hs := by
  induction hs using List_pair_ind with
  | nil => rfl
  | single h => rfl
  | cons2 h1 h2 hs ih =>
    rw [pass1_cons2, msetHpList_cons, msetHp_link, ih]
    rw [msetHpList_cons, msetHpList_cons]
    ac_rfl

theorem mset_pass2 [LinearOrder α] (hs : List (Hp α)) :
    msetHeap (pass2 hs) = msetHpList hs := by
  induction hs with
  | nil => simp [pass2_nil, msetHpList_nil, msetHeap_none]
  | cons h hs ih =>
    rw [pass2_cons]
    cases hpass : pass2 hs with
    | none =>
      have hhs : hs = [] := by
        rw [← pass2_eq_none_iff]; exact hpass
      subst hhs
      simp [msetHpList_singleton]
    | some h' =>
      have hih : msetHp h' = msetHpList hs := by
        have := ih
        rw [hpass] at this
        simpa using this
      simp only [msetHeap_some, msetHp_link, hih, msetHpList_cons]

theorem mset_delMin [LinearOrder α] (ho : Heap α) (x : α)
    (hx : getMin ho = some x) :
    msetHeap (delMin ho) = msetHeap ho - {x} := by
  cases ho with
  | none => simp [getMin_none] at hx
  | some h =>
    obtain ⟨r, hs⟩ := h
    simp only [getMin_some, Option.some.injEq] at hx
    subst hx
    rw [delMin_some, mset_pass2, msetHpList_pass1, msetHeap_some, msetHp_eq]
    rw [Multiset.sub_singleton, Multiset.erase_cons_head]

/-! ### Correctness: invariant lemmas -/

theorem php_link [LinearOrder α] {h1 h2 : Hp α} (h1p : php h1) (h2p : php h2) :
    php (link h1 h2) := by
  obtain ⟨x1, hs1⟩ := h1
  obtain ⟨x2, hs2⟩ := h2
  rw [php_eq] at h1p h2p
  by_cases hc : x1 < x2
  · rw [link_eq_pos hc, php_eq]
    constructor
    · intro h' hh'
      simp only [List.mem_cons] at hh'
      rcases hh' with rfl | hh'
      · intro y hy
        rw [msetHp_mem] at hy
        rcases hy with rfl | ⟨h'', hh'', hy⟩
        · exact le_of_lt hc
        · exact le_trans (le_of_lt hc) (h2p.1 h'' hh'' y hy)
      · intro y hy
        exact h1p.1 h' hh' y hy
    · exact ⟨h2p, h1p.2⟩
  · rw [link_eq_neg hc, php_eq]
    constructor
    · intro h' hh'
      simp only [List.mem_cons] at hh'
      rcases hh' with rfl | hh'
      · intro y hy
        rw [msetHp_mem] at hy
        rcases hy with rfl | ⟨h'', hh'', hy⟩
        · exact le_of_not_gt hc
        · exact le_trans (le_of_not_gt hc) (h1p.1 h'' hh'' y hy)
      · intro y hy
        exact h2p.1 h' hh' y hy
    · exact ⟨h1p, h2p.2⟩

theorem invar_merge [LinearOrder α] {ho1 ho2 : Heap α} (h1 : invar ho1)
    (h2 : invar ho2) : invar (merge ho1 ho2) := by
  cases ho1 with
  | none => rw [merge_none_left]; exact h2
  | some hp1 =>
    cases ho2 with
    | none => rw [merge_none_right]; exact h1
    | some hp2 =>
      rw [merge_some_some]
      exact php_link h1 h2

theorem invar_insert [LinearOrder α] {x : α} {ho : Heap α} (h : invar ho) :
    invar (insert x ho) := by
  cases ho with
  | none =>
    simp only [insert, invar_some]
    rw [php_eq]
    constructor
    · intro h' hh'
      simp at hh'
    · trivial
  | some hp =>
    simp only [insert, invar_some]
    have hphp : php (.mk x []) := by
      rw [php_eq]
      constructor
      · intro h' hh'
        simp at hh'
      · trivial
    exact php_link hphp h

theorem invar_pass1 [LinearOrder α] {hs : List (Hp α)}
    (hall : ∀ h ∈ hs, php h) : ∀ h ∈ pass1 hs, php h := by
  induction hs using List_pair_ind with
  | nil =>
    intro h hh'
    rw [pass1_nil] at hh'
    simp at hh'
  | single a =>
    intro h' hh'
    rw [pass1_single] at hh'
    simp only [List.mem_singleton] at hh'
    subst hh'
    exact hall _ List.mem_cons_self
  | cons2 h1 h2 hs ih =>
    intro h' hh'
    rw [pass1_cons2] at hh'
    simp only [List.mem_cons] at hh'
    rcases hh' with rfl | hh'
    · exact php_link (hall h1 List.mem_cons_self)
        (hall h2 (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact ih (fun h hh => hall h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))) h' hh'

theorem invar_pass2 [LinearOrder α] {hs : List (Hp α)}
    (hall : ∀ h ∈ hs, php h) : invar (pass2 hs) := by
  induction hs with
  | nil => trivial
  | cons h hs ih =>
    rw [pass2_cons]
    cases hpass : pass2 hs with
    | none =>
      exact hall h (List.mem_cons_self)
    | some h' =>
      have ih' : php h' := by
        have := ih (fun h hh => hall h (List.mem_cons_of_mem _ hh))
        rw [hpass] at this
        exact this
      exact php_link (hall h (List.mem_cons_self)) ih'

theorem invar_delMin [LinearOrder α] {ho : Heap α} (h : invar ho) :
    invar (delMin ho) := by
  cases ho with
  | none => exact h
  | some hp =>
    obtain ⟨x, hs⟩ := hp
    rw [delMin_some]
    apply invar_pass2
    apply invar_pass1
    intro h' hh'
    have hphp : php (.mk x hs) := h
    rw [php_eq] at hphp
    exact phpList_of_mem hh' hphp.2

/-! ### Correctness: `getMin` lemmas (book §23.1.1, items 2–3) -/

theorem getMin_mem (ho : Heap α) (x : α) (hx : getMin ho = some x) :
    x ∈ msetHeap ho := by
  cases ho with
  | none => simp [getMin_none] at hx
  | some h =>
    obtain ⟨r, hs⟩ := h
    simp only [getMin_some, Option.some.injEq] at hx
    subst hx
    simp [msetHeap_some, msetHp_eq]

theorem getMin_le [LinearOrder α] (ho : Heap α) (x y : α)
    (hx : getMin ho = some x) (hinv : invar ho) (hy : y ∈ msetHeap ho) :
    x ≤ y := by
  cases ho with
  | none => simp [getMin_none] at hx
  | some h =>
    obtain ⟨r, hs⟩ := h
    simp only [getMin_some, Option.some.injEq] at hx
    subst hx
    have hphp : php (.mk r hs) := hinv
    rw [php_eq] at hphp
    rw [msetHeap_some, msetHp_eq, Multiset.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_refl _
    · rw [msetHpList_mem] at hy
      obtain ⟨h', hh', hy⟩ := hy
      exact hphp.1 h' hh' y hy

theorem getMin_isLeast [LinearOrder α] (ho : Heap α) (x : α)
    (hx : getMin ho = some x) (hinv : invar ho) :
    IsLeast {y | y ∈ msetHeap ho} x := by
  refine ⟨getMin_mem ho x hx, ?_⟩
  intro y hy
  exact getMin_le ho x y hx hinv hy

/-- `getMin` is defined on every nonempty heap: the definedness clause
of the `Priority_Queue_Merge` specifications. -/
theorem getMin_defined (ho : Heap α) (hne : msetHeap ho ≠ 0) :
    ∃ x, getMin ho = some x := by
  cases ho with
  | none => simp [msetHeap] at hne
  | some h =>
    obtain ⟨x, hs⟩ := h
    exact ⟨x, rfl⟩

theorem msetHeap_eq_zero_iff (ho : Heap α) : msetHeap ho = 0 ↔ ho = none := by
  cases ho with
  | none => simp [msetHeap_none]
  | some h =>
    obtain ⟨x, hs⟩ := h
    constructor
    · intro hcontra
      have hc := congrArg Multiset.card hcontra
      simp only [msetHeap_some, msetHp_eq, Multiset.card_cons,
        Multiset.card_zero] at hc
      omega
    · intro hcontra
      simp at hcontra

/-! ### The `Priority_Queue_Merge` specification (book §23.1.1) -/

/-- All of the `Priority_Queue_Merge` specification properties for pairing
heaps, as one conjunction. In the AFP this is the `interpretation pairing:
Priority_Queue_Merge` (10 cases) at the end of `Pairing_Heap_List2.thy`,
against the locale in `HOL-Data_Structures.Priority_Queue_Specs`.
Three deliberate form changes, all strengthenings or exact equivalents,
not weakenings:
* The locale's `mset_get_min` (`get_min q = Min_mset (mset q)`) appears
  here in the decomposed form `getMin_mem` + `getMin_le` — the two lemmas
  the AFP's own case-5 proof combines via `eq_Min_iff`. For a nonempty
  finite multiset, `x ∈ s ∧ ∀ y ∈ s, x ≤ y` iff `x = Min_mset s`.
* Several locale axioms carry an `invar q` hypothesis (`mset_insert`,
  `mset_del_min`, `mset_merge`, `is_empty`) and `mset_del_min` is stated
  with `q ≠ empty` and the partial `get_min`. Here they are stated
  *without* the `invar` hypotheses and with `getMin ho = some x`, because
  Lean proves each of them unconditionally — a stronger statement, which
  implies the locale's version.
* The definedness clause `msetHeap ho ≠ 0 → ∃ x, getMin ho = some x`
  is added (see the module doc of `PairingHeap.PriorityQueue`): without
  it, the `getMin` clauses would be vacuous for an implementation whose
  `getMin` always returns `none`. -/
theorem priority_queue_merge [LinearOrder α] :
    (msetHeap (empty : Heap α) = 0) ∧
    (∀ ho : Heap α, msetHeap ho = 0 ↔ ho = none) ∧
    (∀ (x : α) (ho : Heap α),
      msetHeap (insert x ho) = {x} + msetHeap ho) ∧
    (∀ (ho : Heap α) (x : α), getMin ho = some x →
      msetHeap (delMin ho) = msetHeap ho - {x}) ∧
    (∀ (ho : Heap α) (x : α), getMin ho = some x → x ∈ msetHeap ho) ∧
    (∀ (ho : Heap α) (x y : α), getMin ho = some x → invar ho →
      y ∈ msetHeap ho → x ≤ y) ∧
    (∀ (ho : Heap α), msetHeap ho ≠ 0 → ∃ x, getMin ho = some x) ∧
    invar (empty : Heap α) ∧
    (∀ (x : α) (ho : Heap α), invar ho → invar (insert x ho)) ∧
    (∀ ho : Heap α, invar ho → invar (delMin ho)) ∧
    (∀ (ho1 ho2 : Heap α),
      msetHeap (merge ho1 ho2) = msetHeap ho1 + msetHeap ho2) ∧
    (∀ (ho1 ho2 : Heap α), invar ho1 → invar ho2 → invar (merge ho1 ho2)) := by
  refine ⟨rfl, ?_, mset_insert, mset_delMin, getMin_mem, getMin_le, ?_, trivial,
    fun _ _ h => invar_insert h, fun ho h => invar_delMin h, mset_merge,
    fun ho1 ho2 h1 h2 => invar_merge h1 h2⟩
  · intro ho
    cases ho with
    | none => simp
    | some h =>
      constructor
      · intro hcontra
        exact absurd hcontra (msetHp_ne_zero h)
      · intro hcontra
        exact absurd hcontra (by simp)
  · intro ho hne
    exact getMin_defined ho hne

/-- The `Priority_Queue_Merge` specification in the locale's form: the
locale's assumptions (the `invar` hypotheses are kept, `isEmpty` is used,
`mset_insert` is stated as `mset + {x}`, and `mset_get_min` is the
`IsLeast` form), plus the definedness clause. This is the counterpart
of `priority_queue_merge`, which states the same content in
strengthened (unconditional) form. -/
theorem priority_queue_merge_locale [LinearOrder α] :
    PriorityQueueMergeSpec (empty : Heap α) isEmpty merge insert delMin getMin
      invar msetHeap := by
  unfold PriorityQueueMergeSpec
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_⟩
  · intro ho _
    exact (msetHeap_eq_zero_iff ho).symm
  · intro x ho _
    rw [mset_insert]
    exact add_comm _ _
  · intro ho x _ _ hx
    exact mset_delMin ho x hx
  · intro ho x hinv _ hx
    exact getMin_isLeast ho x hx hinv
  · intro ho hne
    exact getMin_defined ho hne
  · intro x ho h
    exact invar_insert h
  · intro ho h _
    exact invar_delMin h
  · intro ho1 ho2 h1 h2
    exact mset_merge ho1 ho2
  · intro ho1 ho2 h1 h2
    exact invar_merge h1 h2

/-- The `Priority_Queue_Merge` specification in the book's form: Chapter 14,
Figures 14.1–14.2. The book's 9 properties, in the book's order and with
the book's `invar` hypotheses, plus the definedness clause. -/
theorem priority_queue_merge_book [LinearOrder α] :
    PriorityQueueSpec (empty : Heap α) merge insert delMin getMin invar
      msetHeap := by
  unfold PriorityQueueSpec
  refine ⟨rfl, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x ho _
    rw [mset_insert]
    exact add_comm _ _
  · intro x ho h
    exact invar_insert h
  · intro ho x _ _ hx
    exact mset_delMin ho x hx
  · intro ho h _
    exact invar_delMin h
  · intro ho x hinv _ hx
    exact getMin_isLeast ho x hx hinv
  · intro ho hne
    exact getMin_defined ho hne
  · intro ho1 ho2 h1 h2
    exact mset_merge ho1 ho2
  · intro ho1 ho2 h1 h2
    exact invar_merge h1 h2

/-! ### Exercise 23.1: `mergePairs` -/

/-- Exercise 23.1, part 1: `mergePairs hs = pass2 (pass1 hs)`. -/
theorem mergePairs_eq [LinearOrder α] (hs : List (Hp α)) :
    mergePairs hs = pass2 (pass1 hs) := by
  induction hs using List_pair_ind with
  | nil => rfl
  | single h =>
    show mergePairs [h] = pass2 (pass1 [h])
    rw [mergePairs_single, pass1_single]
    rfl
  | cons2 h1 h2 hs ih =>
    rw [mergePairs_cons2, pass1_cons2, pass2_cons]
    cases hpass : pass2 (pass1 hs) with
    | none =>
      have hmp : mergePairs hs = none := by rw [ih, hpass]
      rw [hmp]
    | some h' =>
      have hmp : mergePairs hs = some h' := by rw [ih, hpass]
      rw [hmp]

/-- Exercise 23.1, part 2 (running-time bound):
`TmergePairs hs ≤ Tpass1 hs + Tpass2 (pass1 hs)`. -/
theorem mergePairs_time_le [LinearOrder α] (hs : List (Hp α)) :
    TmergePairs hs ≤ Tpass1 hs + Tpass2 (pass1 hs) := by
  rw [TmergePairs_eq_length_div_two, Tpass1_eq_length_div_two]
  have hnonneg : 0 ≤ Tpass2 (pass1 hs) := Nat.zero_le _
  omega

end List2

end PairingHeap

end Cslib.Algorithms.Lean
