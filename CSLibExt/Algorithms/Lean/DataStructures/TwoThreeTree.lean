/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.OrderedInsert
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# 2-3 trees

A 2-3 tree is a balanced search tree in which every internal node has two or
three children and all leaves lie at the same depth. Here the tree type is
indexed by its height: a `Tree α h` has all of its leaves at depth `h`, so
balance is a typing invariant. The recursive `Balanced` predicate and
`height_eq` record the same fact at the level of the recursively computed
height. Keys stored at nodes are strict separators: in `node2 a l r` every key
of `l` is below `a` and every key of `r` is above it, and similarly with two
separators at a `node3`; this is the `Ordered` predicate.

Insertion follows the standard splitting discipline. The auxiliary `ins`
returns an `Overflow`: either a replacement tree of the same height, or a
*split* into two trees of that height separated by a promoted key. A 2-node
absorbs a split child by becoming a 3-node; a 3-node passes a split upward.
At the root, a split becomes a new 2-node and the height grows by one.
Insertion ignores an already-present key.

The machine-checked results are `ins_spec`, which bundles preservation of
`Ordered` and the equation `flatten (insert result) = orderedInsert x (flatten
t)` for the height-indexed insertion, and its root-level consequences in the
`Root` API: `Root.ordered_insert`, `Root.flatten_insert`,
`Root.mem_flatten_insert`, and `Root.contains_eq_true_iff` (search agrees with
membership in the flattening). There is no formal cost model; the index gives
height `O(log n)` only in combination with size bounds that are not stated
here. Deletion is out of scope for this module.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace TwoThreeTree

/-- A 2-3 tree indexed by height: all leaves of `Tree α h` are at depth `h`.
A `node2` stores one separator key with two children, and a `node3` stores two
separator keys with three children. -/
public inductive Tree (α : Type u) : Nat → Type u where
  | leaf : Tree α 0
  | node2 {h : Nat} (a : α) (l r : Tree α h) : Tree α (h + 1)
  | node3 {h : Nat} (a b : α) (l m r : Tree α h) : Tree α (h + 1)

/-- The result of inserting into a tree of height `h`: either a tree of the
same height, or a split into two trees of height `h` around a promoted key. -/
public inductive Overflow (α : Type u) : Nat → Type u where
  | ok {h : Nat} (t : Tree α h) : Overflow α h
  | split {h : Nat} (l : Tree α h) (k : α) (r : Tree α h) : Overflow α h

variable {α : Type u}

/-- The height of a tree, computed from its leftmost spine. -/
public def height : {h : Nat} → Tree α h → Nat
  | _, .leaf => 0
  | _, .node2 _ l _ => height l + 1
  | _, .node3 _ _ l _ _ => height l + 1

/-- The computed height of a tree agrees with its height index. -/
public theorem height_eq {h : Nat} (t : Tree α h) : height t = h := by
  induction t with
  | leaf => rfl
  | node2 _ _ _ ihl _ => exact congrArg Nat.succ ihl
  | node3 _ _ _ _ _ ihl _ _ => exact congrArg Nat.succ ihl

/-- The balance invariant: subtrees of every node have equal computed heights,
recursively, so all leaves lie at the same depth. -/
public def Balanced : {h : Nat} → Tree α h → Prop
  | _, .leaf => True
  | _, .node2 _ l r => Balanced l ∧ Balanced r ∧ height l = height r
  | _, .node3 _ _ l m r =>
      Balanced l ∧ Balanced m ∧ Balanced r ∧ height l = height m ∧ height m = height r

/-- Every height-indexed tree is balanced. -/
public theorem balanced {h : Nat} (t : Tree α h) : Balanced t := by
  induction t with
  | leaf => trivial
  | node2 _ _ _ ihl ihr => exact ⟨ihl, ihr, by rw [height_eq, height_eq]⟩
  | node3 _ _ _ _ _ ihl ihm ihr =>
    exact ⟨ihl, ihm, ihr, by rw [height_eq, height_eq], by rw [height_eq, height_eq]⟩

/-- Structural membership, independent of the ordering invariant. -/
public def Mem (x : α) : {h : Nat} → Tree α h → Prop
  | _, .leaf => False
  | _, .node2 a l r => Mem x l ∨ x = a ∨ Mem x r
  | _, .node3 a b l m r => Mem x l ∨ x = a ∨ Mem x m ∨ x = b ∨ Mem x r

public instance {h : Nat} : Membership α (Tree α h) :=
  ⟨fun t x => Mem x t⟩

@[simp] private theorem mem_leaf {x : α} :
    x ∈ (Tree.leaf : Tree α 0) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node2 {h : Nat} {x a : α} {l r : Tree α h} :
    x ∈ Tree.node2 a l r ↔ x ∈ l ∨ x = a ∨ x ∈ r :=
  Iff.rfl

@[simp] private theorem mem_node3 {h : Nat} {x a b : α} {l m r : Tree α h} :
    x ∈ Tree.node3 a b l m r ↔ x ∈ l ∨ x = a ∨ x ∈ m ∨ x = b ∨ x ∈ r :=
  Iff.rfl

/-- `All p t` states that every separator key in `t` satisfies `p`. -/
public def All (p : α → Prop) : {h : Nat} → Tree α h → Prop
  | _, .leaf => True
  | _, .node2 a l r => All p l ∧ p a ∧ All p r
  | _, .node3 a b l m r => All p l ∧ p a ∧ All p m ∧ p b ∧ All p r

private theorem all_mono {p q : α → Prop} (hmono : ∀ y, p y → q y) :
    ∀ {h : Nat} (t : Tree α h), All p t → All q t := by
  intro h t
  induction t with
  | leaf => exact fun _ => trivial
  | node2 a l r ihl ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAr⟩ := hAll
    exact ⟨ihl hAl, hmono a hpa, ihr hAr⟩
  | node3 a b l m r ihl ihm ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAm, hpb, hAr⟩ := hAll
    exact ⟨ihl hAl, hmono a hpa, ihm hAm, hmono b hpb, ihr hAr⟩

/-- `All` is equivalent to universal quantification over structural membership. -/
public theorem all_iff_forall_mem {p : α → Prop} {h : Nat} {t : Tree α h} :
    All p t ↔ ∀ x, x ∈ t → p x := by
  induction t with
  | leaf => simp [All]
  | node2 a l r ihl ihr =>
    simp only [All, mem_node2, ihl, ihr]
    constructor
    · rintro ⟨hAl, hpa, hAr⟩ x (hx | hx | hx)
      · exact hAl x hx
      · simpa [hx] using hpa
      · exact hAr x hx
    · intro hforall
      exact ⟨fun x hx => hforall x (Or.inl hx), hforall a (Or.inr (Or.inl rfl)),
        fun x hx => hforall x (Or.inr (Or.inr hx))⟩
  | node3 a b l m r ihl ihm ihr =>
    simp only [All, mem_node3, ihl, ihm, ihr]
    constructor
    · rintro ⟨hAl, hpa, hAm, hpb, hAr⟩ x (hx | hx | hx | hx | hx)
      · exact hAl x hx
      · simpa [hx] using hpa
      · exact hAm x hx
      · simpa [hx] using hpb
      · exact hAr x hx
    · intro hforall
      exact ⟨fun x hx => hforall x (Or.inl hx), hforall a (Or.inr (Or.inl rfl)),
        fun x hx => hforall x (Or.inr (Or.inr (Or.inl hx))),
        hforall b (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        fun x hx => hforall x (Or.inr (Or.inr (Or.inr (Or.inr hx))))⟩

/-- The ordering invariant: separator keys strictly separate the keys of their
subtrees, recursively. -/
public def Ordered [LT α] : {h : Nat} → Tree α h → Prop
  | _, .leaf => True
  | _, .node2 a l r =>
      Ordered l ∧ Ordered r ∧ All (· < a) l ∧ All (a < ·) r
  | _, .node3 a b l m r =>
      Ordered l ∧ Ordered m ∧ Ordered r ∧ a < b ∧ All (· < a) l ∧
        All (a < ·) m ∧ All (· < b) m ∧ All (b < ·) r

/-- Append the inorder traversal of a tree to an existing suffix in linear
time: subtrees interleaved with separator keys, accumulated without
recopying left results. -/
public def flattenAux : {h : Nat} → Tree α h → List α → List α
  | _, .leaf, suffix => suffix
  | _, .node2 a l r, suffix => flattenAux l (a :: flattenAux r suffix)
  | _, .node3 a b l m r, suffix =>
      flattenAux l (a :: flattenAux m (b :: flattenAux r suffix))

private theorem flattenAux_append {h : Nat} (t : Tree α h)
    (xs ys : List α) :
    flattenAux t (xs ++ ys) = flattenAux t xs ++ ys := by
  induction t generalizing xs with
  | leaf => rfl
  | node2 a l r ihl ihr =>
      simp only [flattenAux]
      rw [ihr]
      change flattenAux l ((a :: flattenAux r xs) ++ ys) =
        flattenAux l (a :: flattenAux r xs) ++ ys
      exact ihl _
  | node3 a b l m r ihl ihm ihr =>
      simp only [flattenAux]
      rw [ihr]
      change flattenAux l
          (a :: flattenAux m ((b :: flattenAux r xs) ++ ys)) =
        flattenAux l (a :: flattenAux m (b :: flattenAux r xs)) ++ ys
      rw [ihm]
      change flattenAux l ((a :: flattenAux m (b :: flattenAux r xs)) ++ ys) =
        flattenAux l (a :: flattenAux m (b :: flattenAux r xs)) ++ ys
      exact ihl _

/-- The linear-time inorder traversal of a tree: subtrees interleaved with
separator keys. -/
public def flatten {h : Nat} (t : Tree α h) : List α :=
  flattenAux t []

/-- `flattenAux` prepends the flattening of its tree to the suffix. -/
public theorem flattenAux_eq {h : Nat} (t : Tree α h) (suffix : List α) :
    flattenAux t suffix = flatten t ++ suffix := by
  show flattenAux t suffix = flattenAux t [] ++ suffix
  rw [← flattenAux_append t [] suffix]
  simp

@[simp] public theorem flatten_leaf : flatten (Tree.leaf : Tree α 0) = [] :=
  rfl

@[simp] public theorem flatten_node2 {h : Nat} {a : α} {l r : Tree α h} :
    flatten (Tree.node2 a l r) = flatten l ++ a :: flatten r := by
  show flattenAux l (a :: flattenAux r []) =
    flattenAux l [] ++ a :: flattenAux r []
  simpa using flattenAux_append l [] (a :: flattenAux r [])

@[simp] public theorem flatten_node3 {h : Nat} {a b : α} {l m r : Tree α h} :
    flatten (Tree.node3 a b l m r) =
      flatten l ++ a :: (flatten m ++ b :: flatten r) := by
  have hm : flattenAux m (b :: flattenAux r []) =
      flattenAux m [] ++ b :: flattenAux r [] := by
    simpa using flattenAux_append m [] (b :: flattenAux r [])
  show flattenAux l (a :: flattenAux m (b :: flattenAux r [])) =
    flattenAux l [] ++ a :: (flattenAux m [] ++ b :: flattenAux r [])
  rw [hm]
  simpa using flattenAux_append l []
    (a :: (flattenAux m [] ++ b :: flattenAux r []))

/-- The flattening contains exactly the structurally present keys. -/
public theorem mem_flatten {x : α} {h : Nat} {t : Tree α h} :
    x ∈ flatten t ↔ x ∈ t := by
  induction t with
  | leaf => simp
  | node2 a l r ihl ihr => simp [ihl, ihr, or_left_comm]
  | node3 a b l m r ihl ihm ihr => simp [ihl, ihm, ihr, or_left_comm]

/-- `All` is equivalent to universal quantification over the flattening. -/
public theorem all_iff_forall_flatten {p : α → Prop} {h : Nat} {t : Tree α h} :
    All p t ↔ ∀ y ∈ flatten t, p y := by
  rw [all_iff_forall_mem]
  constructor
  · intro hforall y hy
    exact hforall y (mem_flatten.mp hy)
  · intro hforall y hy
    exact hforall y (mem_flatten.mpr hy)

/-- The flattening of an ordered tree is strictly increasing. -/
public theorem ordered_flatten_pairwise [LinearOrder α] {h : Nat} {t : Tree α h}
    (hOrd : Ordered t) : List.Pairwise (· < ·) (flatten t) := by
  induction t with
  | leaf => simp
  | node2 a l r ihl ihr =>
    obtain ⟨hOl, hOr, hAl, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBr : ∀ y ∈ flatten r, a < y := all_iff_forall_flatten.mp hAr
    rw [flatten_node2, List.pairwise_append]
    refine ⟨ihl hOl, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨hBr, ihr hOr⟩
    · intro y hy z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hBl y hy
      · exact lt_trans (hBl y hy) (hBr z hz)
  | node3 a b l m r ihl ihm ihr =>
    obtain ⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBmgt : ∀ y ∈ flatten m, a < y := all_iff_forall_flatten.mp hAmgt
    have hBmlt : ∀ y ∈ flatten m, y < b := all_iff_forall_flatten.mp hAmlt
    have hBr : ∀ y ∈ flatten r, b < y := all_iff_forall_flatten.mp hAr
    have hpwMid : List.Pairwise (· < ·) (flatten m ++ b :: flatten r) := by
      rw [List.pairwise_append]
      refine ⟨ihm hOm, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨hBr, ihr hOr⟩
      · intro y hy z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hBmlt y hy
        · exact lt_trans (hBmlt y hy) (hBr z hz)
    have hpwTail : List.Pairwise (· < ·) (a :: (flatten m ++ b :: flatten r)) := by
      rw [List.pairwise_cons]
      refine ⟨?_, hpwMid⟩
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hBmgt y hy
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hab
        · exact lt_trans hab (hBr y hy)
    rw [flatten_node3, List.pairwise_append]
    refine ⟨ihl hOl, hpwTail, ?_⟩
    intro y hy z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hBl y hy
    · exact lt_trans (hBl y hy) ((List.pairwise_cons.mp hpwTail).1 z hz)

/-- The flattening of an ordered tree has no duplicate keys. -/
public theorem flatten_nodup [LinearOrder α] {h : Nat} {t : Tree α h}
    (hOrd : Ordered t) : (flatten t).Nodup :=
  (ordered_flatten_pairwise hOrd).nodup

/-- Search a tree by comparing the query against separator keys. -/
public def contains [LinearOrder α] (x : α) : {h : Nat} → Tree α h → Bool
  | _, .leaf => false
  | _, .node2 a l r =>
      if x < a then contains x l
      else if a < x then contains x r
      else true
  | _, .node3 a b l m r =>
      if x < a then contains x l
      else if a < x then
        if x < b then contains x m
        else if b < x then contains x r
        else true
      else true

/-- Search succeeds exactly on the keys of the flattening, for ordered trees. -/
public theorem contains_eq_true_iff [LinearOrder α] {x : α} {h : Nat} {t : Tree α h}
    (hOrd : Ordered t) : contains x t = true ↔ x ∈ flatten t := by
  induction t with
  | leaf => simp [contains]
  | node2 a l r ihl ihr =>
    obtain ⟨hOl, hOr, hAl, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBr : ∀ y ∈ flatten r, a < y := all_iff_forall_flatten.mp hAr
    by_cases hxa : x < a
    · have hNotR : x ∉ flatten r := fun hmem => lt_asymm hxa (hBr x hmem)
      simp [contains, hxa, ihl hOl, hNotR, ne_of_lt hxa]
    · by_cases hax : a < x
      · have hNotL : x ∉ flatten l := fun hmem => lt_asymm hax (hBl x hmem)
        simp [contains, hxa, hax, ihr hOr, hNotL, ne_of_gt hax]
      · obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        simp [contains, hxa]
  | node3 a b l m r ihl ihm ihr =>
    obtain ⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBmgt : ∀ y ∈ flatten m, a < y := all_iff_forall_flatten.mp hAmgt
    have hBmlt : ∀ y ∈ flatten m, y < b := all_iff_forall_flatten.mp hAmlt
    have hBr : ∀ y ∈ flatten r, b < y := all_iff_forall_flatten.mp hAr
    by_cases hxa : x < a
    · have hNotM : x ∉ flatten m := fun hmem => lt_asymm hxa (hBmgt x hmem)
      have hNotR : x ∉ flatten r :=
        fun hmem => lt_asymm (lt_trans hxa hab) (hBr x hmem)
      simp [contains, hxa, ihl hOl, hNotM, hNotR, ne_of_lt hxa,
        ne_of_lt (lt_trans hxa hab)]
    · by_cases hax : a < x
      · by_cases hxb : x < b
        · have hNotL : x ∉ flatten l := fun hmem => lt_asymm hax (hBl x hmem)
          have hNotR : x ∉ flatten r := fun hmem => lt_asymm hxb (hBr x hmem)
          simp [contains, hxa, hax, hxb, ihm hOm, hNotL, hNotR, ne_of_gt hax,
            ne_of_lt hxb]
        · by_cases hbx : b < x
          · have hNotL : x ∉ flatten l := fun hmem => lt_asymm hax (hBl x hmem)
            have hNotM : x ∉ flatten m := fun hmem => lt_asymm hbx (hBmlt x hmem)
            simp [contains, hxa, hax, hxb, hbx, ihr hOr, hNotL, hNotM,
              ne_of_gt hax, ne_of_gt hbx]
          · obtain rfl : x = b := le_antisymm (le_of_not_gt hbx) (le_of_not_gt hxb)
            simp [contains, hxa, hax, hxb]
      · obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        simp [contains, hxa]

private theorem orderedInsert_append_left [LinearOrder α] {x a : α} (hxa : x < a) :
    ∀ (L R : List α), (∀ y ∈ L, y < a) →
      orderedInsert x (L ++ a :: R) = orderedInsert x L ++ a :: R := by
  intro L
  induction L with
  | nil =>
    intro R _
    simp [orderedInsert, hxa]
  | cons b bs ih =>
    intro R hL
    have hbs : ∀ y ∈ bs, y < a := fun y hy => hL y (List.mem_cons_of_mem b hy)
    show orderedInsert x (b :: (bs ++ a :: R)) = orderedInsert x (b :: bs) ++ a :: R
    rcases lt_trichotomy x b with hlt | heq | hgt
    · simp [orderedInsert, hlt]
    · have hnot1 : ¬x < b := by rw [heq]; exact lt_irrefl _
      have hnot2 : ¬b < x := by rw [heq]; exact lt_irrefl _
      simp [orderedInsert, hnot1, hnot2]
    · have hnot : ¬x < b := not_lt_of_ge (le_of_lt hgt)
      simp [orderedInsert, hnot, hgt, ih R hbs]

private theorem orderedInsert_append_right [LinearOrder α] {x a : α} (hax : a < x) :
    ∀ (L R : List α), (∀ y ∈ L, y < x) →
      orderedInsert x (L ++ a :: R) = L ++ a :: orderedInsert x R := by
  intro L
  induction L with
  | nil =>
    intro R _
    have hnot : ¬x < a := not_lt_of_ge (le_of_lt hax)
    simp [orderedInsert, hnot, hax]
  | cons b bs ih =>
    intro R hL
    have hb : b < x := hL b (by simp)
    have hbs : ∀ y ∈ bs, y < x := fun y hy => hL y (List.mem_cons_of_mem b hy)
    have hnot : ¬x < b := not_lt_of_ge (le_of_lt hb)
    show orderedInsert x (b :: (bs ++ a :: R)) = (b :: bs) ++ a :: orderedInsert x R
    simp [orderedInsert, hnot, hb, ih R hbs]

private theorem orderedInsert_append_eq [LinearOrder α] (a : α) :
    ∀ (L R : List α), (∀ y ∈ L, y < a) →
      orderedInsert a (L ++ a :: R) = L ++ a :: R := by
  intro L
  induction L with
  | nil =>
    intro R _
    simp [orderedInsert, lt_irrefl a]
  | cons b bs ih =>
    intro R hL
    have hb : b < a := hL b (by simp)
    have hbs : ∀ y ∈ bs, y < a := fun y hy => hL y (List.mem_cons_of_mem b hy)
    have hnot : ¬a < b := not_lt_of_ge (le_of_lt hb)
    show orderedInsert a (b :: (bs ++ a :: R)) = (b :: bs) ++ a :: R
    simp [orderedInsert, hnot, hb, ih R hbs]

/-- Insert a key into a height-indexed tree, returning an `Overflow`. A leaf
always splits; a 2-node absorbs a split child by becoming a 3-node; a 3-node
with a split child splits in turn, promoting the appropriate separator. Inserting
a key equal to a separator leaves the tree unchanged. -/
public def ins [LinearOrder α] (x : α) : {h : Nat} → Tree α h → Overflow α h
  | _, .leaf => .split .leaf x .leaf
  | _, .node2 a l r =>
      if x < a then
        match ins x l with
        | .ok l' => .ok (.node2 a l' r)
        | .split l₁ k l₂ => .ok (.node3 k a l₁ l₂ r)
      else if a < x then
        match ins x r with
        | .ok r' => .ok (.node2 a l r')
        | .split r₁ k r₂ => .ok (.node3 a k l r₁ r₂)
      else .ok (.node2 a l r)
  | _, .node3 a b l m r =>
      if x < a then
        match ins x l with
        | .ok l' => .ok (.node3 a b l' m r)
        | .split l₁ k l₂ => .split (.node2 k l₁ l₂) a (.node2 b m r)
      else if a < x then
        if x < b then
          match ins x m with
          | .ok m' => .ok (.node3 a b l m' r)
          | .split m₁ k m₂ => .split (.node2 a l m₁) k (.node2 b m₂ r)
        else if b < x then
          match ins x r with
          | .ok r' => .ok (.node3 a b l m r')
          | .split r₁ k r₂ => .split (.node2 a l m) b (.node2 k r₁ r₂)
        else .ok (.node3 a b l m r)
      else .ok (.node3 a b l m r)

/-- The specification of `ins x t` as an `Overflow` of a given source tree `t`:
in the `ok` case the result is ordered with the expected flattening, and in the
`split` case both parts are ordered, separated by the promoted key, with the
expected combined flattening. -/
public def InsSpec [LinearOrder α] (x : α) {h : Nat} (t : Tree α h) :
    Overflow α h → Prop
  | .ok t' => Ordered t' ∧ flatten t' = orderedInsert x (flatten t)
  | .split l k r =>
      Ordered l ∧ Ordered r ∧ All (· < k) l ∧ All (k < ·) r ∧
        flatten l ++ k :: flatten r = orderedInsert x (flatten t)

/-- `All` lifted to an insertion overflow. -/
private def AllOverflow (p : α → Prop) : {h : Nat} → Overflow α h → Prop
  | _, .ok t => All p t
  | _, .split l k r => All p l ∧ p k ∧ All p r

private theorem all_ins [LinearOrder α] {p : α → Prop} {x : α} (hx : p x) :
    ∀ {h : Nat} (t : Tree α h), All p t → AllOverflow p (ins x t) := by
  intro hidx t
  induction t with
  | leaf =>
    intro _
    exact ⟨trivial, hx, trivial⟩
  | node2 a l r ihl ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAr⟩ := hAll
    by_cases hxa : x < a
    · have ih := ihl hAl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l' r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨ih, hpa, hAr⟩
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨h1, h2, h3⟩ := ih
        have hEq : ins x (Tree.node2 a l r) =
            Overflow.ok (Tree.node3 k a l₁ l₂ r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨h1, h2, h3, hpa, hAr⟩
    · by_cases hax : a < x
      · have ih := ihr hAr
        cases hins : ins x r with
        | ok r' =>
          rw [hins] at ih
          have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l r') := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          exact ⟨hAl, hpa, ih⟩
        | split r₁ k r₂ =>
          rw [hins] at ih
          obtain ⟨h1, h2, h3⟩ := ih
          have hEq : ins x (Tree.node2 a l r) =
              Overflow.ok (Tree.node3 a k l r₁ r₂) := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          exact ⟨hAl, hpa, h1, h2, h3⟩
      · have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        exact ⟨hAl, hpa, hAr⟩
  | node3 a b l m r ihl ihm ihr =>
    intro hAll
    obtain ⟨hAl, hpa, hAm, hpb, hAr⟩ := hAll
    by_cases hxa : x < a
    · have ih := ihl hAl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l' m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨ih, hpa, hAm, hpb, hAr⟩
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨h1, h2, h3⟩ := ih
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.split (Tree.node2 k l₁ l₂) a (Tree.node2 b m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        exact ⟨⟨h1, h2, h3⟩, hpa, ⟨hAm, hpb, hAr⟩⟩
    · by_cases hax : a < x
      · by_cases hxb : x < b
        · have ih := ihm hAm
          cases hins : ins x m with
          | ok m' =>
            rw [hins] at ih
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m' r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            exact ⟨hAl, hpa, ih, hpb, hAr⟩
          | split m₁ k m₂ =>
            rw [hins] at ih
            obtain ⟨h1, h2, h3⟩ := ih
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.split (Tree.node2 a l m₁) k (Tree.node2 b m₂ r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            exact ⟨⟨hAl, hpa, h1⟩, h2, ⟨h3, hpb, hAr⟩⟩
        · by_cases hbx : b < x
          · have ih := ihr hAr
            cases hins : ins x r with
            | ok r' =>
              rw [hins] at ih
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.ok (Tree.node3 a b l m r') := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              exact ⟨hAl, hpa, hAm, hpb, ih⟩
            | split r₁ k r₂ =>
              rw [hins] at ih
              obtain ⟨h1, h2, h3⟩ := ih
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.split (Tree.node2 a l m) b (Tree.node2 k r₁ r₂) := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              exact ⟨⟨hAl, hpa, hAm⟩, hpb, ⟨h1, h2, h3⟩⟩
          · have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m r) := by
              simp [ins, hxa, hax, hxb, hbx]
            rw [hEq]
            exact ⟨hAl, hpa, hAm, hpb, hAr⟩
      · have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l m r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        exact ⟨hAl, hpa, hAm, hpb, hAr⟩

/-- Insertion into an ordered tree satisfies `InsSpec`: it preserves the
ordering invariant and its flattening is `orderedInsert` of the old flattening.
Balance is automatic from the height index. -/
public theorem ins_spec [LinearOrder α] (x : α) :
    ∀ {h : Nat} (t : Tree α h), Ordered t → InsSpec x t (ins x t) := by
  intro hidx t
  induction t with
  | leaf =>
    intro _
    show InsSpec x Tree.leaf (Overflow.split Tree.leaf x Tree.leaf)
    exact ⟨trivial, trivial, trivial, trivial, by simp [orderedInsert]⟩
  | node2 a l r ihl ihr =>
    intro hOrd
    obtain ⟨hOl, hOr, hAl, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    by_cases hxa : x < a
    · have ih := ihl hOl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        obtain ⟨hOl', hf⟩ := ih
        have hAll' : All (· < a) l' := by
          have hAll := all_ins (p := (· < a)) hxa l hAl
          rw [hins] at hAll
          exact hAll
        have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l' r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hOl', hOr, hAll', hAr⟩, ?_⟩
        simp only [flatten_node2]
        rw [hf, orderedInsert_append_left hxa _ _ hBl]
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
        have hAllSplit := all_ins (p := (· < a)) hxa l hAl
        rw [hins] at hAllSplit
        obtain ⟨-, hka, hAa₂⟩ := hAllSplit
        have hEq : ins x (Tree.node2 a l r) =
            Overflow.ok (Tree.node3 k a l₁ l₂ r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hO₁, hO₂, hOr, hka, hA₁, hA₂, hAa₂, hAr⟩, ?_⟩
        simp only [flatten_node3, flatten_node2]
        rw [orderedInsert_append_left hxa _ _ hBl, ← hf]
        simp [List.append_assoc]
    · by_cases hax : a < x
      · have hBlx : ∀ y ∈ flatten l, y < x :=
          fun y hy => lt_trans (hBl y hy) hax
        have ih := ihr hOr
        cases hins : ins x r with
        | ok r' =>
          rw [hins] at ih
          obtain ⟨hOr', hf⟩ := ih
          have hAll' : All (a < ·) r' := by
            have hAll := all_ins (p := (a < ·)) hax r hAr
            rw [hins] at hAll
            exact hAll
          have hEq : ins x (Tree.node2 a l r) =
              Overflow.ok (Tree.node2 a l r') := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          refine ⟨⟨hOl, hOr', hAl, hAll'⟩, ?_⟩
          simp only [flatten_node2]
          rw [hf, orderedInsert_append_right hax _ _ hBlx]
        | split r₁ k r₂ =>
          rw [hins] at ih
          obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
          have hAllSplit := all_ins (p := (a < ·)) hax r hAr
          rw [hins] at hAllSplit
          obtain ⟨hAa₁, hak, -⟩ := hAllSplit
          have hEq : ins x (Tree.node2 a l r) =
              Overflow.ok (Tree.node3 a k l r₁ r₂) := by
            simp [ins, hxa, hax, hins]
          rw [hEq]
          refine ⟨⟨hOl, hO₁, hO₂, hak, hAl, hAa₁, hA₁, hA₂⟩, ?_⟩
          simp only [flatten_node3, flatten_node2]
          rw [orderedInsert_append_right hax _ _ hBlx, ← hf]
      · have hEq : ins x (Tree.node2 a l r) = Overflow.ok (Tree.node2 a l r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        refine ⟨⟨hOl, hOr, hAl, hAr⟩, ?_⟩
        simp only [flatten_node2]
        rw [orderedInsert_append_eq _ _ _ hBl]
  | node3 a b l m r ihl ihm ihr =>
    intro hOrd
    obtain ⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩ := hOrd
    have hBl : ∀ y ∈ flatten l, y < a := all_iff_forall_flatten.mp hAl
    have hBmlt : ∀ y ∈ flatten m, y < b := all_iff_forall_flatten.mp hAmlt
    by_cases hxa : x < a
    · have ih := ihl hOl
      cases hins : ins x l with
      | ok l' =>
        rw [hins] at ih
        obtain ⟨hOl', hf⟩ := ih
        have hAll' : All (· < a) l' := by
          have hAll := all_ins (p := (· < a)) hxa l hAl
          rw [hins] at hAll
          exact hAll
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l' m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hOl', hOm, hOr, hab, hAll', hAmgt, hAmlt, hAr⟩, ?_⟩
        simp only [flatten_node3]
        rw [hf, orderedInsert_append_left hxa _ _ hBl]
      | split l₁ k l₂ =>
        rw [hins] at ih
        obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
        have hAllSplit := all_ins (p := (· < a)) hxa l hAl
        rw [hins] at hAllSplit
        obtain ⟨hAa₁, hka, hAa₂⟩ := hAllSplit
        have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.split (Tree.node2 k l₁ l₂) a (Tree.node2 b m r) := by
          simp [ins, hxa, hins]
        rw [hEq]
        refine ⟨⟨hO₁, hO₂, hA₁, hA₂⟩, ⟨hOm, hOr, hAmlt, hAr⟩, ⟨hAa₁, hka, hAa₂⟩,
          ⟨hAmgt, hab, all_mono (fun y hy => lt_trans hab hy) r hAr⟩, ?_⟩
        simp only [flatten_node2, flatten_node3]
        rw [orderedInsert_append_left hxa _ _ hBl, ← hf]
    · by_cases hax : a < x
      · have hBlx : ∀ y ∈ flatten l, y < x :=
          fun y hy => lt_trans (hBl y hy) hax
        by_cases hxb : x < b
        · have ih := ihm hOm
          cases hins : ins x m with
          | ok m' =>
            rw [hins] at ih
            obtain ⟨hOm', hf⟩ := ih
            have hAllGt : All (a < ·) m' := by
              have hAll := all_ins (p := (a < ·)) hax m hAmgt
              rw [hins] at hAll
              exact hAll
            have hAllLt : All (· < b) m' := by
              have hAll := all_ins (p := (· < b)) hxb m hAmlt
              rw [hins] at hAll
              exact hAll
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m' r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            refine ⟨⟨hOl, hOm', hOr, hab, hAl, hAllGt, hAllLt, hAr⟩, ?_⟩
            simp only [flatten_node3]
            rw [hf, orderedInsert_append_right hax _ _ hBlx,
              orderedInsert_append_left hxb _ _ hBmlt]
          | split m₁ k m₂ =>
            rw [hins] at ih
            obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
            have hAllGt := all_ins (p := (a < ·)) hax m hAmgt
            rw [hins] at hAllGt
            obtain ⟨hAm₁gt, hak, -⟩ := hAllGt
            have hAllLt := all_ins (p := (· < b)) hxb m hAmlt
            rw [hins] at hAllLt
            obtain ⟨-, hkb, hAm₂lt⟩ := hAllLt
            have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.split (Tree.node2 a l m₁) k (Tree.node2 b m₂ r) := by
              simp [ins, hxa, hax, hxb, hins]
            rw [hEq]
            refine ⟨⟨hOl, hO₁, hAl, hAm₁gt⟩, ⟨hO₂, hOr, hAm₂lt, hAr⟩,
              ⟨all_mono (fun y hy => lt_trans hy hak) l hAl, hak, hA₁⟩,
              ⟨hA₂, hkb, all_mono (fun y hy => lt_trans hkb hy) r hAr⟩, ?_⟩
            simp only [flatten_node2, flatten_node3]
            rw [orderedInsert_append_right hax _ _ hBlx,
              orderedInsert_append_left hxb _ _ hBmlt, ← hf]
            simp [List.append_assoc]
        · by_cases hbx : b < x
          · have hBmx : ∀ y ∈ flatten m, y < x :=
              fun y hy => lt_trans (hBmlt y hy) hbx
            have ih := ihr hOr
            cases hins : ins x r with
            | ok r' =>
              rw [hins] at ih
              obtain ⟨hOr', hf⟩ := ih
              have hAll' : All (b < ·) r' := by
                have hAll := all_ins (p := (b < ·)) hbx r hAr
                rw [hins] at hAll
                exact hAll
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.ok (Tree.node3 a b l m r') := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              refine ⟨⟨hOl, hOm, hOr', hab, hAl, hAmgt, hAmlt, hAll'⟩, ?_⟩
              simp only [flatten_node3]
              rw [hf, orderedInsert_append_right hax _ _ hBlx,
                orderedInsert_append_right hbx _ _ hBmx]
            | split r₁ k r₂ =>
              rw [hins] at ih
              obtain ⟨hO₁, hO₂, hA₁, hA₂, hf⟩ := ih
              have hAllSplit := all_ins (p := (b < ·)) hbx r hAr
              rw [hins] at hAllSplit
              obtain ⟨hAr₁, hbk, hAr₂⟩ := hAllSplit
              have hEq : ins x (Tree.node3 a b l m r) =
                  Overflow.split (Tree.node2 a l m) b (Tree.node2 k r₁ r₂) := by
                simp [ins, hxa, hax, hxb, hbx, hins]
              rw [hEq]
              refine ⟨⟨hOl, hOm, hAl, hAmgt⟩, ⟨hO₁, hO₂, hA₁, hA₂⟩,
                ⟨all_mono (fun y hy => lt_trans hy hab) l hAl, hab, hAmlt⟩,
                ⟨hAr₁, hbk, hAr₂⟩, ?_⟩
              simp only [flatten_node2, flatten_node3]
              rw [orderedInsert_append_right hax _ _ hBlx,
                orderedInsert_append_right hbx _ _ hBmx, ← hf]
              simp [List.append_assoc]
          · have hEq : ins x (Tree.node3 a b l m r) =
                Overflow.ok (Tree.node3 a b l m r) := by
              simp [ins, hxa, hax, hxb, hbx]
            rw [hEq]
            obtain rfl : x = b := le_antisymm (le_of_not_gt hbx) (le_of_not_gt hxb)
            refine ⟨⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩, ?_⟩
            simp only [flatten_node3]
            rw [orderedInsert_append_right hax _ _ hBlx,
              orderedInsert_append_eq _ _ _ hBmlt]
      · have hEq : ins x (Tree.node3 a b l m r) =
            Overflow.ok (Tree.node3 a b l m r) := by
          simp [ins, hxa, hax]
        rw [hEq]
        obtain rfl : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        refine ⟨⟨hOl, hOm, hOr, hab, hAl, hAmgt, hAmlt, hAr⟩, ?_⟩
        simp only [flatten_node3]
        rw [orderedInsert_append_eq _ _ _ hBl]

/-- A 2-3 tree with existentially quantified height, for use as a standalone
search tree. -/
public structure Root (α : Type u) where
  /-- The height of the underlying tree. -/
  height : Nat
  /-- The underlying height-indexed tree. -/
  tree : Tree α height

/-- Turn an insertion overflow into a root: a split becomes a new 2-node one
level higher. -/
public def Overflow.toRoot : {h : Nat} → Overflow α h → Root α
  | _, .ok t => ⟨_, t⟩
  | _, .split l k r => ⟨_, .node2 k l r⟩

/-- The empty 2-3 tree. -/
public def Root.empty : Root α :=
  ⟨0, Tree.leaf⟩

/-- The inorder traversal of a root's tree. -/
public def Root.flatten (t : Root α) : List α :=
  TwoThreeTree.flatten t.tree

/-- Search a root's tree by separator comparisons. -/
public def Root.contains [LinearOrder α] (x : α) (t : Root α) : Bool :=
  TwoThreeTree.contains x t.tree

/-- The ordering invariant for a root's tree. -/
public def Root.Ordered [LT α] (t : Root α) : Prop :=
  TwoThreeTree.Ordered t.tree

/-- Insert a key into a root, growing the height by one exactly when the root
splits. Insertion ignores an already-present key. -/
public def Root.insert [LinearOrder α] (x : α) (t : Root α) : Root α :=
  Overflow.toRoot (ins x t.tree)

/-- The empty tree is ordered. -/
public theorem Root.ordered_empty [LT α] : (Root.empty : Root α).Ordered :=
  trivial

@[simp] public theorem Root.flatten_empty :
    (Root.empty : Root α).flatten = [] :=
  rfl

/-- The computed height of a root's tree agrees with its stored height. -/
public theorem Root.height_tree (t : Root α) :
    TwoThreeTree.height t.tree = t.height :=
  height_eq t.tree

/-- Every root's tree is balanced. -/
public theorem Root.balanced (t : Root α) : Balanced t.tree :=
  TwoThreeTree.balanced t.tree

/-- Insertion preserves the ordering invariant at the root. -/
public theorem Root.ordered_insert [LinearOrder α] {x : α} {t : Root α}
    (hOrd : t.Ordered) : (t.insert x).Ordered := by
  have hSpec := ins_spec x t.tree hOrd
  cases hins : ins x t.tree with
  | ok t' =>
    rw [hins] at hSpec
    obtain ⟨hOrd', -⟩ := hSpec
    have hIns : t.insert x = (⟨t.height, t'⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    exact hOrd'
  | split l k r =>
    rw [hins] at hSpec
    obtain ⟨hOl, hOr, hAl, hAr, -⟩ := hSpec
    have hIns : t.insert x = (⟨t.height + 1, Tree.node2 k l r⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    exact ⟨hOl, hOr, hAl, hAr⟩

/-- The flattening after root insertion is `orderedInsert` of the flattening. -/
public theorem Root.flatten_insert [LinearOrder α] {x : α} {t : Root α}
    (hOrd : t.Ordered) : (t.insert x).flatten = orderedInsert x t.flatten := by
  have hSpec := ins_spec x t.tree hOrd
  cases hins : ins x t.tree with
  | ok t' =>
    rw [hins] at hSpec
    obtain ⟨-, hf⟩ := hSpec
    have hIns : t.insert x = (⟨t.height, t'⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    exact hf
  | split l k r =>
    rw [hins] at hSpec
    obtain ⟨-, -, -, -, hf⟩ := hSpec
    have hIns : t.insert x = (⟨t.height + 1, Tree.node2 k l r⟩ : Root α) := by
      simp [Root.insert, Overflow.toRoot, hins]
    rw [hIns]
    show TwoThreeTree.flatten (Tree.node2 k l r) =
      orderedInsert x (TwoThreeTree.flatten t.tree)
    rw [flatten_node2]
    exact hf

/-- Root insertion adds exactly the inserted key to the flattening. -/
public theorem Root.mem_flatten_insert [LinearOrder α] {x y : α} {t : Root α}
    (hOrd : t.Ordered) : y ∈ (t.insert x).flatten ↔ y = x ∨ y ∈ t.flatten := by
  rw [Root.flatten_insert hOrd, mem_orderedInsert]

/-- Search at the root succeeds exactly on keys of the flattening. -/
public theorem Root.contains_eq_true_iff [LinearOrder α] {x : α} {t : Root α}
    (hOrd : t.Ordered) : t.contains x = true ↔ x ∈ t.flatten :=
  TwoThreeTree.contains_eq_true_iff hOrd

/-- Insertion grows the stored height by at most one. -/
public theorem Root.height_insert_le [LinearOrder α] (x : α) (t : Root α) :
    (t.insert x).height ≤ t.height + 1 := by
  cases hins : ins x t.tree <;> simp [Root.insert, Overflow.toRoot, hins]

/-- Build a root by inserting the list from right to left. -/
public def Root.fromList [LinearOrder α] : List α → Root α
  | [] => .empty
  | x :: xs => Root.insert x (Root.fromList xs)

/-- A tree built from a list is ordered. -/
public theorem Root.ordered_fromList [LinearOrder α] (xs : List α) :
    (Root.fromList xs).Ordered := by
  induction xs with
  | nil => exact Root.ordered_empty
  | cons _ _ ih => exact Root.ordered_insert ih

/-- A key is in the flattening of a tree built from a list exactly when it is
in the list. -/
public theorem Root.mem_fromList [LinearOrder α] {x : α} {xs : List α} :
    x ∈ (Root.fromList xs).flatten ↔ x ∈ xs := by
  induction xs with
  | nil => simp [Root.fromList]
  | cons y ys ih =>
    show x ∈ ((Root.fromList ys).insert y).flatten ↔ x ∈ y :: ys
    rw [Root.mem_flatten_insert (Root.ordered_fromList ys), ih]
    simp only [List.mem_cons]

example : (Root.insert 3 (Root.insert 1
    (Root.insert 2 (Root.empty : Root Nat)))).flatten = [1, 2, 3] := by
  have h0 : (Root.empty : Root Nat).Ordered := Root.ordered_empty
  have h1 : ((Root.empty : Root Nat).insert 2).Ordered :=
    Root.ordered_insert h0
  have h2 : (((Root.empty : Root Nat).insert 2).insert 1).Ordered :=
    Root.ordered_insert h1
  rw [Root.flatten_insert h2, Root.flatten_insert h1, Root.flatten_insert h0,
    Root.flatten_empty]
  rfl

/-- Deprecated forwarder for the shared `Cslib.Algorithms.Lean.orderedInsert`.
Kept so existing fully qualified references to `TwoThreeTree.orderedInsert`
keep elaborating; new code should use the shared name. -/
@[deprecated "use Cslib.Algorithms.Lean.orderedInsert instead"
  (since := "2026-10-12")]
public def orderedInsert [LinearOrder α] (x : α) : List α → List α :=
  Cslib.Algorithms.Lean.orderedInsert x

/-- Deprecated forwarder for the shared `Cslib.Algorithms.Lean.mem_orderedInsert`. -/
@[deprecated "use Cslib.Algorithms.Lean.mem_orderedInsert instead"
  (since := "2026-10-12")]
public theorem mem_orderedInsert [LinearOrder α] {x y : α} {xs : List α} :
    y ∈ orderedInsert x xs ↔ y = x ∨ y ∈ xs :=
  Cslib.Algorithms.Lean.mem_orderedInsert

end TwoThreeTree
end Cslib.Algorithms.Lean
