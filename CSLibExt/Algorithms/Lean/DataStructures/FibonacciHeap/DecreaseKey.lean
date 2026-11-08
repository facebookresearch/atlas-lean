/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap

/-!
# Decrease-key for Fibonacci heaps: cut without marks

CLRS `FIB-HEAP-DECREASE-KEY` (Chapter 19) lowers the key of a node `x`, cuts `x` from
its parent if heap order is violated, and then performs cascading cuts: a parent that
has already lost one child since it was linked (it is marked) is itself cut, and so on
up the tree. The parent module `FibonacciHeap.lean` represents trees as persistent rose
trees storing only a degree, a root value, and children: there are no parent pointers
and no mark field, so the CLRS procedure cannot be implemented literally here. This
file implements the honest functional analogue and states plainly where it deviates.

The node to decrease is addressed by a path: a list of child indices from a root of the
forest (`FibonacciTree.subtreeAt`). A path is the persistent substitute for the node
handle that an imperative implementation passes to decrease-key; no parent pointers are
simulated. `FibonacciTree.cutAt` extracts the subtree at a path and rebuilds its
ancestors with corrected degrees, `FibonacciTree.decreaseRoot` lowers the extracted
root, and `FibonacciHeap.decreaseKey` puts the decreased subtree back as a new tree in
the root list. The cut is unconditional: the subtree moves to the root list even when
the decreased key would still respect heap order under its old parent. That is a
simplification, not a correctness issue.

What is missing, plainly: cascading cuts. Without a mark field there is no record of
how many children a node has lost since it was linked, so ancestors of a cut node are
never themselves cut, and a node can lose arbitrarily many children over successive
decrease-key operations. Correctness (heap order, the represented multiset, the cached
minimum) does not depend on marks and is fully proved here. The classical amortized
`O(1)` bound for decrease-key and the Fibonacci size bound on trees of a given degree
do depend on marks and cascading cuts; neither is claimed. There is no cost model in
this file, as in the parent module.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/-- Every element of a list with one index removed already occurs in the list. -/
private theorem mem_eraseIdx_subset {β : Type v} {l : List β} {i : Nat} {x : β}
    (h : x ∈ l.eraseIdx i) : x ∈ l := by
  induction l generalizing i with
  | nil => exact h
  | cons a l ih =>
      cases i with
      | zero => exact List.mem_cons_of_mem a h
      | succ i =>
          have herase : (a :: l).eraseIdx (i + 1) = a :: l.eraseIdx i := rfl
          rw [herase, List.mem_cons] at h
          rcases h with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (ih h)

/-- Every element of a list with one index replaced is the replacement or already
occurs in the list. -/
private theorem mem_set_cases {β : Type v} {l : List β} {i : Nat} {y x : β}
    (h : x ∈ l.set i y) : x = y ∨ x ∈ l := by
  induction l generalizing i with
  | nil => exact Or.inr h
  | cons a l ih =>
      cases i with
      | zero =>
          have hx : x ∈ y :: l := h
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem a hx)
      | succ i =>
          have hset : (a :: l).set (i + 1) y = a :: l.set i y := rfl
          rw [hset, List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inr List.mem_cons_self
          · rcases ih h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem a h)

/-- The sum of mapped multisets splits off the contribution of one index. -/
private theorem sum_map_eraseIdx {α : Type u} {β : Type v} (f : β → Multiset α)
    {l : List β} {i : Nat} {x : β} (h : l[i]? = some x) :
    (l.map f).sum = f x + ((l.eraseIdx i).map f).sum := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
      cases i with
      | zero =>
          have hax : a = x := by simpa using h
          subst hax
          rfl
      | succ i =>
          have h' : l[i]? = some x := h
          have herase : (a :: l).eraseIdx (i + 1) = a :: l.eraseIdx i := rfl
          rw [herase]
          simp only [List.map_cons, List.sum_cons]
          rw [ih h', ← Multiset.add_assoc (f a) (f x), Multiset.add_comm (f a) (f x),
            Multiset.add_assoc]

/-- The sum of mapped multisets over a list with one index replaced splits off the
replacement's contribution against the erased list. -/
private theorem sum_map_set {α : Type u} {β : Type v} (f : β → Multiset α)
    {l : List β} {i : Nat} {x : β} (h : l[i]? = some x) (y : β) :
    ((l.set i y).map f).sum = f y + ((l.eraseIdx i).map f).sum := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have h' : l[i]? = some x := h
          have hset : (a :: l).set (i + 1) y = a :: l.set i y := rfl
          have herase : (a :: l).eraseIdx (i + 1) = a :: l.eraseIdx i := rfl
          rw [hset, herase]
          simp only [List.map_cons, List.sum_cons]
          rw [ih h', ← Multiset.add_assoc (f a) (f y), Multiset.add_comm (f a) (f y),
            Multiset.add_assoc]

namespace FibonacciTree

variable {α : Type u}

/-- The subtree at a path of child indices from the root, or `none` when the path
leaves the tree. The empty path addresses the whole tree. -/
@[expose] public def subtreeAt : List Nat → FibonacciTree α → Option (FibonacciTree α)
  | [], t => some t
  | i :: p, .node _ _ children => (children[i]?).bind (subtreeAt p)

@[simp] public theorem subtreeAt_nil (t : FibonacciTree α) : subtreeAt [] t = some t := rfl

public theorem subtreeAt_cons (i : Nat) (p : List Nat) (d : Nat) (r : α)
    (cs : List (FibonacciTree α)) :
    subtreeAt (i :: p) (.node d r cs) = (cs[i]?).bind (subtreeAt p) := rfl

/-- Cut out the subtree at a path: returns the extracted subtree together with the
remainder of the tree with ancestors rebuilt and degrees corrected. The remainder is
`none` exactly for the empty path, where the whole tree is extracted. -/
@[expose] public def cutAt : List Nat → FibonacciTree α →
    Option (FibonacciTree α × Option (FibonacciTree α))
  | [], t => some (t, none)
  | i :: p, .node _ root children =>
      match children[i]? with
      | none => none
      | some child =>
          match cutAt p child with
          | none => none
          | some (sub, none) =>
              some (sub, some (.node (children.eraseIdx i).length root
                (children.eraseIdx i)))
          | some (sub, some child') =>
              some (sub, some (.node (children.set i child').length root
                (children.set i child')))

@[simp] public theorem cutAt_nil (t : FibonacciTree α) : cutAt [] t = some (t, none) := rfl

/-- Replace the root value of a tree, keeping its degree and children. Used on an
extracted subtree with a key no larger than the old root. -/
@[expose] public def decreaseRoot (t : FibonacciTree α) (newKey : α) : FibonacciTree α :=
  match t with
  | .node degree _ children => .node degree newKey children

@[simp] public theorem root_decreaseRoot (t : FibonacciTree α) (newKey : α) :
    (t.decreaseRoot newKey).root = newKey := by
  cases t
  rfl

/-- Decreasing a root replaces one occurrence of the old root in the represented
multiset by the new key. -/
public theorem elements_decreaseRoot [DecidableEq α] (t : FibonacciTree α) (newKey : α) :
    (t.decreaseRoot newKey).elements = newKey ::ₘ t.elements.erase t.root := by
  cases t with
  | node d r cs => simp [decreaseRoot, elements, root]

/-- Lowering the root of a valid tree to a key no larger than the old root keeps the
tree valid: the new root is still no greater than every represented element. -/
public theorem Valid.decreaseRoot [Preorder α] {t : FibonacciTree α} (hv : Valid t)
    {newKey : α} (hle : newKey ≤ t.root) : Valid (t.decreaseRoot newKey) := by
  cases t with
  | node d r cs =>
      have hle' : newKey ≤ r := hle
      refine Valid.node (fun c hc => hv.child_valid hc) hv.degree_eq ?_
      intro v hv_mem
      simp only [elements] at hv_mem
      rcases Multiset.mem_cons.mp hv_mem with rfl | hv_mem
      · exact le_rfl
      · apply hle'.trans
        apply hv.root_le
        simp only [elements]
        exact Multiset.mem_cons_of_mem hv_mem

/-- Every subtree addressed by a path in a valid tree is valid. -/
public theorem Valid.subtreeAt [LE α] {t sub : FibonacciTree α} (hv : Valid t)
    {p : List Nat} (h : subtreeAt p t = some sub) : Valid sub := by
  induction p generalizing t with
  | nil =>
      simp only [subtreeAt_nil, Option.some.injEq] at h
      exact h ▸ hv
  | cons i p ih =>
      cases t with
      | node d r cs =>
          rw [subtreeAt_cons] at h
          cases hchild : cs[i]? with
          | none =>
              rw [hchild] at h
              simp at h
          | some child =>
              rw [hchild, Option.bind_some] at h
              exact ih (hv.child_valid (List.mem_of_getElem? hchild)) h

/-- Cutting at a path extracts exactly the subtree that the path addresses. -/
public theorem cutAt_subtreeAt {p : List Nat} {t sub : FibonacciTree α}
    {rem : Option (FibonacciTree α)} (h : cutAt p t = some (sub, rem)) :
    subtreeAt p t = some sub := by
  induction p generalizing t sub rem with
  | nil =>
      simp only [cutAt_nil, Option.some.injEq, Prod.mk.injEq] at h
      rw [subtreeAt_nil, h.1]
  | cons i p ih =>
      cases t with
      | node d r cs =>
          cases hchild : cs[i]? with
          | none => simp [cutAt, hchild] at h
          | some child =>
              cases hcut : cutAt p child with
              | none => simp [cutAt, hchild, hcut] at h
              | some result =>
                  rcases result with ⟨sub', rem'⟩
                  have hsub : sub' = sub := by
                    cases rem' <;>
                      simp only [cutAt, hchild, hcut, Option.some.injEq,
                        Prod.mk.injEq] at h
                    · exact h.1
                    · exact h.1
                  rw [subtreeAt_cons, hchild, Option.bind_some]
                  exact hsub ▸ ih hcut

/-- Every addressed subtree can be cut out. -/
public theorem subtreeAt_cutAt {p : List Nat} {t sub : FibonacciTree α}
    (h : subtreeAt p t = some sub) : ∃ rem, cutAt p t = some (sub, rem) := by
  induction p generalizing t with
  | nil =>
      simp only [subtreeAt_nil, Option.some.injEq] at h
      exact ⟨none, by rw [cutAt_nil, h]⟩
  | cons i p ih =>
      cases t with
      | node d r cs =>
          rw [subtreeAt_cons] at h
          cases hchild : cs[i]? with
          | none =>
              rw [hchild] at h
              simp at h
          | some child =>
              rw [hchild, Option.bind_some] at h
              obtain ⟨rem, hcut⟩ := ih h
              cases rem with
              | none =>
                  exact ⟨some (.node (cs.eraseIdx i).length r (cs.eraseIdx i)),
                    by simp [cutAt, hchild, hcut]⟩
              | some child' =>
                  exact ⟨some (.node (cs.set i child').length r (cs.set i child')),
                    by simp [cutAt, hchild, hcut]⟩

/-- A cut with no remainder extracted the whole tree. -/
public theorem cutAt_eq_self {p : List Nat} {t sub : FibonacciTree α}
    (h : cutAt p t = some (sub, none)) : sub = t := by
  induction p generalizing t with
  | nil =>
      simp only [cutAt_nil, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | cons i p ih =>
      cases t with
      | node d r cs =>
          cases hchild : cs[i]? with
          | none => simp [cutAt, hchild] at h
          | some child =>
              cases hcut : cutAt p child with
              | none => simp [cutAt, hchild, hcut] at h
              | some result =>
                  rcases result with ⟨sub', rem'⟩
                  cases rem' <;> simp [cutAt, hchild, hcut] at h

/-- Cutting partitions the represented multiset into the remainder and the extracted
subtree. -/
public theorem cutAt_elements {p : List Nat} {t sub t' : FibonacciTree α}
    (h : cutAt p t = some (sub, some t')) :
    t.elements = t'.elements + sub.elements := by
  induction p generalizing t t' with
  | nil => simp [cutAt_nil] at h
  | cons i p ih =>
      cases t with
      | node d r cs =>
          cases hchild : cs[i]? with
          | none => simp [cutAt, hchild] at h
          | some child =>
              cases hcut : cutAt p child with
              | none => simp [cutAt, hchild, hcut] at h
              | some result =>
                  rcases result with ⟨sub', rem'⟩
                  cases rem' with
                  | none =>
                      have hsub : sub' = child := cutAt_eq_self hcut
                      simp only [cutAt, hchild, hcut, Option.some.injEq,
                        Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      simp only [elements]
                      rw [sum_map_eraseIdx elements hchild, ← hsub, Multiset.cons_add,
                        Multiset.add_comm sub'.elements]
                  | some child' =>
                      simp only [cutAt, hchild, hcut, Option.some.injEq,
                        Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hih := ih hcut
                      simp only [elements]
                      rw [sum_map_eraseIdx elements hchild,
                        sum_map_set elements hchild child', hih, Multiset.cons_add]
                      congr 1
                      rw [Multiset.add_assoc, Multiset.add_comm sub'.elements,
                        ← Multiset.add_assoc]

/-- The subtree extracted by a cut from a valid tree is valid. -/
public theorem cutAt_sub_valid [LE α] {p : List Nat} {t sub : FibonacciTree α}
    {rem : Option (FibonacciTree α)} (hv : Valid t)
    (h : cutAt p t = some (sub, rem)) : Valid sub :=
  hv.subtreeAt (cutAt_subtreeAt h)

/-- The remainder left by a cut from a valid tree is valid: its children are valid,
its stored degree is corrected, and its root still bounds every remaining element. -/
public theorem cutAt_remainder_valid [LE α] {p : List Nat} {t sub t' : FibonacciTree α}
    (hv : Valid t) (h : cutAt p t = some (sub, some t')) : Valid t' := by
  induction p generalizing t t' with
  | nil => simp [cutAt_nil] at h
  | cons i p ih =>
      cases t with
      | node d r cs =>
          cases hchild : cs[i]? with
          | none => simp [cutAt, hchild] at h
          | some child =>
              have hchildValid : Valid child :=
                hv.child_valid (List.mem_of_getElem? hchild)
              cases hcut : cutAt p child with
              | none => simp [cutAt, hchild, hcut] at h
              | some result =>
                  rcases result with ⟨sub', rem'⟩
                  have hElem : (FibonacciTree.node d r cs).elements =
                      t'.elements + sub.elements := cutAt_elements h
                  cases rem' with
                  | none =>
                      simp only [cutAt, hchild, hcut, Option.some.injEq,
                        Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      refine Valid.node (fun c hc =>
                        hv.child_valid (mem_eraseIdx_subset hc)) rfl ?_
                      intro v hv_mem
                      exact hv.root_le (hElem.symm ▸
                        Multiset.mem_add.mpr (Or.inl hv_mem))
                  | some child' =>
                      simp only [cutAt, hchild, hcut, Option.some.injEq,
                        Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hchild'Valid : Valid child' := ih hchildValid hcut
                      refine Valid.node ?_ rfl ?_
                      · intro c hc
                        rcases mem_set_cases hc with rfl | hc
                        · exact hchild'Valid
                        · exact hv.child_valid hc
                      · intro v hv_mem
                        exact hv.root_le (hElem.symm ▸
                          Multiset.mem_add.mpr (Or.inl hv_mem))

end FibonacciTree

namespace FibonacciForest

variable {α : Type u}

/-- Cut the subtree at path `p` inside the `i`-th tree of a forest: returns the
extracted subtree together with the forest in which that tree is replaced by the cut
remainder (or removed when the whole tree was extracted). -/
@[expose] public def cutTreeAt (trees : List (FibonacciTree α)) (i : Nat) (p : List Nat) :
    Option (FibonacciTree α × List (FibonacciTree α)) :=
  match trees[i]? with
  | none => none
  | some t =>
      match t.cutAt p with
      | none => none
      | some (sub, none) => some (sub, trees.eraseIdx i)
      | some (sub, some t') => some (sub, trees.set i t')

/-- Cutting a subtree out of a forest partitions the represented multiset into the
remaining forest and the extracted subtree. -/
public theorem cutTreeAt_elements {trees : List (FibonacciTree α)} {i : Nat} {p : List Nat}
    {sub : FibonacciTree α} {rest : List (FibonacciTree α)}
    (h : cutTreeAt trees i p = some (sub, rest)) :
    elements trees = elements rest + sub.elements := by
  cases htree : trees[i]? with
  | none => simp [cutTreeAt, htree] at h
  | some t =>
      cases hcut : t.cutAt p with
      | none => simp [cutTreeAt, htree, hcut] at h
      | some result =>
          rcases result with ⟨sub', rem'⟩
          cases rem' with
          | none =>
              have hsub : sub' = t := FibonacciTree.cutAt_eq_self hcut
              simp only [cutTreeAt, htree, hcut, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              change (trees.map FibonacciTree.elements).sum =
                ((trees.eraseIdx i).map FibonacciTree.elements).sum + sub'.elements
              rw [sum_map_eraseIdx FibonacciTree.elements htree, ← hsub,
                Multiset.add_comm]
          | some t' =>
              simp only [cutTreeAt, htree, hcut, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hCutElem := FibonacciTree.cutAt_elements hcut
              change (trees.map FibonacciTree.elements).sum =
                ((trees.set i t').map FibonacciTree.elements).sum + sub'.elements
              rw [sum_map_eraseIdx FibonacciTree.elements htree,
                sum_map_set FibonacciTree.elements htree t', hCutElem,
                Multiset.add_assoc, Multiset.add_comm sub'.elements,
                ← Multiset.add_assoc]

/-- Both parts of a forest cut from a valid forest are valid. -/
public theorem cutTreeAt_valid [LE α] {trees : List (FibonacciTree α)} {i : Nat}
    {p : List Nat} {sub : FibonacciTree α} {rest : List (FibonacciTree α)}
    (hv : Valid trees) (h : cutTreeAt trees i p = some (sub, rest)) :
    sub.Valid ∧ Valid rest := by
  cases htree : trees[i]? with
  | none => simp [cutTreeAt, htree] at h
  | some t =>
      have htValid : t.Valid := hv t (List.mem_of_getElem? htree)
      cases hcut : t.cutAt p with
      | none => simp [cutTreeAt, htree, hcut] at h
      | some result =>
          rcases result with ⟨sub', rem'⟩
          have hsubValid : sub'.Valid := FibonacciTree.cutAt_sub_valid htValid hcut
          cases rem' with
          | none =>
              simp only [cutTreeAt, htree, hcut, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hsubValid, fun c hc => hv c (mem_eraseIdx_subset hc)⟩
          | some t' =>
              simp only [cutTreeAt, htree, hcut, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ht'Valid : t'.Valid :=
                FibonacciTree.cutAt_remainder_valid htValid hcut
              refine ⟨hsubValid, fun c hc => ?_⟩
              rcases mem_set_cases hc with rfl | hc
              · exact ht'Valid
              · exact hv c hc

/-- A subtree addressed by an index into the root list and a path inside that tree can
be cut out of the forest. -/
public theorem cutTreeAt_of_subtreeAt {trees : List (FibonacciTree α)} {i : Nat}
    {p : List Nat} {t sub : FibonacciTree α} (htree : trees[i]? = some t)
    (hpath : t.subtreeAt p = some sub) :
    ∃ rest, cutTreeAt trees i p = some (sub, rest) := by
  obtain ⟨rem, hcut⟩ := FibonacciTree.subtreeAt_cutAt hpath
  cases rem with
  | none => exact ⟨trees.eraseIdx i, by simp [cutTreeAt, htree, hcut]⟩
  | some t' => exact ⟨trees.set i t', by simp [cutTreeAt, htree, hcut]⟩

end FibonacciForest

namespace FibonacciHeap

variable {α : Type u}

/-- In a valid forest, a represented element that is no greater than every
represented element is the minimum root. -/
private theorem minRoot_eq_some_of_least [LinearOrder α]
    {trees : List (FibonacciTree α)} (hv : FibonacciForest.Valid trees) {x : α}
    (hx : x ∈ FibonacciForest.elements trees)
    (hle : ∀ y ∈ FibonacciForest.elements trees, x ≤ y) :
    FibonacciForest.minRoot trees = some x := by
  have hne : trees ≠ [] := by
    rintro rfl
    simp [FibonacciForest.elements] at hx
  cases hmr : FibonacciForest.minRoot trees with
  | none => exact absurd ((FibonacciForest.minRoot_eq_none_iff trees).mp hmr) hne
  | some x' =>
      let heap : FibonacciHeap α := ⟨trees, some x', hv, hmr.symm⟩
      have hfind : heap.findMin = some x' := rfl
      have hx' : x' ∈ FibonacciForest.elements trees := findMin_mem hfind
      have h1 : x ≤ x' := hle x' hx'
      have h2 : x' ≤ x := findMin_le hfind hx
      exact congrArg some (le_antisymm h2 h1)

/-- Decrease the key of the node addressed by root index `i` and path `p` to
`newKey`: cut the addressed subtree out of its tree, lower its root, and put it back
as a new tree in the root list. The cached minimum of the result is the smaller of
`newKey` and the previous cached minimum, computed without rescanning the root
list. When the address does not resolve or `newKey` is larger than the addressed
root (so the operation would be an increase), the heap is returned unchanged.
Unlike CLRS decrease-key this performs no cascading cuts: the trees carry no mark
field (see the module documentation). -/
public def decreaseKey [LinearOrder α] (heap : FibonacciHeap α) (i : Nat) (p : List Nat)
    (newKey : α) : FibonacciHeap α :=
  match found : FibonacciForest.cutTreeAt heap.trees i p with
  | none => heap
  | some (sub, rest) =>
      if hle : newKey ≤ sub.root then
        have hv := FibonacciForest.cutTreeAt_valid heap.valid found
        let trees := sub.decreaseRoot newKey :: rest
        have trees_valid : FibonacciForest.Valid trees := by
          intro t ht
          have ht' : t ∈ sub.decreaseRoot newKey :: rest := ht
          rw [List.mem_cons] at ht'
          rcases ht' with rfl | ht'
          · exact hv.1.decreaseRoot hle
          · exact hv.2 t ht'
        let newMin : Option α := match heap.cachedMin with
          | none => some newKey
          | some m => some (min newKey m)
        have hmin : newMin = FibonacciForest.minRoot trees := by
          have hElemTrees : FibonacciForest.elements trees =
              newKey ::ₘ (FibonacciForest.elements heap.trees).erase sub.root := by
            have hElem := FibonacciForest.cutTreeAt_elements found
            show FibonacciForest.elements (sub.decreaseRoot newKey :: rest) = _
            rw [hElem,
              Multiset.erase_add_right_pos _ (FibonacciTree.root_mem_elements sub)]
            change (sub.decreaseRoot newKey).elements +
                FibonacciForest.elements rest = _
            rw [FibonacciTree.elements_decreaseRoot, Multiset.cons_add,
              Multiset.add_comm (sub.elements.erase sub.root)]
          cases hc : heap.cachedMin with
          | none =>
              exfalso
              have hfind : heap.findMin = none := hc
              have htrees : heap.trees = [] := (findMin_eq_none_iff heap).mp hfind
              rw [htrees] at found
              simp [FibonacciForest.cutTreeAt] at found
          | some m =>
              have hnew : newMin = some (min newKey m) := by
                show (match heap.cachedMin with
                  | none => some newKey
                  | some m' => some (min newKey m')) = some (min newKey m)
                rw [hc]
              have hfind : heap.findMin = some m := hc
              have hmMem : m ∈ heap.elements := findMin_mem hfind
              change m ∈ FibonacciForest.elements heap.trees at hmMem
              have hmem : min newKey m ∈ FibonacciForest.elements trees := by
                by_cases hm : m = sub.root
                · have hmin' : min newKey m = newKey :=
                    min_eq_left (hm ▸ hle)
                  rw [hElemTrees, hmin']
                  exact Multiset.mem_cons_self _ _
                · rw [hElemTrees]
                  rcases le_total newKey m with hnm | hnm
                  · rw [min_eq_left hnm]
                    exact Multiset.mem_cons_self _ _
                  · rw [min_eq_right hnm]
                    exact Multiset.mem_cons_of_mem
                      ((Multiset.mem_erase_of_ne hm).mpr hmMem)
              have hleast : ∀ y ∈ FibonacciForest.elements trees,
                  min newKey m ≤ y := by
                intro y hy
                rw [hElemTrees] at hy
                rcases Multiset.mem_cons.mp hy with rfl | hy
                · exact min_le_left _ _
                · exact (min_le_right newKey m).trans
                    (findMin_le hfind (Multiset.mem_of_mem_erase hy))
              rw [hnew]
              exact (minRoot_eq_some_of_least trees_valid hmem hleast).symm
        ⟨trees, newMin, trees_valid, hmin⟩
      else heap

/-- On a successful cut with a genuine decrease, the new root list is the decreased
subtree in front of the cut remainder forest. -/
public theorem decreaseKey_trees_of_cut [LinearOrder α] {heap : FibonacciHeap α}
    {i : Nat} {p : List Nat} {newKey : α} {sub : FibonacciTree α}
    {rest : List (FibonacciTree α)}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = some (sub, rest))
    (hle : newKey ≤ sub.root) :
    (heap.decreaseKey i p newKey).trees = sub.decreaseRoot newKey :: rest := by
  unfold decreaseKey
  split
  · rename_i hnone
    rw [hcut] at hnone
    simp at hnone
  · rename_i sub' rest' hfound
    rw [hcut] at hfound
    simp only [Option.some.injEq, Prod.mk.injEq] at hfound
    obtain ⟨rfl, rfl⟩ := hfound
    rw [dite_eq_left hle]

/-- Decrease-key with an address that does not resolve is the identity. -/
public theorem decreaseKey_eq_self_of_cut_none [LinearOrder α] {heap : FibonacciHeap α}
    {i : Nat} {p : List Nat} {newKey : α}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = none) :
    heap.decreaseKey i p newKey = heap := by
  unfold decreaseKey
  split
  · rfl
  · rename_i sub' rest' hfound
    rw [hcut] at hfound
    simp at hfound

/-- Decrease-key with a key larger than the addressed root is the identity. -/
public theorem decreaseKey_eq_self_of_not_le [LinearOrder α] {heap : FibonacciHeap α}
    {i : Nat} {p : List Nat} {newKey : α} {sub : FibonacciTree α}
    {rest : List (FibonacciTree α)}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = some (sub, rest))
    (hle : ¬ newKey ≤ sub.root) :
    heap.decreaseKey i p newKey = heap := by
  unfold decreaseKey
  split
  · rfl
  · rename_i sub' rest' hfound
    rw [hcut] at hfound
    simp only [Option.some.injEq, Prod.mk.injEq] at hfound
    obtain ⟨rfl, rfl⟩ := hfound
    rw [dite_eq_right hle]

/-- A successful decrease-key replaces exactly one occurrence of the old key (the
addressed subtree's root) by the new key in the represented multiset. -/
public theorem decreaseKey_elements [LinearOrder α] {heap : FibonacciHeap α} {i : Nat}
    {p : List Nat} {newKey : α} {sub : FibonacciTree α} {rest : List (FibonacciTree α)}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = some (sub, rest))
    (hle : newKey ≤ sub.root) :
    (heap.decreaseKey i p newKey).elements =
      newKey ::ₘ heap.elements.erase sub.root := by
  have hTrees := decreaseKey_trees_of_cut hcut hle
  have hElem := FibonacciForest.cutTreeAt_elements hcut
  change FibonacciForest.elements (heap.decreaseKey i p newKey).trees =
    newKey ::ₘ (FibonacciForest.elements heap.trees).erase sub.root
  rw [hTrees, hElem,
    Multiset.erase_add_right_pos _ (FibonacciTree.root_mem_elements sub)]
  change (sub.decreaseRoot newKey).elements + FibonacciForest.elements rest = _
  rw [FibonacciTree.elements_decreaseRoot, Multiset.cons_add,
    Multiset.add_comm (sub.elements.erase sub.root)]

/-- `decreaseKey_elements` stated through the addressing view: the caller names the
root tree and the addressed subtree instead of the cut remainder. -/
public theorem decreaseKey_elements_of_subtreeAt [LinearOrder α]
    {heap : FibonacciHeap α} {i : Nat} {p : List Nat} {newKey : α}
    {t sub : FibonacciTree α} (htree : heap.trees[i]? = some t)
    (hpath : t.subtreeAt p = some sub) (hle : newKey ≤ sub.root) :
    (heap.decreaseKey i p newKey).elements =
      newKey ::ₘ heap.elements.erase sub.root := by
  obtain ⟨rest, hcut⟩ := FibonacciForest.cutTreeAt_of_subtreeAt htree hpath
  exact decreaseKey_elements hcut hle

/-- A successful decrease-key preserves the number of represented elements. -/
public theorem decreaseKey_card_elements [LinearOrder α] {heap : FibonacciHeap α}
    {i : Nat} {p : List Nat} {newKey : α} {sub : FibonacciTree α}
    {rest : List (FibonacciTree α)}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = some (sub, rest))
    (hle : newKey ≤ sub.root) :
    (heap.decreaseKey i p newKey).elements.card = heap.elements.card := by
  have hmem : sub.root ∈ heap.elements := by
    have hElem := FibonacciForest.cutTreeAt_elements hcut
    change sub.root ∈ FibonacciForest.elements heap.trees
    rw [hElem]
    exact Multiset.mem_add.mpr (Or.inr (FibonacciTree.root_mem_elements sub))
  have hne : heap.elements ≠ 0 := by
    intro h0
    rw [h0] at hmem
    simp at hmem
  have hpos : 0 < heap.elements.card := Multiset.card_pos.mpr hne
  have hcard : (heap.elements.erase sub.root).card + 1 = heap.elements.card := by
    rw [Multiset.card_erase_of_mem hmem]
    exact Nat.succ_pred_eq_of_pos hpos
  rw [decreaseKey_elements hcut hle, Multiset.card_cons]
  exact hcard

/-- After a successful decrease-key, minimum inspection returns the smaller of the
new key and the old minimum. -/
public theorem decreaseKey_findMin [LinearOrder α] {heap : FibonacciHeap α} {i : Nat}
    {p : List Nat} {newKey m : α} {sub : FibonacciTree α}
    {rest : List (FibonacciTree α)}
    (hcut : FibonacciForest.cutTreeAt heap.trees i p = some (sub, rest))
    (hle : newKey ≤ sub.root) (hmin : heap.findMin = some m) :
    (heap.decreaseKey i p newKey).findMin = some (min newKey m) := by
  have hElem := decreaseKey_elements hcut hle
  have hNewKeyMem : newKey ∈ (heap.decreaseKey i p newKey).elements :=
    hElem ▸ Multiset.mem_cons_self newKey _
  have hex : ∃ x, (heap.decreaseKey i p newKey).findMin = some x := by
    cases hfind : (heap.decreaseKey i p newKey).findMin with
    | some x => exact ⟨x, rfl⟩
    | none =>
        have hTrees := decreaseKey_trees_of_cut hcut hle
        have hempty : (heap.decreaseKey i p newKey).trees = [] :=
          (findMin_eq_none_iff _).mp hfind
        rw [hTrees] at hempty
        simp at hempty
  obtain ⟨x, hx⟩ := hex
  have hxMem : x ∈ (heap.decreaseKey i p newKey).elements := findMin_mem hx
  have hxLeNew : x ≤ newKey := findMin_le hx hNewKeyMem
  have hmMem : m ∈ heap.elements := findMin_mem hmin
  have hxLeM : x ≤ m := by
    by_cases hm : m = sub.root
    · exact hxLeNew.trans (by rw [hm]; exact hle)
    · have hmMem' : m ∈ (heap.decreaseKey i p newKey).elements := by
        rw [hElem]
        exact Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne hm).mpr hmMem)
      exact findMin_le hx hmMem'
  have hMinLeX : min newKey m ≤ x := by
    rw [hElem] at hxMem
    rcases Multiset.mem_cons.mp hxMem with rfl | hxMem
    · exact min_le_left _ _
    · exact (min_le_right newKey m).trans
        (findMin_le hmin (Multiset.mem_of_mem_erase hxMem))
  rw [hx]
  exact congrArg some (le_antisymm (le_min hxLeNew hxLeM) hMinLeX)

/-- The forest after decrease-key is valid: heap order is restored. This is the
validity field of the resulting heap, exposed as a theorem for convenience. -/
public theorem decreaseKey_valid [LinearOrder α] (heap : FibonacciHeap α) (i : Nat)
    (p : List Nat) (newKey : α) :
    FibonacciForest.Valid (heap.decreaseKey i p newKey).trees :=
  (heap.decreaseKey i p newKey).valid

end FibonacciHeap

end Cslib.Algorithms.Lean
