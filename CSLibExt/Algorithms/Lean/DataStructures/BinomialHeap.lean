/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.AddSub

/-!
# Binomial min-heaps

This module implements persistent binomial trees and forests. A valid tree of rank `r` has
children of ranks `r - 1, ..., 0`, contains exactly `2 ^ r` elements, and has a root no greater
than any represented element. A valid heap is a forest whose tree ranks are strictly increasing.

`BinomialTree.link` retains its left argument as parent when the roots compare equal. The same
left-biased policy is used when selecting the minimum tree.

The machine-checked results establish the rank, size, order, forest, and multiset invariants.
There is no formal cost model here. Under constant-time comparison and constructor assumptions,
`link` takes constant time; insertion and minimum inspection visit at most the number of roots
`k`; and the implementation gives conservative worst-case bounds `O((k₁ + k₂) ^ 2)` for
meld and `O(k + r + (k + r) ^ 2)` for deleting a tree of rank `r`. The proved powers-of-two tree
sizes and unique ranks give machine-checked binary-logarithm bounds on `k` and `r`.
These structural bounds are not theorems about running time in this module.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- **Binomial tree.** A binomial tree over a type $\alpha$ is a node that stores a rank, which is
a natural number, a root value in $\alpha$, and a list of binomial trees over $\alpha$ as its
children. The type imposes no invariant; the binomial-tree shape and heap order are expressed
by a separate validity predicate. -/
public inductive BinomialTree (α : Type u) where
  | node (rank : Nat) (root : α) (children : List (BinomialTree α))
deriving Repr

namespace BinomialTree

variable {α : Type u}

/-- **Rank of a binomial tree.** The rank of a binomial tree is the natural number stored at its
root node. -/
@[expose] public def rank {α : Type u} : BinomialTree α → Nat
  | .node rank _ _ => rank

/-- **Root of a binomial tree.** The root of the binomial tree with rank $r$, root value $a$ and
list of children $c$ is $a$. -/
@[expose] public def root {α : Type u} : BinomialTree α → α
  | .node _ root _ => root

/-- **Children of a binomial tree.** The children of a binomial tree are the binomial trees in
the list stored at its root node, in their stored order.

The list carries no ordering constraint in general; in a valid binomial tree of rank $r$ the
children have ranks $r - 1, \dots, 0$ in that order. -/
@[expose] public def children {α : Type u} : BinomialTree α → List (BinomialTree α)
  | .node _ _ children => children

/-- **Elements of a binomial tree.** The multiset of elements of a binomial tree with root value
$x$ and children $t_1, \dots, t_k$ is defined recursively as $\{x\}$ added to the multiset sum of
the multisets of elements of $t_1, \dots, t_k$; the stored rank plays no role. -/
@[expose] public def elements {α : Type u} : BinomialTree α → Multiset α
  | .node _ root children => root ::ₘ (children.map elements).sum

/-- **The root of a binomial tree is one of its elements.** For every binomial tree $t$, the root
of $t$ occurs in the multiset represented by $t$. -/
public theorem root_mem_elements (tree : BinomialTree α) : tree.root ∈ tree.elements := by
  cases tree
  simp [root, elements]

/-- **Valid binomial tree.** For a type $\alpha$ with a relation $\le$, validity of binomial
trees over $\alpha$ is defined inductively: the tree with stored rank $r$, root $a$ and list of
children $c_1, \dots, c_k$ is valid when every child $c_i$ is valid, the ranks of
$c_1, \dots, c_k$ are exactly $r - 1, r - 2, \dots, 0$ in this order, the multiset of elements
of the tree (its root together with the elements of all its children) has exactly $2^r$
members counted with multiplicity, and $a \le x$ for every element $x$ of the tree. -/
public inductive Valid {α : Type u} [LE α] : BinomialTree α → Prop
  | node {rank : Nat} {root : α} {children : List (BinomialTree α)}
      (children_valid : ∀ child ∈ children, Valid child)
      (children_ranks : children.map BinomialTree.rank = (List.range rank).reverse)
      (card_elements : (elements (.node rank root children)).card = 2 ^ rank)
      (root_le : ∀ value ∈ elements (.node rank root children), root ≤ value) :
      Valid (.node rank root children)

/-- **Singleton binomial heap.** For a value $a$ in a linear order, the binomial heap whose list of
trees consists of exactly one tree: the tree of rank $0$ with root $a$ and no children. -/
@[expose] public def singleton (value : α) : BinomialTree α :=
  .node 0 value []

/-- **Linking two binomial trees.** Over a linear order, the link of binomial trees $s$ and $t$
is defined as follows. If the root of $s$ is at most the root of $t$, it is the tree whose rank
is one more than the rank of $s$, whose root is the root of $s$, and whose children are $t$
followed by the children of $s$. Otherwise it is the tree whose rank is one more than the rank
of $s$, whose root is the root of $t$, and whose children are $s$ followed by the children of
$t$. In particular, the root of $s$ is kept when the two roots are equal. -/
@[expose] public def link [LinearOrder α] (left right : BinomialTree α) : BinomialTree α :=
  if left.root ≤ right.root then
    .node (left.rank + 1) left.root (right :: left.children)
  else
    .node (left.rank + 1) right.root (left :: right.children)

@[simp] public theorem rank_singleton (value : α) : (singleton value).rank = 0 := by
  rfl

@[simp] public theorem root_singleton (value : α) : (singleton value).root = value := by
  rfl

@[simp] public theorem children_singleton (value : α) :
    (singleton value).children = [] := by
  rfl

@[simp] public theorem elements_singleton (value : α) :
    (singleton value).elements = {value} := by
  simp [singleton, elements]

@[simp] public theorem rank_link [LinearOrder α] (left right : BinomialTree α) :
    (link left right).rank = left.rank + 1 := by
  rw [link]
  split <;> rfl

/-- **Linking binomial trees adds their elements.** For any two binomial trees $s$ and $t$ over a
linearly ordered type, the multiset of elements of the tree obtained by linking $s$ and $t$ is
the sum of the multisets of elements of $s$ and $t$. -/
public theorem elements_link [LinearOrder α] (left right : BinomialTree α) :
    (link left right).elements = left.elements + right.elements := by
  rw [link]
  split
  · cases left
    cases right
    simp only [root, rank, children, elements, List.map_cons, List.sum_cons]
    rw [Multiset.cons_add, Multiset.add_cons, Multiset.add_comm]
    simpa only [Multiset.cons_add] using Multiset.cons_swap _ _ _
  · cases left
    cases right
    simp only [root, rank, children, elements, List.map_cons, List.sum_cons]
    rw [Multiset.cons_add, Multiset.add_cons]
    simp only [Multiset.cons_add, Multiset.cons_swap]

/-- **Singleton binomial trees are valid.** For a linearly ordered type $\alpha$ and any
$a \in \alpha$, the singleton binomial tree with rank $0$, root $a$ and no children is valid. -/
public theorem valid_singleton [LinearOrder α] (value : α) : Valid (singleton value) := by
  constructor
  · simp
  · rfl
  · simp [elements]
  · simp [elements]

/-- **Children of a valid binomial tree are valid.** For a type $\alpha$ with a relation $\le$,
every child of a valid binomial tree over $\alpha$ is itself a valid binomial tree. -/
public theorem Valid.child_valid [LE α] {tree child : BinomialTree α}
    (valid : Valid tree) (member : child ∈ tree.children) : Valid child := by
  cases valid with
  | node children_valid _ _ _ => exact children_valid child member

/-- **Child ranks of a valid binomial tree.** For a type $\alpha$ with a relation $\le$, if a
valid binomial tree over $\alpha$ has rank $r$, then the ranks of its children, listed in their
stored order, are $r - 1, r - 2, \dots, 1, 0$; there are no children when $r = 0$. -/
public theorem Valid.children_ranks [LE α] {tree : BinomialTree α} (valid : Valid tree) :
    tree.children.map BinomialTree.rank = (List.range tree.rank).reverse := by
  cases valid with
  | node _ children_ranks _ _ => exact children_ranks

/-- **Size of a valid binomial tree.** For a type $\alpha$ with a relation $\le$, every valid
binomial tree of rank $r$ over $\alpha$ represents a multiset of exactly $2^r$ elements, counted
with multiplicity. -/
public theorem Valid.card_elements [LE α] {tree : BinomialTree α} (valid : Valid tree) :
    tree.elements.card = 2 ^ tree.rank := by
  cases valid with
  | node _ _ card_elements _ => exact card_elements

/-- **The rank of a valid binomial tree is logarithmic.** A valid binomial tree of rank $r$
holding $n$ elements, counted with multiplicity, satisfies $r \le \lfloor \log_2 n \rfloor$. -/
public theorem Valid.rank_le_log2_card [LE α] {tree : BinomialTree α} (valid : Valid tree) :
    tree.rank ≤ Nat.log2 tree.elements.card := by
  simpa only [valid.card_elements, Nat.log2_two_pow] using (le_rfl : tree.rank ≤ tree.rank)

/-- **The root of a valid binomial tree is a lower bound.** For a type $\alpha$ with a relation
$\le$ and a valid binomial tree $t$ over $\alpha$, the root $a$ of $t$ satisfies $a \le v$ for
every element $v$ of the multiset represented by $t$. -/
public theorem Valid.root_le [LE α] {tree : BinomialTree α} (valid : Valid tree)
    {value : α} (member : value ∈ tree.elements) : tree.root ≤ value := by
  cases valid with
  | node _ _ _ root_le => exact root_le value member

/-- **Linking preserves binomial-tree validity.** If $s$ and $t$ are valid binomial trees
of equal rank, then the tree obtained by linking $s$ with $t$ is valid. -/
public theorem Valid.link [LinearOrder α] {left right : BinomialTree α}
    (left_valid : Valid left) (right_valid : Valid right)
    (ranks : left.rank = right.rank) : Valid (link left right) := by
  rw [BinomialTree.link]
  split
  · rename_i root_le
    constructor
    · intro child member
      simp only [children, List.mem_cons] at member
      rcases member with rfl | member
      · exact right_valid
      · exact left_valid.child_valid member
    · simp only [children, rank, List.map_cons, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.cons.injEq]
      exact ⟨ranks.symm, left_valid.children_ranks⟩
    · have element_eq :
          (BinomialTree.node (left.rank + 1) left.root
            (right :: left.children)).elements = left.elements + right.elements := by
          simpa [BinomialTree.link, root_le] using elements_link left right
      rw [element_eq, Multiset.card_add, left_valid.card_elements,
        right_valid.card_elements, ← ranks, Nat.two_pow_succ]
    · intro value member
      have union_member : value ∈ left.elements + right.elements := by
        rw [← elements_link left right]
        simpa [BinomialTree.link, root_le] using member
      rcases Multiset.mem_add.mp union_member with member | member
      · exact left_valid.root_le member
      · exact root_le.trans (right_valid.root_le member)
  · rename_i not_le
    have root_le : right.root ≤ left.root := le_of_not_ge not_le
    constructor
    · intro child member
      simp only [children, List.mem_cons] at member
      rcases member with rfl | member
      · exact left_valid
      · exact right_valid.child_valid member
    · simp only [children, rank, List.map_cons, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.cons.injEq]
      constructor
      · trivial
      · change right.children.map BinomialTree.rank =
          (List.range left.rank).reverse
        rw [right_valid.children_ranks]
        exact congrArg (fun rank => (List.range rank).reverse) ranks.symm
    · have element_eq :
          (BinomialTree.node (left.rank + 1) right.root
            (left :: right.children)).elements = left.elements + right.elements := by
          simpa [BinomialTree.link, not_le] using elements_link left right
      rw [element_eq, Multiset.card_add, left_valid.card_elements,
        right_valid.card_elements, ← ranks, Nat.two_pow_succ]
    · intro value member
      have union_member : value ∈ left.elements + right.elements := by
        rw [← elements_link left right]
        simpa [BinomialTree.link, not_le] using member
      rcases Multiset.mem_add.mp union_member with member | member
      · exact root_le.trans (left_valid.root_le member)
      · exact right_valid.root_le member

end BinomialTree

/-- **Valid binomial forest.** For a type $\alpha$ with a relation $\le$, a list of binomial trees
over $\alpha$ is a valid forest when every tree in it is a valid binomial tree and the ranks of its
trees are strictly increasing along the list. -/
@[expose] public def BinomialForest.Valid {α : Type u} [LE α]
    (trees : List (BinomialTree α)) : Prop :=
  (∀ tree ∈ trees, tree.Valid) ∧
    (trees.map BinomialTree.rank).Pairwise (· < ·)

namespace BinomialForest

variable {α : Type u}

/-- **Elements of a binomial forest.** The multiset of elements of a list of binomial trees
$t_1, \dots, t_k$ is the multiset sum of the multisets of elements of $t_1, \dots, t_k$; for the
empty list it is the empty multiset. -/
@[expose] public def elements {α : Type u} (trees : List (BinomialTree α)) : Multiset α :=
  (trees.map BinomialTree.elements).sum

private lemma card_elements_le_card {trees : List (BinomialTree α)} {tree : BinomialTree α}
    (member : tree ∈ trees) : tree.elements.card ≤ (elements trees).card := by
  induction trees with
  | nil => simp at member
  | cons head tail ih =>
    change tree.elements.card ≤ (head.elements + elements tail).card
    rw [Multiset.card_add]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have card_le := ih member
      omega

private theorem mem_elements_iff {trees : List (BinomialTree α)} {value : α} :
    value ∈ elements trees ↔ ∃ tree ∈ trees, value ∈ tree.elements := by
  induction trees with
  | nil => simp [elements]
  | cons tree trees ih =>
      change value ∈ tree.elements + elements trees ↔
        ∃ current ∈ tree :: trees, value ∈ current.elements
      rw [Multiset.mem_add, ih]
      simp

/-- **Rank lower bound for a forest.** For a natural number $r$, a list of binomial trees has
ranks at least $r$ when every tree in it has rank at least $r$. -/
public def RanksAtLeast {α : Type u} (rank : Nat)
    (trees : List (BinomialTree α)) : Prop :=
  ∀ tree ∈ trees, rank ≤ tree.rank

/-- **The empty forest is valid.** For every type $\alpha$ with a relation $\le$, the empty list of
binomial trees over $\alpha$ is a valid binomial forest. -/
public theorem valid_nil [LE α] : Valid ([] : List (BinomialTree α)) := by
  simp [Valid]

private theorem Valid.head_valid [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (valid : Valid (tree :: trees)) : tree.Valid := by
  exact valid.1 tree (by simp)

private theorem Valid.tail [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (valid : Valid (tree :: trees)) : Valid trees := by
  constructor
  · intro current member
    exact valid.1 current (by simp [member])
  · simpa [List.pairwise_map] using valid.2.tail

private theorem Valid.head_lt [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (valid : Valid (tree :: trees))
    {other : BinomialTree α} (member : other ∈ trees) : tree.rank < other.rank := by
  rw [Valid, List.map_cons, List.pairwise_cons] at valid
  exact valid.2.1 other.rank (List.mem_map.mpr ⟨other, member, rfl⟩)

theorem valid_cons [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (tree_valid : tree.Valid) (trees_valid : Valid trees)
    (rank_lt : ∀ other ∈ trees, tree.rank < other.rank) : Valid (tree :: trees) := by
  rw [Valid, List.map_cons, List.pairwise_cons]
  constructor
  · intro current member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact tree_valid
    · exact trees_valid.1 current member
  · refine ⟨?_, trees_valid.2⟩
    intro rank member
    rcases List.mem_map.mp member with ⟨other, other_mem, rfl⟩
    exact rank_lt other other_mem

/-- **Validity of binomial forests passes to sublists.** For a type $\alpha$ with a relation $\le$
and lists $L$, $R$ of binomial trees over $\alpha$, if $L$ is a sublist of $R$ (obtained by
deleting entries while keeping the order of the rest) and $R$ is a valid forest, then $L$ is a valid
forest. -/
public theorem Valid.sublist [LE α] {left right : List (BinomialTree α)}
    (sublist : left.Sublist right) (valid : Valid right) : Valid left := by
  constructor
  · intro tree member
    exact valid.1 tree (sublist.subset member)
  · exact valid.2.sublist (sublist.map BinomialTree.rank)

/-- **Tree ranks in a valid forest are logarithmic.** If $F$ is a valid binomial forest and $T$
is a tree of $F$ of rank $r$, then $r \le \lfloor \log_2 n \rfloor$, where $n$ is the number of
elements, counted with multiplicity, represented by $F$. -/
public theorem Valid.member_rank_le_log2_card [LE α] {trees : List (BinomialTree α)}
    {tree : BinomialTree α} (valid : Valid trees) (member : tree ∈ trees) :
    tree.rank ≤ Nat.log2 (elements trees).card := by
  have card_le := card_elements_le_card member
  have card_pos : 0 < tree.elements.card := by
    cases tree
    simp [BinomialTree.elements]
  apply (Nat.le_log2 (by omega)).mpr
  rw [← (valid.1 tree member).card_elements]
  exact card_le

/-- **A valid binomial forest has logarithmically many trees.** Let $\alpha$ be a type with a
relation $\le$. If a valid binomial forest over $\alpha$ has $n$ elements, counted with
multiplicity, then it consists of at most $\lfloor \log_2 n \rfloor + 1$ trees, where
$\lfloor \log_2 0 \rfloor$ is taken to be $0$. -/
public theorem Valid.length_le_log2_card_succ [LE α] {trees : List (BinomialTree α)}
    (valid : Valid trees) : trees.length ≤ Nat.log2 (elements trees).card + 1 := by
  have subset : trees.map BinomialTree.rank ⊆ List.range (Nat.log2 (elements trees).card + 1) := by
    intro rank member
    rcases List.mem_map.mp member with ⟨tree, tree_member, rfl⟩
    have rank_le := valid.member_rank_le_log2_card tree_member
    have rank_lt : tree.rank < Nat.log2 (elements trees).card + 1 := by omega
    simpa using rank_lt
  simpa using valid.2.nodup.length_le_of_subset subset

/-- **A valid binomial forest with no elements has no trees.** Let $\alpha$ be a type with a
relation $\le$. If a list of binomial trees over $\alpha$ is a valid binomial forest and its
multiset of elements has cardinality $0$, then the list has length $0$. -/
public theorem Valid.length_eq_zero_of_card_eq_zero [LE α] {trees : List (BinomialTree α)}
    (valid : Valid trees) (empty : (elements trees).card = 0) : trees.length = 0 := by
  cases trees with
  | nil => rfl
  | cons tree trees =>
    have tree_valid := valid.1 tree (by simp)
    have card_le := card_elements_le_card (show tree ∈ tree :: trees by simp)
    rw [tree_valid.card_elements, empty] at card_le
    simp at card_le

/-- **Carry insertion into a binomial forest.** For a linearly ordered type, the carry of a
binomial tree $t$ into a list $F$ of binomial trees is defined by recursion on $F$. If $F$ is
empty, the result is the one-tree list $[t]$. If $F$ starts with a tree $u$ followed by a list
$F'$ and the rank of $t$ is less than the rank of $u$, the result is $F$ with $t$ prepended.
Otherwise the result is the carry of the link of $t$ and $u$ into $F'$.

It is meant for a tree whose rank is no greater than every rank in the forest, where linking
equal-rank trees propagates like a binary carry. -/
@[expose] public def carry [LinearOrder α] (tree : BinomialTree α) :
    List (BinomialTree α) → List (BinomialTree α)
  | [] => [tree]
  | other :: trees =>
      if tree.rank < other.rank then
        tree :: other :: trees
      else
        carry (tree.link other) trees

private theorem elements_carry [LinearOrder α] (tree : BinomialTree α)
    (trees : List (BinomialTree α)) :
    elements (carry tree trees) = tree.elements + elements trees := by
  induction trees generalizing tree with
  | nil => simp [carry, elements]
  | cons other trees ih =>
      rw [carry]
      split
      · simp [elements]
      · rw [ih, BinomialTree.elements_link]
        simp only [elements, List.map_cons, List.sum_cons]
        rw [Multiset.add_assoc]

private theorem carry_correct [LinearOrder α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (tree_valid : tree.Valid) (trees_valid : Valid trees)
    (lower : RanksAtLeast tree.rank trees) :
    Valid (carry tree trees) ∧ RanksAtLeast tree.rank (carry tree trees) := by
  induction trees generalizing tree with
  | nil =>
      constructor
      · exact valid_cons tree_valid valid_nil (by simp)
      · simp [carry, RanksAtLeast]
  | cons other trees ih =>
      rw [carry]
      split
      · rename_i rank_lt
        constructor
        · apply valid_cons tree_valid trees_valid
          intro current member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact rank_lt
          · exact rank_lt.trans (trees_valid.head_lt member)
        · intro current member
          by_cases equal : current = tree
          · subst current
            exact Nat.le_refl tree.rank
          · exact lower current (by simpa [equal] using member)
      · rename_i not_lt
        have rank_le : tree.rank ≤ other.rank := lower other (by simp)
        have ranks : tree.rank = other.rank :=
          Nat.le_antisymm rank_le (Nat.le_of_not_gt not_lt)
        have linked_valid := tree_valid.link trees_valid.head_valid ranks
        have linked_lower : RanksAtLeast (tree.link other).rank trees := by
          intro current member
          rw [BinomialTree.rank_link, ranks]
          exact trees_valid.head_lt member
        have result := ih linked_valid trees_valid.tail linked_lower
        exact ⟨result.1, fun current member => by
          have := result.2 current member
          rw [BinomialTree.rank_link] at this
          omega⟩

/-- **Melding binomial forests.** Over a linear order, the meld of two lists of binomial trees
is defined by recursion on their total length. For every list $L$, the meld of the empty list
with $L$ is $L$, and the meld of $L$ with the empty list is $L$. For nonempty lists with first
trees $s$ and $t$ and remaining lists $F$ and $G$: if the rank of $s$ is less than the rank of
$t$, the meld is $s$ followed by the meld of $F$ with the second list; if the rank of $t$ is less
than the rank of $s$, it is $t$ followed by the meld of the first list with $G$; and if the ranks
are equal, it is the result of carrying the link of $s$ with $t$ into the meld of $F$ and $G$.

It is intended for forests of strictly increasing ranks, where equal-rank trees are linked and
the carries are propagated. -/
@[expose] public def meldTrees [LinearOrder α] :
    List (BinomialTree α) → List (BinomialTree α) → List (BinomialTree α)
  | [], right => right
  | left, [] => left
  | leftTree :: leftTrees, rightTree :: rightTrees =>
      if leftTree.rank < rightTree.rank then
        leftTree :: meldTrees leftTrees (rightTree :: rightTrees)
      else if rightTree.rank < leftTree.rank then
        rightTree :: meldTrees (leftTree :: leftTrees) rightTrees
      else
        carry (leftTree.link rightTree) (meldTrees leftTrees rightTrees)
termination_by left right => left.length + right.length

/-- **Melding binomial forests adds their elements.** For any two lists $L$ and $R$ of binomial
trees over a linearly ordered type, the multiset of elements of the meld of $L$ and $R$ is the
sum of the multisets of elements of $L$ and $R$. -/
theorem elements_meldTrees [LinearOrder α]
    (left right : List (BinomialTree α)) :
    elements (meldTrees left right) = elements left + elements right := by
  cases left with
  | nil => simp [meldTrees, elements]
  | cons leftTree leftTrees =>
      cases right with
      | nil => simp [meldTrees, elements]
      | cons rightTree rightTrees =>
          rw [meldTrees]
          split
          · change leftTree.elements +
                elements (meldTrees leftTrees (rightTree :: rightTrees)) =
              (leftTree.elements + elements leftTrees) +
                elements (rightTree :: rightTrees)
            rw [elements_meldTrees leftTrees (rightTree :: rightTrees)]
            rw [Multiset.add_assoc]
          · split
            · change rightTree.elements +
                  elements (meldTrees (leftTree :: leftTrees) rightTrees) =
                elements (leftTree :: leftTrees) +
                  (rightTree.elements + elements rightTrees)
              rw [elements_meldTrees (leftTree :: leftTrees) rightTrees]
              exact calc
                rightTree.elements +
                    (elements (leftTree :: leftTrees) + elements rightTrees) =
                    (rightTree.elements + elements (leftTree :: leftTrees)) +
                      elements rightTrees := (Multiset.add_assoc _ _ _).symm
                _ =
                    (elements (leftTree :: leftTrees) + rightTree.elements) +
                      elements rightTrees := congrArg
                        (fun values => values + elements rightTrees)
                        (Multiset.add_comm _ _)
                _ = elements (leftTree :: leftTrees) +
                    (rightTree.elements + elements rightTrees) :=
                      Multiset.add_assoc _ _ _
            · rw [elements_carry, BinomialTree.elements_link,
                elements_meldTrees leftTrees rightTrees]
              change (leftTree.elements + rightTree.elements) +
                  (elements leftTrees + elements rightTrees) =
                (leftTree.elements + elements leftTrees) +
                  (rightTree.elements + elements rightTrees)
              exact calc
                (leftTree.elements + rightTree.elements) +
                    (elements leftTrees + elements rightTrees) =
                    leftTree.elements +
                      (rightTree.elements +
                        (elements leftTrees + elements rightTrees)) :=
                          Multiset.add_assoc _ _ _
                _ = leftTree.elements +
                    ((rightTree.elements + elements leftTrees) +
                      elements rightTrees) := congrArg _
                        (Multiset.add_assoc _ _ _).symm
                _ = leftTree.elements +
                    ((elements leftTrees + rightTree.elements) +
                      elements rightTrees) := congrArg
                        (fun values => leftTree.elements +
                          (values + elements rightTrees))
                        (Multiset.add_comm _ _)
                _ = leftTree.elements +
                    (elements leftTrees +
                      (rightTree.elements + elements rightTrees)) := congrArg _
                        (Multiset.add_assoc _ _ _)
                _ = (leftTree.elements + elements leftTrees) +
                    (rightTree.elements + elements rightTrees) :=
                      (Multiset.add_assoc _ _ _).symm
termination_by left.length + right.length

/-- **Melding preserves forest validity and rank lower bounds.** Let $r$ be a natural number
and let $F$ and $G$ be valid binomial forests in which every tree has rank at least $r$. Then
the meld of $F$ and $G$ is a valid binomial forest in which every tree has rank at least $r$. -/
public theorem meldTrees_correct [LinearOrder α] {rank : Nat}
    {left right : List (BinomialTree α)} (left_valid : Valid left)
    (right_valid : Valid right) (left_lower : RanksAtLeast rank left)
    (right_lower : RanksAtLeast rank right) :
    Valid (meldTrees left right) ∧ RanksAtLeast rank (meldTrees left right) := by
  cases left with
  | nil => simpa [meldTrees] using And.intro right_valid right_lower
  | cons leftTree leftTrees =>
      cases right with
      | nil => simpa [meldTrees] using And.intro left_valid left_lower
      | cons rightTree rightTrees =>
          rw [meldTrees]
          split
          · rename_i rank_lt
            have recursive := meldTrees_correct (rank := leftTree.rank + 1)
              left_valid.tail right_valid
              (fun current member => left_valid.head_lt member)
              (by
                intro current member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact rank_lt
                · exact rank_lt.trans (right_valid.head_lt member))
            constructor
            · apply valid_cons left_valid.head_valid recursive.1
              intro current member
              exact recursive.2 current member
            · intro current member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact left_lower current (by simp)
              · have lower_head := left_lower leftTree (by simp)
                have lower_current := recursive.2 current member
                omega
          · split
            · rename_i rank_lt
              have recursive := meldTrees_correct (rank := rightTree.rank + 1)
                left_valid right_valid.tail
                (by
                  intro current member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rank_lt
                  · exact rank_lt.trans (left_valid.head_lt member))
                (fun current member => right_valid.head_lt member)
              constructor
              · apply valid_cons right_valid.head_valid recursive.1
                intro current member
                exact recursive.2 current member
              · intro current member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact right_lower current (by simp)
                · have lower_head := right_lower rightTree (by simp)
                  have lower_current := recursive.2 current member
                  omega
            · rename_i right_not_lt left_not_lt
              have ranks : leftTree.rank = rightTree.rank := by omega
              have recursive := meldTrees_correct (rank := leftTree.rank + 1)
                left_valid.tail right_valid.tail
                (fun current member => left_valid.head_lt member)
                (by
                  intro current member
                  rw [ranks]
                  exact right_valid.head_lt member)
              have linked_valid := left_valid.head_valid.link right_valid.head_valid ranks
              have carried := carry_correct linked_valid recursive.1 (by
                simpa [BinomialTree.rank_link] using recursive.2)
              exact ⟨carried.1, fun current member => by
                have lower_head := left_lower leftTree (by simp)
                have lower_current := carried.2 current member
                rw [BinomialTree.rank_link] at lower_current
                omega⟩
termination_by left.length + right.length

/-- **Removing a minimum-root tree from a forest.** For a list $T$ of binomial trees over a linear
order, the result is nothing when $T$ is empty. Otherwise it is the first tree $m$ of $T$ whose root
is minimal among the roots of the trees of $T$, together with the list obtained from $T$ by
deleting that occurrence of $m$, the remaining trees keeping their order. -/
@[expose] public def removeMinTree [LinearOrder α] :
    List (BinomialTree α) → Option (BinomialTree α × List (BinomialTree α))
  | [] => none
  | tree :: trees =>
      match removeMinTree trees with
      | none => some (tree, [])
      | some (minimum, rest) =>
          if minimum.root < tree.root then
            some (minimum, tree :: rest)
          else
            some (tree, trees)

theorem removeMinTree_eq_none_iff [LinearOrder α]
    (trees : List (BinomialTree α)) : removeMinTree trees = none ↔ trees = [] := by
  cases trees with
  | nil => simp [removeMinTree]
  | cons tree trees =>
      cases found : removeMinTree trees with
      | none => simp [removeMinTree, found]
      | some result =>
          rcases result with ⟨minimum, rest⟩
          by_cases less : minimum.root < tree.root <;>
            simp [removeMinTree, found, less]

/-- **Removing a minimum-root tree.** Let $T$ be a list of binomial trees over a linear order, and
suppose that removing a minimum tree from $T$ returns the tree $m$ and the list $R$. Then the
multiset represented by $m$ plus the multiset represented by the forest $R$ equals the multiset
represented by the forest $T$; $m$ is a member of $T$; $R$ is a sublist of $T$; and the root of
$m$ is at most the root of every tree in $T$. -/
public theorem removeMinTree_spec [LinearOrder α]
    {trees : List (BinomialTree α)} {minimum : BinomialTree α}
    {rest : List (BinomialTree α)} (result : removeMinTree trees = some (minimum, rest)) :
    minimum.elements + elements rest = elements trees ∧
      minimum ∈ trees ∧ rest.Sublist trees ∧
      ∀ tree ∈ trees, minimum.root ≤ tree.root := by
  induction trees generalizing minimum rest with
  | nil => simp [removeMinTree] at result
  | cons tree trees ih =>
      cases found : removeMinTree trees with
      | none =>
          have trees_empty := (removeMinTree_eq_none_iff trees).mp found
          subst trees
          simp only [removeMinTree] at result
          simp only [Option.some.injEq, Prod.mk.injEq] at result
          rcases result with ⟨rfl, rfl⟩
          simp [elements]
      | some selected =>
          rcases selected with ⟨tailMinimum, tailRest⟩
          have tail_spec := ih found
          by_cases less : tailMinimum.root < tree.root
          · simp only [removeMinTree, found, less, ite_true, Option.some.injEq,
              Prod.mk.injEq] at result
            rcases result with ⟨rfl, rfl⟩
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [elements, List.map_cons, List.sum_cons]
              change tailMinimum.elements + (tree.elements + elements tailRest) =
                tree.elements + elements trees
              rw [← tail_spec.1]
              rw [← Multiset.add_assoc,
                Multiset.add_comm tailMinimum.elements tree.elements,
                Multiset.add_assoc]
            · simp [tail_spec.2.1]
            · exact tail_spec.2.2.1.cons_cons tree
            · intro current member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact le_of_lt less
              · exact tail_spec.2.2.2 current member
          · simp only [removeMinTree, found, less, ite_false, Option.some.injEq,
              Prod.mk.injEq] at result
            rcases result with ⟨rfl, rfl⟩
            refine ⟨by rfl, by simp, by simp, ?_⟩
            intro current member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact le_rfl
            · exact (le_of_not_gt less).trans (tail_spec.2.2.2 current member)

theorem removeMinTree_root_le [LinearOrder α] {trees : List (BinomialTree α)}
    {minimum : BinomialTree α} {rest : List (BinomialTree α)}
    (valid : Valid trees) (result : removeMinTree trees = some (minimum, rest))
    {value : α} (member : value ∈ elements trees) : minimum.root ≤ value := by
  have spec := removeMinTree_spec result
  rcases mem_elements_iff.mp member with ⟨tree, tree_mem, value_mem⟩
  exact (spec.2.2.2 tree tree_mem).trans ((valid.1 tree tree_mem).root_le value_mem)

/-- **Reversed children of a valid binomial tree form a valid forest.** For a linearly ordered
type $\alpha$ and a valid binomial tree $t$ over $\alpha$, the children of $t$ listed in reverse
order form a valid binomial forest: every tree in the list is valid and the ranks strictly
increase along the list. -/
public theorem valid_reverse_children [LinearOrder α] {tree : BinomialTree α}
    (valid : tree.Valid) : Valid tree.children.reverse := by
  constructor
  · intro child member
    exact valid.child_valid (by simpa using member)
  · rw [List.map_reverse, valid.children_ranks, List.reverse_reverse]
    exact List.pairwise_lt_range

private theorem sum_append (left right : List (Multiset α)) :
    (left ++ right).sum = left.sum + right.sum := by
  induction left with
  | nil => simp
  | cons value values ih =>
      simp only [List.cons_append, List.sum_cons]
      rw [ih, Multiset.add_assoc]

private theorem sum_reverse (values : List (Multiset α)) :
    values.reverse.sum = values.sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [List.reverse_cons, sum_append, ih]
      rw [Multiset.add_comm]
      change (value + 0) + values.sum = value + values.sum
      rw [Multiset.add_zero]

theorem root_cons_elements_reverse_children (tree : BinomialTree α) :
    tree.root ::ₘ elements tree.children.reverse = tree.elements := by
  cases tree
  simp only [BinomialTree.root, BinomialTree.children, BinomialTree.elements, elements,
    List.map_reverse]
  rw [sum_reverse]

end BinomialForest

/-- **Binomial heap.** A binomial min-heap over a linearly ordered type $\alpha$ consists of a
list of binomial trees over $\alpha$ together with a proof that this list is a valid binomial
forest: every tree in it is a valid binomial tree and the tree ranks are strictly increasing
along the list. -/
public structure BinomialHeap (α : Type u) [LinearOrder α] where
  /-- The binomial trees, in strictly increasing rank order. -/
  trees : List (BinomialTree α)
  valid : BinomialForest.Valid trees

namespace BinomialHeap

variable {α : Type u}

/-- **Elements of a binomial heap.** Over a linearly ordered type, the multiset of elements of a
binomial heap is the multiset of elements of its list of binomial trees, that is, the multiset sum
of the multisets of elements of its trees. -/
@[expose] public def elements [LinearOrder α] (heap : BinomialHeap α) : Multiset α :=
  BinomialForest.elements heap.trees

/-- **Tree ranks in a binomial heap are logarithmic.** Every tree in a binomial heap holding $n$
elements, counted with multiplicity, has rank at most $\lfloor \log_2 n \rfloor$. -/
public theorem rank_le_log2_card [LinearOrder α] (heap : BinomialHeap α)
    {tree : BinomialTree α} (member : tree ∈ heap.trees) :
    tree.rank ≤ Nat.log2 heap.elements.card :=
  heap.valid.member_rank_le_log2_card member

/-- **A binomial heap has logarithmically many trees.** If a binomial heap over a linearly ordered
type has $n$ elements, counted with multiplicity, then its number of trees is at most
$\lfloor \log_2 n \rfloor + 1$, where $\lfloor \log_2 0 \rfloor$ is taken to be $0$. -/
public theorem length_le_log2_card_succ [LinearOrder α] (heap : BinomialHeap α) :
    heap.trees.length ≤ Nat.log2 heap.elements.card + 1 :=
  heap.valid.length_le_log2_card_succ

/-- **Empty binomial heap.** For a linearly ordered type $\alpha$, the empty binomial heap over
$\alpha$ is the binomial heap whose list of trees is empty. -/
@[expose] public def empty [LinearOrder α] : BinomialHeap α :=
  ⟨[], BinomialForest.valid_nil⟩

/-- **Melding binomial heaps.** Over a linear order, the meld of two binomial heaps is the
binomial heap whose forest is the meld of the forests of the two heaps. -/
@[expose] public def meld [LinearOrder α] (left right : BinomialHeap α) : BinomialHeap α :=
  ⟨BinomialForest.meldTrees left.trees right.trees,
    (BinomialForest.meldTrees_correct (rank := 0) left.valid right.valid
      (by simp [BinomialForest.RanksAtLeast])
      (by simp [BinomialForest.RanksAtLeast])).1⟩

/-- **One-element binomial heap.** For a value $a$ in a linearly ordered type $\alpha$, the
one-element binomial heap of $a$ is the binomial heap whose list of trees consists of exactly one
tree: the binomial tree of rank $0$ with root $a$ and no children. -/
@[expose] public def singleton [LinearOrder α] (value : α) : BinomialHeap α :=
  ⟨[BinomialTree.singleton value], by
    apply BinomialForest.valid_cons (BinomialTree.valid_singleton value)
      BinomialForest.valid_nil
    simp⟩

/-- **Insertion into a binomial heap.** Inserting a value $x$ into a binomial heap $H$ over a
linearly ordered type gives the meld of the one-element binomial heap containing $x$ with $H$. -/
@[expose] public def insert [LinearOrder α] (heap : BinomialHeap α) (value : α) : BinomialHeap α :=
  (singleton value).meld heap

/-- **Minimum of a binomial heap.** The minimum lookup of a binomial heap over a linearly ordered
type returns no value when the heap has no trees, and otherwise returns the least of the root
values of its trees, leaving the heap unchanged. -/
@[expose] public def findMin [LinearOrder α] (heap : BinomialHeap α) : Option α :=
  (BinomialForest.removeMinTree heap.trees).map fun result => result.1.root

/-- **Minimum deletion on a binomial forest.** Given a list of binomial trees over a linearly
ordered type, if the list is empty there is no result. Otherwise, remove the first tree whose root
is minimal among the roots of the list; the result is the root of that tree together with the
forest obtained by melding its children, in reversed order, with the remaining trees. -/
@[expose] public def deleteMinTrees [LinearOrder α]
    (trees : List (BinomialTree α)) : Option (α × List (BinomialTree α)) :=
  match BinomialForest.removeMinTree trees with
  | none => none
  | some (minimum, rest) =>
      some (minimum.root,
        BinomialForest.meldTrees minimum.children.reverse rest)

/-- **Deleting the minimum of a binomial heap.** If the binomial heap $H$ has no trees, there is no
result. Otherwise, remove from the list of trees of $H$ the first tree whose root is minimal; the
result is that root together with the binomial heap whose list of trees is obtained by melding
the children of the removed tree, in reversed order, with the remaining trees. -/
public def deleteMin [LinearOrder α]
    (heap : BinomialHeap α) : Option (α × BinomialHeap α) :=
  match found : BinomialForest.removeMinTree heap.trees with
  | none => none
  | some (minimum, rest) =>
      have spec := BinomialForest.removeMinTree_spec found
      have minimum_valid : minimum.Valid := heap.valid.1 minimum spec.2.1
      have rest_valid : BinomialForest.Valid rest := heap.valid.sublist spec.2.2.1
      have children_valid := BinomialForest.valid_reverse_children minimum_valid
      let trees := BinomialForest.meldTrees minimum.children.reverse rest
      have trees_valid : BinomialForest.Valid trees :=
        (BinomialForest.meldTrees_correct (rank := 0) children_valid rest_valid
          (by simp [BinomialForest.RanksAtLeast])
          (by simp [BinomialForest.RanksAtLeast])).1
      some (minimum.root, ⟨trees, trees_valid⟩)

/-- **Binomial heap deletion agrees with forest deletion.** For every binomial heap $H$ over a
linearly ordered type, deleting the minimum of $H$ and then replacing the remaining heap by its
list of trees gives the same result as minimum deletion on the list of trees of $H$: both have no
result, or both return the same minimum value and the same list of trees. -/
public theorem deleteMin_trees [LinearOrder α] (heap : BinomialHeap α) :
    heap.deleteMin.map (fun result => (result.1, result.2.trees)) =
      deleteMinTrees heap.trees := by
  unfold deleteMin deleteMinTrees
  split <;> rename_i found <;> simp only [found] <;> rfl

/-- **Melding binomial heaps adds their elements.** For any two binomial heaps $H_1$ and $H_2$ over
a linearly ordered type, the multiset of elements of the meld of $H_1$ and $H_2$ is the sum of
the multisets of elements of $H_1$ and $H_2$. -/
public theorem elements_meld [LinearOrder α] (left right : BinomialHeap α) :
    (left.meld right).elements = left.elements + right.elements := by
  simpa [meld, elements] using
    (BinomialForest.elements_meldTrees left.trees right.trees)

/-- **Insertion into a binomial heap adds one occurrence.** For every binomial heap $H$ over a
linearly ordered type and every value $v$, the multiset of elements of the heap obtained by
inserting $v$ into $H$ is the multiset of elements of $H$ with one more occurrence of $v$. -/
public theorem elements_insert [LinearOrder α] (heap : BinomialHeap α) (value : α) :
    (heap.insert value).elements = value ::ₘ heap.elements := by
  rw [insert, elements_meld]
  simp [singleton, elements, BinomialForest.elements]

/-- **The minimum lookup fails exactly on the empty binomial heap.** For a binomial heap $H$ over a
linearly ordered type, the minimum lookup of $H$ returns no value if and only if the list of
trees of $H$ is empty. -/
public theorem findMin_eq_none_iff [LinearOrder α] (heap : BinomialHeap α) :
    heap.findMin = none ↔ heap.trees = [] := by
  simp [findMin, BinomialForest.removeMinTree_eq_none_iff]

/-- **The minimum lookup of a binomial heap returns one of its elements.** Let $H$ be a binomial
heap over a linearly ordered type. If the minimum lookup of $H$ returns $m$, then $m$ is an
element of $H$. -/
public theorem findMin_mem [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    (result : heap.findMin = some minimum) : minimum ∈ heap.elements := by
  unfold findMin at result
  cases found : BinomialForest.removeMinTree heap.trees with
  | none => simp [found] at result
  | some selected =>
      rcases selected with ⟨tree, rest⟩
      simp only [found, Option.map_some, Option.some.injEq] at result
      subst minimum
      have spec := BinomialForest.removeMinTree_spec found
      change tree.root ∈ BinomialForest.elements heap.trees
      rw [← spec.1]
      exact Multiset.mem_add.mpr (Or.inl (BinomialTree.root_mem_elements tree))

/-- **The minimum lookup of a binomial heap returns a lower bound.** Let $H$ be a binomial heap over
a linearly ordered type. If the minimum lookup of $H$ returns $m$, then $m \le v$ for every
element $v$ of $H$. -/
public theorem findMin_le [LinearOrder α] {heap : BinomialHeap α} {minimum value : α}
    (result : heap.findMin = some minimum) (member : value ∈ heap.elements) :
    minimum ≤ value := by
  unfold findMin at result
  cases found : BinomialForest.removeMinTree heap.trees with
  | none => simp [found] at result
  | some selected =>
      rcases selected with ⟨tree, rest⟩
      simp only [found, Option.map_some, Option.some.injEq] at result
      subst minimum
      exact BinomialForest.removeMinTree_root_le heap.valid found member

theorem deleteMin_partition [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    have spec := BinomialForest.removeMinTree_spec found
    change tree.root ::ₘ
        BinomialForest.elements
          (BinomialForest.meldTrees tree.children.reverse remaining) =
      BinomialForest.elements heap.trees
    rw [BinomialForest.elements_meldTrees, ← Multiset.cons_add,
      BinomialForest.root_cons_elements_reverse_children, spec.1]

/-- **Deleting the minimum fails only on the empty binomial heap.** For a binomial heap $H$ over a
linearly ordered type, deleting the minimum of $H$ returns no result if and only if the list of
trees of $H$ is empty. -/
public theorem deleteMin_eq_none_iff [LinearOrder α] (heap : BinomialHeap α) :
    heap.deleteMin = none ↔ heap.trees = [] := by
  unfold deleteMin
  split
  · rename_i found
    exact ⟨fun _ => (BinomialForest.removeMinTree_eq_none_iff heap.trees).mp found,
      fun _ => rfl⟩
  · rename_i tree remaining found
    constructor
    · intro impossible
      contradiction
    · intro empty
      have none : BinomialForest.removeMinTree heap.trees = none :=
        (BinomialForest.removeMinTree_eq_none_iff heap.trees).mpr empty
      rw [none] at found
      contradiction

/-- **Deleting the minimum of a binomial heap removes one occurrence.** For a binomial heap $H$
over a linearly ordered type, if deleting the minimum of $H$ succeeds and returns a value $m$
and a heap $H'$, then the multiset of elements of $H'$ is the multiset of elements of $H$ with
one occurrence of $m$ removed. -/
public theorem deleteMin_elements [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    rest.elements = heap.elements.erase minimum := by
  rw [← deleteMin_partition result, Multiset.erase_cons_head]

/-- **Deleting the minimum of a binomial heap splits its multiset.** For a binomial heap $H$ over
a linearly ordered type, if deleting the minimum of $H$ succeeds and returns a value $m$ and a
heap $H'$, then the multiset of elements of $H$ equals the multiset of elements of $H'$ with one
more occurrence of $m$. -/
public theorem deleteMin_cons_elements [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements := by
  exact deleteMin_partition result

/-- **The value deleted from a binomial heap is a lower bound for its elements.** If deleting the
minimum of a binomial heap $H$ over a linearly ordered type succeeds and returns a value $m$
together with a remaining heap, then $m \le v$ for every value $v$ in the multiset of elements of
$H$. -/
public theorem deleteMin_le [LinearOrder α] {heap : BinomialHeap α} {minimum value : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest))
    (member : value ∈ heap.elements) : minimum ≤ value := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact BinomialForest.removeMinTree_root_le heap.valid found member

end BinomialHeap

end Cslib.Algorithms.Lean
