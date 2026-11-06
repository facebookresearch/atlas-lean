/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Order.RelClasses
public import Std.Data.TreeMap

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
# Balanced interval search trees

This module implements closed intervals in an AVL tree ordered by the low
endpoint and a stable occurrence identifier.  Each nonempty node stores its
subtree height, size, and maximum high endpoint.  A second balanced map locates
an existing identifier before replacement or deletion.
-/

namespace Cslib.Algorithms.Lean.IntervalTree

local instance : DecidableLE Int := Int.decLe
local instance : DecidableLT Int := Int.decLt
local instance : DecidableEq Int := Int.decEq

/-- **Interval.** An interval is a pair of integers, its low endpoint and its high endpoint, read as
the closed interval from the low to the high endpoint. The structure itself imposes no order on the
endpoints; the public update operations accept an interval only when its low endpoint is at most
its high endpoint. -/
structure Interval where
  low : Int
  high : Int
deriving Repr, DecidableEq

namespace Interval

/-- **Valid interval.** A closed interval with integer endpoints $a$ (low) and $b$ (high) is
valid when its low endpoint is at most its high endpoint, $a \le b$. -/
def Valid (interval : Interval) : Prop :=
  interval.low ≤ interval.high

/-- **Boolean interval validity test.** For an interval $[a, b]$ with integer endpoints, the
Boolean validity test returns true exactly when $a \le b$. -/
def valid (interval : Interval) : Bool :=
  letI : Decidable interval.Valid := Int.decLe _ _
  decide interval.Valid

/-- **Overlapping closed intervals.** An interval $I$ with low endpoint $a$ and high endpoint $b$
overlaps an interval $J$ with low endpoint $c$ and high endpoint $d$ when $a \le d$ and $c \le b$;
in particular, intervals that share only an endpoint overlap. -/
def Overlaps (left right : Interval) : Prop :=
  left.low ≤ right.high ∧ right.low ≤ left.high

/-- **Overlap test for closed intervals.** For an interval $I$ with low endpoint $a$ and high
endpoint $b$ and an interval $J$ with low endpoint $c$ and high endpoint $d$, the overlap test of
$I$ against $J$ returns true exactly when $a \le d$ and $c \le b$; it compares $a$ with $d$ first
and returns false without the second comparison when $a > d$. -/
def overlaps (left right : Interval) : Bool :=
  match Int.decLe left.low right.high with
  | .isFalse _ => false
  | .isTrue _ =>
      match Int.decLe right.low left.high with
      | .isFalse _ => false
      | .isTrue _ => true

/-- **Overlap test with comparison count.** For an interval $I$ with low endpoint $a$ and high
endpoint $b$ and an interval $J$ with low endpoint $c$ and high endpoint $d$, the instrumented
overlap test of $I$ against $J$ returns the pair (false, $1$) when $a > d$, the pair (false, $2$)
when $a \le d$ and $c > b$, and the pair (true, $2$) when $a \le d$ and $c \le b$; the number
is the count of endpoint comparisons evaluated. -/
def overlapsWithCost (left right : Interval) : Bool × Nat :=
  match Int.decLe left.low right.high with
  | .isFalse _ => (false, 1)
  | .isTrue _ =>
      match Int.decLe right.low left.high with
      | .isFalse _ => (false, 2)
      | .isTrue _ => (true, 2)

/-- **The instrumented overlap test returns the plain result.** For intervals $I$ and $J$, the
Boolean component of the instrumented overlap test of $I$ against $J$ equals the overlap test of
$I$ against $J$. -/
@[simp] theorem overlapsWithCost_fst (left right : Interval) :
    (left.overlapsWithCost right).1 = left.overlaps right := by
  unfold overlapsWithCost overlaps
  cases h₁ : Int.decLe left.low right.high with
  | isFalse _ => rfl
  | isTrue _ =>
      cases h₂ : Int.decLe right.low left.high <;> rfl

/-- **Comparison count of the overlap test.** For intervals $I$ and $J$, the instrumented overlap
test of $I$ against $J$ reports $2$ endpoint comparisons when the low endpoint of $I$ is at most
the high endpoint of $J$, and $1$ comparison otherwise. -/
theorem overlapsWithCost_snd (left right : Interval) :
    (left.overlapsWithCost right).2 = if left.low ≤ right.high then 2 else 1 := by
  unfold overlapsWithCost
  cases h₁ : Int.decLe left.low right.high with
  | isFalse h => simp [h]
  | isTrue h =>
      cases h₂ : Int.decLe right.low left.high <;> simp [h]

theorem overlaps_eq_true {left right : Interval} :
    left.overlaps right = true ↔
      left.Overlaps right := by
  unfold overlaps Overlaps
  cases h₁ : Int.decLe left.low right.high with
  | isFalse _ => simp_all
  | isTrue _ =>
      cases h₂ : Int.decLe right.low left.high <;> simp_all

theorem overlaps_comm (left right : Interval) :
    left.overlaps right = right.overlaps left := by
  unfold overlaps
  cases h₁ : Int.decLe left.low right.high with
  | isFalse _ =>
      cases h₂ : Int.decLe right.low left.high <;> simp_all
  | isTrue _ =>
      cases h₂ : Int.decLe right.low left.high <;> simp_all

end Interval

/-- **Interval tree entry.** An entry of the interval tree consists of an identifier, which is a
natural number, and an interval with integer low and high endpoints.

Identifiers, rather than endpoints, are meant to be unique among stored entries; this is required
by the indexed tree's representation invariant, not by the entry itself. -/
structure Entry where
  id : Nat
  interval : Interval
deriving Repr, DecidableEq

namespace Entry

/-- **Search key of an interval entry.** The key of an entry is the pair
$(\ell, i) \in \mathbb{Z} \times \mathbb{N}$, where $\ell$ is the low endpoint of the entry's
interval and $i$ is the entry's identifier. -/
def key (entry : Entry) : Int × Nat :=
  (entry.interval.low, entry.id)

end Entry

/-- **Lexicographic comparison of keys.** For keys $(a, i)$ and $(b, j)$ in
$\mathbb{Z} \times \mathbb{N}$ (a low endpoint and an occurrence identifier), the comparison
returns less-than if $a < b$, or if $a = b$ and $i < j$; greater-than if $a > b$, or if $a = b$
and $i > j$; and equal if $a = b$ and $i = j$. -/
def compareKey (left right : Int × Nat) : Ordering :=
  if left.1 < right.1 then .lt
  else if right.1 < left.1 then .gt
  else if left.2 < right.2 then .lt
  else if right.2 < left.2 then .gt
  else .eq

/-- **Operation cost counters for interval trees.** A cost record for the interval tree consists
of seven natural-number counters, each defaulting to $0$: node visits, key comparisons, endpoint
comparisons, cached-maximum reads, cache writes, rotations, and identifier-index operations.

The cached-maximum counter is deliberately narrow: it counts only the reads made by search
pruning, one per visited node where the left subtree's cached maximum decides the descent. Node
construction, rebalancing and the rotations read cached heights, sizes and maxima while rebuilding
nodes; those reads are not counted separately, and maintenance work is reported through the cache
write, rotation and remaining counters instead. -/
structure Cost where
  nodeVisits : Nat := 0
  keyComparisons : Nat := 0
  endpointComparisons : Nat := 0
  /-- Cached-maximum reads performed by search pruning only; see `Cost`. -/
  maxCacheReads : Nat := 0
  cacheWrites : Nat := 0
  rotations : Nat := 0
  indexOperations : Nat := 0
deriving Repr, DecidableEq

namespace Cost

protected def add (left right : Cost) : Cost where
  nodeVisits := left.nodeVisits + right.nodeVisits
  keyComparisons := left.keyComparisons + right.keyComparisons
  endpointComparisons := left.endpointComparisons + right.endpointComparisons
  maxCacheReads := left.maxCacheReads + right.maxCacheReads
  cacheWrites := left.cacheWrites + right.cacheWrites
  rotations := left.rotations + right.rotations
  indexOperations := left.indexOperations + right.indexOperations

instance : Add Cost := ⟨Cost.add⟩

end Cost

/-- **Interval tree.** An interval tree is either empty or a node consisting of a left subtree,
an entry, a right subtree and three cached fields: a height and a size (natural numbers) and a
maximum high endpoint (an integer). The type imposes no balance or consistency condition on
these fields; it is the carrier on which the AVL interval-tree operations act. -/
inductive Tree where
  | empty
  | node
      (height : Nat)
      (size : Nat)
      (maxHigh : Int)
      (left : Tree)
      (entry : Entry)
      (right : Tree)
deriving Repr, DecidableEq

namespace Tree

def height : Tree → Nat
  | .empty => 0
  | .node height _ _ _ _ _ => height

def size : Tree → Nat
  | .empty => 0
  | .node _ size _ _ _ _ => size

/-- **Cached maximum of an interval tree.** The cached maximum of an interval tree is no value
when the tree is empty, and when the tree is a node it is the integer stored in the node's cached
maximum-high-endpoint field.

It is read in constant time. The tree type itself does not require this field to equal the
largest high endpoint of an interval in the subtree. -/
def cachedMax? : Tree → Option Int
  | .empty => none
  | .node _ _ maxHigh _ _ _ => some maxHigh

/-- **Maximum with an optional value.** For an integer $a$ and an optional integer $v$, the value
is $a$ when $v$ is absent and $\max(a, v)$ when $v$ is present. It combines a value with an
optional subtree maximum without using a sentinel value. -/
def maxWith (fallback : Int) : Option Int → Int
  | none => fallback
  | some value => max fallback value

/-- **Maximum high endpoint at a node.** For subtrees $L$ and $R$ and an entry $e$, the node
maximum is the largest of the high endpoint of the interval of $e$, the cached maximum high
endpoint stored at the root of $L$, and the one stored at the root of $R$, where an empty subtree
stores no cached maximum and contributes nothing. -/
def nodeMax (left : Tree) (entry : Entry) (right : Tree) : Int :=
  maxWith (maxWith entry.interval.high left.cachedMax?) right.cachedMax?

/-- **Node construction with repaired metadata.** For an interval tree $T$ write $h(T)$ and $|T|$
for its cached height and size, both $0$ for the empty tree. Given interval trees $L$ and $R$ and
an entry $e$, this builds the node with left subtree $L$, entry $e$ and right subtree $R$ whose
cached height is $\max(h(L), h(R)) + 1$, whose cached size is $|L| + |R| + 1$, and whose cached
maximum high endpoint is the largest of the high endpoint of $e$ and the cached maxima of the
nonempty subtrees among $L$ and $R$.

It is the sole ordinary node constructor. -/
def mkNode (left : Tree) (entry : Entry) (right : Tree) : Tree :=
  .node (max left.height right.height + 1) (left.size + right.size + 1)
    (nodeMax left entry right) left entry right

def singleton (entry : Entry) : Tree :=
  mkNode .empty entry .empty

def entries : Tree → List (Entry)
  | .empty => []
  | .node _ _ _ left entry right => left.entries ++ entry :: right.entries

/-- **Cache invariant of an interval tree.** An interval tree satisfies the cache invariant when
every cached field is exact, recursively. The empty tree satisfies it. A node with stored height
$h$, stored size $s$, stored maximum $m$, left subtree $L$, entry $e$ and right subtree $R$
satisfies it when $L$ and $R$ satisfy it, $m$ is at least the high endpoint of every entry of
$L$, of $e$ and of every entry of $R$, $m$ equals the high endpoint of one of these entries,
$h = \max(\operatorname{height} L, \operatorname{height} R) + 1$ and
$s = \operatorname{size} L + \operatorname{size} R + 1$. Here the height and size of a subtree
are its stored fields, and the empty tree has height and size $0$. -/
def CacheInvariant : Tree → Prop
  | .empty => True
  | .node storedHeight storedSize maxHigh left entry right =>
      left.CacheInvariant ∧ right.CacheInvariant ∧
      (∀ stored ∈ left.entries ++ entry :: right.entries,
        stored.interval.high ≤ maxHigh) ∧
      (∃ stored ∈ left.entries ++ entry :: right.entries,
        stored.interval.high = maxHigh) ∧
      storedHeight = max left.height right.height + 1 ∧
      storedSize = left.size + right.size + 1

/-- **Low-endpoint ordered interval tree.** The empty tree is low-endpoint ordered, and a node is
low-endpoint ordered when both of its subtrees are low-endpoint ordered, every interval in the
left subtree has low endpoint at most the low endpoint of the node's interval, and the node's
low endpoint is at most the low endpoint of every interval in the right subtree. -/
def LowOrdered : Tree → Prop
  | .empty => True
  | .node _ _ _ left entry right =>
      left.LowOrdered ∧ right.LowOrdered ∧
      (∀ stored ∈ left.entries, stored.interval.low ≤ entry.interval.low) ∧
      (∀ stored ∈ right.entries, entry.interval.low ≤ stored.interval.low)

/-- **Validity invariant of an interval tree.** A tree satisfies the validity invariant when
every interval stored in it is valid, that is, its low endpoint is at most its high endpoint.
Recursively, the empty tree satisfies it, and a node satisfies it when its left subtree does,
the interval of its entry is valid, and its right subtree does. -/
def ValidInvariant : Tree → Prop
  | .empty => True
  | .node _ _ _ left entry right =>
      left.ValidInvariant ∧ entry.interval.Valid ∧ right.ValidInvariant

def computedMax? : Tree → Option Int
  | .empty => none
  | .node _ _ _ left entry right =>
      some (maxWith (maxWith entry.interval.high left.computedMax?) right.computedMax?)

/-- **Right rotation.** Write $\langle L, x, R\rangle$ for a node with left subtree $L$, entry $x$
and right subtree $R$. The right rotation sends $\langle\langle a, x, b\rangle, y, c\rangle$ to
$\langle a, x, \langle b, y, c\rangle\rangle$, where both nodes of the result get freshly
recomputed height, size and maximum high endpoint. Every tree not of this shape is returned
unchanged. -/
def rotateRight : Tree → Tree
  | .node _ _ _ (.node _ _ _ a x b) y c =>
      mkNode a x (mkNode b y c)
  | tree => tree

/-- **Left rotation.** Write $\langle L, x, R\rangle$ for a node with left subtree $L$, entry $x$
and right subtree $R$. The left rotation sends $\langle a, x, \langle b, y, c\rangle\rangle$ to
$\langle\langle a, x, b\rangle, y, c\rangle$, where both nodes of the result get freshly
recomputed height, size and maximum high endpoint. Every tree not of this shape is returned
unchanged. -/
def rotateLeft : Tree → Tree
  | .node _ _ _ a x (.node _ _ _ b y c) =>
      mkNode (mkNode a x b) y c
  | tree => tree

/-- **Left-right double rotation.** Write $\langle L, x, R\rangle$ for a node with left subtree
$L$, entry $x$ and right subtree $R$. The left-right rotation sends
$\langle\langle a, x, \langle b, y, c\rangle\rangle, z, d\rangle$ to
$\langle\langle a, x, b\rangle, y, \langle c, z, d\rangle\rangle$, where all three nodes of the
result get freshly recomputed height, size and maximum high endpoint. Every tree not of this
shape is returned unchanged. -/
def rotateLeftRight : Tree → Tree
  | .node _ _ _ (.node _ _ _ a x (.node _ _ _ b y c)) z d =>
      mkNode (mkNode a x b) y (mkNode c z d)
  | tree => tree

/-- **Right-left double rotation.** Write $\langle L, x, R\rangle$ for a node with left subtree
$L$, entry $x$ and right subtree $R$. The right-left rotation sends
$\langle a, x, \langle\langle b, y, c\rangle, z, d\rangle\rangle$ to
$\langle\langle a, x, b\rangle, y, \langle c, z, d\rangle\rangle$, where all three nodes of the
result get freshly recomputed height, size and maximum high endpoint. Every tree not of this
shape is returned unchanged. -/
def rotateRightLeft : Tree → Tree
  | .node _ _ _ a x (.node _ _ _ (.node _ _ _ b y c) z d) =>
      mkNode (mkNode a x b) y (mkNode c z d)
  | tree => tree

/-- **AVL rebalancing step with cost.** Rebalancing a tree $T$ returns a tree and a cost, where
heights are the stored heights. If $T$ is empty, or neither subtree of its root is more than one
taller than the other, it returns $T$ unchanged with zero cost. If the left subtree $L$ is more
than one taller than the right subtree, it applies a right rotation, costing $2$ cache writes and
one rotation, when the left child of $L$ is at least as tall as the right child of $L$, and
otherwise a left-right double rotation, costing $3$ cache writes and two rotations. If the right
subtree $R$ is more than one taller than the left subtree, it applies a left rotation, costing
$2$ cache writes and one rotation, when the right child of $R$ is at least as tall as the left
child of $R$, and otherwise a right-left double rotation, costing $3$ cache writes and two
rotations. All other cost counters are zero. -/
def rebalanceWithCost (tree : Tree) : Tree × Cost :=
  match tree with
  | .empty => (.empty, {})
  | .node _ _ _ left _ right =>
      if left.height > right.height + 1 then
        match left with
        | .empty => (tree, {})
        | .node _ _ _ ll _ lr =>
            if ll.height ≥ lr.height then
              (rotateRight tree, { cacheWrites := 2, rotations := 1 })
            else
              (rotateLeftRight tree, { cacheWrites := 3, rotations := 2 })
      else if right.height > left.height + 1 then
        match right with
        | .empty => (tree, {})
        | .node _ _ _ rl _ rr =>
            if rr.height ≥ rl.height then
              (rotateLeft tree, { cacheWrites := 2, rotations := 1 })
            else
              (rotateRightLeft tree, { cacheWrites := 3, rotations := 2 })
      else
        (tree, {})

private def rebalance (tree : Tree) : Tree :=
  (rebalanceWithCost tree).1

/-- **Keyed insertion with cost.** Inserting an entry $x$ into a tree returns a new tree together
with an operation cost; keys (low endpoint, then identifier) are compared lexicographically. Into
the empty tree, $x$ is inserted as a single node, at a cost of one node visit and one cache write.
At a node with entry $y$: if the key of $x$ equals the key of $y$, then $y$ is replaced by $x$, at a
cost of one node visit, one key comparison and one cache write; if the key of $x$ is smaller
(respectively larger), then $x$ is inserted recursively into the left (respectively right)
subtree, the node is rebuilt with recomputed metadata and rebalanced, and the cost is the cost of
the recursive insertion, plus one node visit, one key comparison and one cache write, plus the
cost of rebalancing. -/
def insertKeyWithCost (newEntry : Entry) : Tree → Tree × Cost
  | .empty =>
      (singleton newEntry, { nodeVisits := 1, cacheWrites := 1 })
  | .node _ _ _ left entry right =>
      match compareKey newEntry.key entry.key with
      | .lt =>
          let (newLeft, childCost) := insertKeyWithCost newEntry left
          let (result, balanceCost) := rebalanceWithCost (mkNode newLeft entry right)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)
      | .eq =>
          (mkNode left newEntry right,
            { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 })
      | .gt =>
          let (newRight, childCost) := insertKeyWithCost newEntry right
          let (result, balanceCost) := rebalanceWithCost (mkNode left entry newRight)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)

def insertKey (tree : Tree) (entry : Entry) : Tree :=
  (tree.insertKeyWithCost entry).1

/-- **Removing the leftmost entry, with its cost.** Removing the leftmost entry of an interval
tree $T$ returns nothing when $T$ is empty. When the root's left subtree is empty, it returns the
root entry, the right subtree, and a cost of one node visit. Otherwise it removes the leftmost
entry $m$ of the left subtree recursively (returning nothing if that fails), rebuilds the root
node over the new left subtree with recomputed height, size and maximum high endpoint, and
rebalances that node; it returns $m$, the rebalanced tree, and the cost of the recursive call plus
one node visit and one cache write plus the cost of rebalancing. -/
def removeMinWithCost :
    Tree → Option (Entry × Tree × Cost)
  | .empty => none
  | .node _ _ _ .empty entry right =>
      some (entry, right, { nodeVisits := 1 })
  | .node _ _ _ left entry right =>
      match removeMinWithCost left with
      | none => none
      | some (minimum, newLeft, childCost) =>
          let (result, balanceCost) := rebalanceWithCost (mkNode newLeft entry right)
          some (minimum, result,
            childCost + { nodeVisits := 1, cacheWrites := 1 } + balanceCost)

/-- **Keyed erasure with cost.** Erasing a key $k \in \mathbb{Z} \times \mathbb{N}$ from an
interval tree returns a new tree together with its cost; the key of an entry is the pair of its low
endpoint and identifier, and keys are compared lexicographically. The empty tree is returned
unchanged at a cost of one node visit. At a node with entry $x$, the key $k$ is compared with the
key of $x$. If $k$ is smaller, $k$ is erased from the left subtree; if it is larger, from the right
subtree; in both cases the node is rebuilt with the new subtree and rebalanced, and the cost is the
subtree's cost plus one node visit, one key comparison, one cache write and the rebalancing cost.
If $k$ equals the key of $x$ and the right subtree is empty (so it has no leftmost entry to
remove), the result is the left subtree at a cost of one node visit and one key comparison.
Otherwise the leftmost entry of the right subtree is removed and takes the place of $x$, the node
is rebuilt and rebalanced, and the cost is the removal's cost plus one node visit, one key
comparison, one cache write and the rebalancing cost. -/
def eraseKeyWithCost (key : Int × Nat) : Tree → Tree × Cost
  | .empty => (.empty, { nodeVisits := 1 })
  | .node _ _ _ left entry right =>
      match compareKey key entry.key with
      | .lt =>
          let (newLeft, childCost) := eraseKeyWithCost key left
          let (result, balanceCost) := rebalanceWithCost (mkNode newLeft entry right)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)
      | .gt =>
          let (newRight, childCost) := eraseKeyWithCost key right
          let (result, balanceCost) := rebalanceWithCost (mkNode left entry newRight)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)
      | .eq =>
          match right.removeMinWithCost with
          | none =>
              (left, { nodeVisits := 1, keyComparisons := 1 })
          | some (successor, newRight, childCost) =>
              let (result, balanceCost) := rebalanceWithCost (mkNode left successor newRight)
              (result,
                childCost +
                  { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
                  balanceCost)

def eraseKey (tree : Tree) (key : Int × Nat) : Tree :=
  (tree.eraseKeyWithCost key).1

@[simp] theorem entries_mkNode (left : Tree) (entry : Entry) (right : Tree) :
    (mkNode left entry right).entries = left.entries ++ entry :: right.entries :=
  rfl

theorem entries_rotateRight (tree : Tree) :
    tree.rotateRight.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases left with
      | empty => rfl
      | node _ _ _ a x b =>
          simp [rotateRight, entries_mkNode, entries, List.append_assoc]

theorem entries_rotateLeft (tree : Tree) :
    tree.rotateLeft.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases right with
      | empty => rfl
      | node _ _ _ b y c =>
          simp [rotateLeft, entries_mkNode, entries, List.append_assoc]

theorem entries_rotateLeftRight (tree : Tree) :
    tree.rotateLeftRight.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases left with
      | empty => rfl
      | node _ _ _ a x lr =>
          cases lr with
          | empty => rfl
          | node _ _ _ b y c =>
              simp [rotateLeftRight, entries_mkNode, entries, List.append_assoc]

theorem entries_rotateRightLeft (tree : Tree) :
    tree.rotateRightLeft.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases right with
      | empty => rfl
      | node _ _ _ rl y c =>
          cases rl with
          | empty => rfl
          | node _ _ _ b z d =>
              simp [rotateRightLeft, entries_mkNode, entries, List.append_assoc]

theorem entries_rebalanceWithCost (tree : Tree) :
    (tree.rebalanceWithCost).1.entries = tree.entries := by
  unfold rebalanceWithCost
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | rfl
      | simp [entries_rotateRight, entries_rotateLeft,
          entries_rotateLeftRight, entries_rotateRightLeft]


/-- **Instrumented overlap search.** Given a query interval $q = [c, d]$ and an interval tree
$T$, the instrumented overlap search returns an optional entry together with a cost record,
defined by recursion on $T$. On the empty tree it returns no entry and records one node visit.
At a node with left subtree $L$, entry $e$ with interval $[a, b]$ and right subtree $R$, it
first tests overlap by evaluating $a \le d$ and, only if that holds, $c \le b$; let
$k \in \{1, 2\}$ be the number of relations evaluated. If both hold, it returns $e$ and records
one node visit and $k$ endpoint comparisons. Otherwise, if $L$ is empty, it returns the result of
searching $R$, adding one node visit and $k$ endpoint comparisons to that search's cost. If $L$
is nonempty with cached maximum high endpoint $m$, it returns the result of searching $L$ when
$c \le m$ and of searching $R$ otherwise, adding one node visit, $k + 1$ endpoint comparisons and
one cached-maximum read to that search's cost. No other counter is ever incremented. -/
def searchWithCost (query : Interval) : Tree → Option Entry × Cost
  | .empty => (none, { nodeVisits := 1 })
  | .node _ _ _ left entry right =>
      let (overlap, endpointCost) := entry.interval.overlapsWithCost query
      if overlap then
        (some entry, { nodeVisits := 1, endpointComparisons := endpointCost })
      else
        match left.cachedMax? with
        | none =>
            let (answer, childCost) := searchWithCost query right
            (answer, childCost + { nodeVisits := 1, endpointComparisons := endpointCost })
        | some leftMax =>
            if query.low ≤ leftMax then
              let (answer, childCost) := searchWithCost query left
              (answer, childCost +
                { nodeVisits := 1, endpointComparisons := endpointCost + 1, maxCacheReads := 1 })
            else
              let (answer, childCost) := searchWithCost query right
              (answer, childCost +
                { nodeVisits := 1, endpointComparisons := endpointCost + 1, maxCacheReads := 1 })

/-- **Instrumented search in the empty tree.** For every query interval $q$, the instrumented
overlap search of $q$ in the empty interval tree returns no entry, and its cost record counts
one node visit and zero for every other counter (key comparisons, endpoint comparisons,
cached-maximum reads, cache writes, rotations and index operations). -/
@[simp] theorem searchWithCost_empty (query : Interval) :
    searchWithCost query .empty = (none, { nodeVisits := 1 }) := rfl

/-- **Instrumented search in a one-entry tree.** Let $e$ be an entry whose interval is $[a, b]$,
let $q = [c, d]$ be a query interval, and let $k = 2$ if $a \le d$ and $k = 1$ otherwise.
Consider the single-node tree built from $e$ with empty subtrees and exact cached fields. If
$[a, b]$ and $[c, d]$ overlap (that is, $a \le d$ and $c \le b$), the instrumented overlap search
of $q$ in this tree returns $e$ with a cost record of one node visit and $k$ endpoint
comparisons. Otherwise it returns no entry with a cost record of two node visits (the root and
its empty right subtree) and $k$ endpoint comparisons. All other counters are zero in both
cases. -/
theorem searchWithCost_singleton (entry : Entry) (query : Interval) :
    searchWithCost query (singleton entry) =
      if entry.interval.overlaps query then
        (some entry,
          { nodeVisits := 1
            endpointComparisons := if entry.interval.low ≤ query.high then 2 else 1 })
      else
        (none,
          { nodeVisits := 2
            endpointComparisons := if entry.interval.low ≤ query.high then 2 else 1 }) := by
  by_cases rootMatches : entry.interval.overlaps query = true
  · simp [singleton, mkNode, searchWithCost, rootMatches, Interval.overlapsWithCost_snd]
  · simp only [singleton, mkNode, searchWithCost,
      Interval.overlapsWithCost_fst, cachedMax?, rootMatches, Bool.false_eq_true, ite_false,
      Interval.overlapsWithCost_snd]
    change ((none : Option Entry), Cost.add { nodeVisits := 1 }
      { nodeVisits := 1,
        endpointComparisons := if entry.interval.low ≤ query.high then 2 else 1 }) = _
    simp [Cost.add]

/-- **Interval-tree overlap search.** The overlap search of a query interval $q$ in an interval
tree $T$ returns the optional entry produced by the instrumented overlap search of $q$ in $T$,
discarding its cost record. -/
def search (tree : Tree) (query : Interval) : Option Entry :=
  (tree.searchWithCost query).1

/-- **Linear-scan overlap search.** For a tree $T$ and a query interval $q$, the oracle search
returns the first entry, in the in-order list of entries of $T$, whose interval overlaps $q$ as
closed intervals, and returns nothing when no entry's interval overlaps $q$.

It is a separate full-traversal oracle used only by specifications and tests. -/
def oracleSearch (tree : Tree) (query : Interval) : Option Entry :=
  tree.entries.find? fun entry => entry.interval.overlaps query

theorem searchWithCost_fst (tree : Tree) (query : Interval) :
    (tree.searchWithCost query).1 = tree.search query := rfl

theorem search_sound {tree : Tree} {query : Interval}
    {entry : Entry} (found : tree.search query = some entry) :
    entry ∈ tree.entries ∧ entry.interval.overlaps query = true := by
  induction tree with
  | empty => simp [search, searchWithCost] at found
  | node height size maxHigh left root right leftIH rightIH =>
      simp only [search, searchWithCost] at found
      split at found
      · simp_all [entries]
      · split at found
        · exact ⟨by simp [entries, (rightIH found).1], (rightIH found).2⟩
        · split at found
          · exact ⟨by simp [entries, (leftIH found).1], (leftIH found).2⟩
          · exact ⟨by simp [entries, (rightIH found).1], (rightIH found).2⟩

/-- **Completeness of interval-tree search.** Let $T$ be an interval tree whose cached height, size
and maximum high endpoint are exact at every node, and whose low endpoints respect the search
order (at every node, low endpoints in the left subtree are at most the node's, and those in the
right subtree at least the node's). If some entry stored in $T$ has an interval that overlaps the
query interval $Q$ (each interval's low endpoint is at most the other's high endpoint), then
searching $T$ for $Q$ returns some entry. -/
theorem search_complete {tree : Tree} {query : Interval} {witness : Entry}
    (cache : tree.CacheInvariant) (ordered : tree.LowOrdered)
    (member : witness ∈ tree.entries)
    (overlap : witness.interval.Overlaps query) :
    ∃ found, tree.search query = some found := by
  induction tree generalizing query witness with
  | empty => simp [entries] at member
  | node height size maxHigh left root right leftIH rightIH =>
      simp only [CacheInvariant] at cache
      simp only [LowOrdered] at ordered
      rcases cache with ⟨leftCache, rightCache, _, _⟩
      rcases ordered with ⟨leftOrdered, rightOrdered, leftLow, rightLow⟩
      have memberCases :
          witness ∈ left.entries ∨ witness = root ∨ witness ∈ right.entries := by
        simpa [entries, or_assoc] using member
      by_cases rootMatches : root.interval.overlaps query = true
      · exact ⟨root, by simp [search, searchWithCost, rootMatches]⟩
      · cases left with
        | empty =>
            rcases memberCases with inLeft | atRoot | inRight
            · simp [entries] at inLeft
            · subst witness
              exact (rootMatches (Interval.overlaps_eq_true.mpr overlap)).elim
            · rcases rightIH rightCache rightOrdered inRight overlap with
                ⟨found, foundEq⟩
              have foundCost : (right.searchWithCost query).1 = some found := by
                simpa only [search] using foundEq
              exact ⟨found, by
                simpa [search, searchWithCost, rootMatches, cachedMax?] using
                  foundCost⟩
        | node leftHeight leftSize leftMax leftLeft leftRoot leftRight =>
            simp only [CacheInvariant] at leftCache
            rcases leftCache with
              ⟨leftLeftCache, leftRightCache, leftUpper, leftWitness, leftHeightEq, leftSizeEq⟩
            by_cases inspectLeft : query.low ≤ leftMax
            · have leftHasOverlap :
                  ∃ candidate ∈
                      (Tree.node leftHeight leftSize leftMax leftLeft leftRoot
                        leftRight).entries,
                    candidate.interval.Overlaps query := by
                rcases memberCases with inLeft | atRoot | inRight
                · exact ⟨witness, inLeft, overlap⟩
                · subst witness
                  exact (rootMatches (Interval.overlaps_eq_true.mpr overlap)).elim
                · rcases leftWitness with ⟨candidate, candidateMem, candidateHigh⟩
                  refine ⟨candidate, candidateMem, ?_, ?_⟩
                  · exact le_trans (leftLow candidate candidateMem)
                      (le_trans (rightLow witness inRight) overlap.1)
                  · simpa [candidateHigh] using inspectLeft
              rcases leftHasOverlap with
                ⟨candidate, candidateMem, candidateOverlap⟩
              rcases leftIH
                  ⟨leftLeftCache, leftRightCache, leftUpper, leftWitness,
                    leftHeightEq, leftSizeEq⟩
                  leftOrdered candidateMem candidateOverlap with
                ⟨found, foundEq⟩
              have foundCost :
                  ((Tree.node leftHeight leftSize leftMax leftLeft leftRoot
                    leftRight).searchWithCost query).1 = some found := by
                simpa only [search] using foundEq
              exact ⟨found, by
                simpa [search, searchWithCost, rootMatches, cachedMax?, inspectLeft]
                  using foundCost⟩
            · have inRight : witness ∈ right.entries := by
                rcases memberCases with inLeft | atRoot | inRight
                · have highLe : witness.interval.high ≤ leftMax :=
                    leftUpper witness inLeft
                  exact (inspectLeft (le_trans overlap.2 highLe)).elim
                · subst witness
                  exact (rootMatches (Interval.overlaps_eq_true.mpr overlap)).elim
                · exact inRight
              rcases rightIH rightCache rightOrdered inRight overlap with
                ⟨found, foundEq⟩
              have foundCost : (right.searchWithCost query).1 = some found := by
                simpa only [search] using foundEq
              exact ⟨found, by
                simpa [search, searchWithCost, rootMatches, cachedMax?, inspectLeft]
                  using foundCost⟩

/-- **Interval-tree search fails exactly when nothing overlaps.** Let $T$ be an interval tree
whose cached height, size and maximum high endpoint are exact at every node, and whose low
endpoints respect the search order (at every node, low endpoints in the left subtree are at most
the node's, and those in the right subtree at least the node's). Then searching $T$ for a query
interval $Q$ returns nothing if and only if no entry stored in $T$ has an interval that overlaps
$Q$ (each interval's low endpoint is at most the other's high endpoint). -/
theorem search_eq_none_iff {tree : Tree} {query : Interval}
    (cache : tree.CacheInvariant) (ordered : tree.LowOrdered) :
    tree.search query = none ↔
      ∀ entry ∈ tree.entries, ¬entry.interval.Overlaps query := by
  constructor
  · intro none entry member overlap
    rcases search_complete cache ordered member overlap with ⟨found, foundEq⟩
    rw [none] at foundEq
    contradiction
  · intro noOverlap
    cases foundEq : tree.search query with
    | none => rfl
    | some entry =>
        have sound := search_sound foundEq
        exact (noOverlap entry sound.1
          (Interval.overlaps_eq_true.mp sound.2)).elim

/-- **Executable cache check for interval trees.** The Boolean cache check returns true on the
empty tree. On a node with stored height $h$, stored size $s$, stored maximum $m$, left subtree
$L$, entry $e$ and right subtree $R$ it returns true exactly when
$h = \max(\operatorname{height} L, \operatorname{height} R) + 1$,
$s = \operatorname{size} L + \operatorname{size} R + 1$, $m$ is the largest of the high endpoint
of $e$ and the cached maxima of those of $L$ and $R$ that are nonempty, and the check returns
true on both $L$ and $R$. Here the height and size of a subtree are its stored fields, and the
empty tree has height and size $0$.

It is used only by the executable invariant checker. -/
def cacheOK : Tree → Bool
  | .empty => true
  | .node storedHeight storedSize storedMax left entry right =>
      storedHeight == max left.height right.height + 1 &&
      storedSize == left.size + right.size + 1 &&
      storedMax == nodeMax left entry right &&
      left.cacheOK && right.cacheOK

/-- **Key between optional bounds.** Given an optional lower bound, an optional upper bound and a
key $k$ (a pair of an integer and a natural number), this test returns true exactly when the lower
bound is absent or strictly below $k$, and the upper bound is absent or strictly above $k$. Keys
are compared lexicographically: first by the integer, then by the natural number. -/
def keyBetween
    (lower upper : Option (Int × Nat)) (key : Int × Nat) : Bool :=
  lower.all (fun value => compareKey value key == .lt) &&
    upper.all (fun value => compareKey key value == .lt)

/-- **Ordered-and-valid check for interval trees.** Keys of entries are pairs (low endpoint,
identifier), ordered lexicographically. Given optional lower and upper key bounds $\ell$ and $u$,
the check accepts the empty tree, and accepts a node with left subtree $L$, entry $e$ and right
subtree $R$ exactly when the key $k$ of $e$ is strictly greater than $\ell$ if $\ell$ is present
and strictly less than $u$ if $u$ is present, the interval of $e$ has low endpoint at most its
high endpoint, $L$ is accepted with bounds $\ell$ and $k$, and $R$ is accepted with bounds $k$
and $u$. -/
def orderedValid :
    Option (Int × Nat) → Option (Int × Nat) → Tree → Bool
  | _, _, .empty => true
  | lower, upper, .node _ _ _ left entry right =>
      keyBetween lower upper entry.key && entry.interval.valid &&
      orderedValid lower (some entry.key) left &&
      orderedValid (some entry.key) upper right

/-- **Boolean AVL balance check for interval trees.** The balance check returns true on the empty
tree. On a node whose left and right subtrees have stored heights $h_L$ and $h_R$ (the empty tree
has height $0$), it returns true exactly when the node's stored height equals
$\max(h_L, h_R) + 1$, $h_L \le h_R + 1$, $h_R \le h_L + 1$, and the check returns true on both
subtrees. -/
def balanced : Tree → Bool
  | .empty => true
  | .node storedHeight _ _ left _ right =>
      storedHeight == max left.height right.height + 1 &&
      left.height ≤ right.height + 1 && right.height ≤ left.height + 1 &&
      left.balanced && right.balanced

def uniqueIds (tree : Tree) : Bool :=
  decide (tree.entries.map (·.id)).Nodup

/-- **AVL balance of an interval tree.** An interval tree is AVL balanced with exact stored heights
when it is empty, or when it is a node such that, writing $h_L$ and $h_R$ for the stored heights
of its left and right subtrees (the empty tree has height $0$), the node's stored height equals
$\max(h_L, h_R) + 1$, $h_L \le h_R + 1$, $h_R \le h_L + 1$, and both subtrees are again AVL
balanced with exact stored heights. -/
def BalancedProp : Tree → Prop
  | .empty => True
  | .node storedHeight _ _ left _ right =>
      storedHeight = max left.height right.height + 1 ∧
      left.height ≤ right.height + 1 ∧ right.height ≤ left.height + 1 ∧
      left.BalancedProp ∧ right.BalancedProp

theorem balancedProp_of_balanced {tree : Tree} (h : tree.balanced = true) :
    tree.BalancedProp := by
  induction tree with
  | empty => trivial
  | node storedHeight _ _ left _ right leftIH rightIH =>
      simp only [balanced, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, leftIH h.1.2, rightIH h.2⟩

theorem compareKey_lt_low {a b : Int × Nat} (h : compareKey a b = .lt) :
    a.1 ≤ b.1 := by
  unfold compareKey at h
  by_cases hlt : a.1 < b.1
  · exact le_of_lt hlt
  · by_cases hgt : b.1 < a.1
    · simp [hlt, hgt] at h
    · have heq : a.1 = b.1 := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      exact le_of_eq heq

theorem compareKey_lt_iff {a b : Int × Nat} :
    compareKey a b = .lt ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  unfold compareKey
  split_ifs <;> simp_all <;> omega

/-- **Key-ordered interval tree.** The empty tree is key-ordered, and a node is key-ordered when
both of its subtrees are key-ordered, the key of every entry in the left subtree is strictly less
than the key of the node's entry, and the key of the node's entry is strictly less than the key of
every entry in the right subtree. Keys are compared lexicographically: low endpoint first, then
identifier. -/
def KeyOrdered : Tree → Prop
  | .empty => True
  | .node _ _ _ left entry right =>
      left.KeyOrdered ∧ right.KeyOrdered ∧
      (∀ e ∈ left.entries, compareKey e.key entry.key = .lt) ∧
      (∀ e ∈ right.entries, compareKey entry.key e.key = .lt)

theorem compareKey_lt_trans {a b c : Int × Nat} (h1 : compareKey a b = .lt)
    (h2 : compareKey b c = .lt) : compareKey a c = .lt := by
  rw [compareKey_lt_iff] at h1 h2 ⊢
  rcases h1 with h | ⟨h, h'⟩ <;> rcases h2 with g | ⟨g, g'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩


theorem keyOrdered_lowOrdered {tree : Tree} (h : tree.KeyOrdered) :
    tree.LowOrdered := by
  induction tree with
  | empty => trivial
  | node _ _ _ left entry right leftIH rightIH =>
      exact ⟨leftIH h.1, rightIH h.2.1,
        fun e he => compareKey_lt_low (h.2.2.1 e he),
        fun e he => compareKey_lt_low (h.2.2.2 e he)⟩

/-- **The executable ordering check implies key ordering.** Let $t$ be an interval tree and let
$\ell$ and $u$ be optional keys in $\mathbb{Z} \times \mathbb{N}$. If the executable ordering check
of $t$ with lower bound $\ell$ and upper bound $u$ succeeds, then $t$ is key-ordered, and every
entry $e$ stored in $t$ satisfies $\ell < \operatorname{key}(e)$ when $\ell$ is present and
$\operatorname{key}(e) < u$ when $u$ is present, where $<$ is the lexicographic order on keys
(low endpoint first, then identifier). -/
theorem keyOrdered_of_orderedValid {lower upper : Option (Int × Nat)}
    {tree : Tree} (h : tree.orderedValid lower upper = true) :
    tree.KeyOrdered ∧
      ∀ e ∈ tree.entries,
        (∀ v ∈ lower, compareKey v e.key = .lt) ∧
          ∀ v ∈ upper, compareKey e.key v = .lt := by
  induction tree generalizing lower upper with
  | empty => exact ⟨trivial, fun e he => by simp [entries] at he⟩
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [orderedValid, Bool.and_eq_true] at h
      have hbetween := h.1.1
      have hleft := h.1.2
      have hright := h.2
      rcases leftIH hleft with ⟨leftOrd, leftBounds⟩
      rcases rightIH hright with ⟨rightOrd, rightBounds⟩
      have hentry : (∀ v ∈ lower, compareKey v entry.key = .lt) ∧
          ∀ v ∈ upper, compareKey entry.key v = .lt := by
        have hb := hbetween
        rw [keyBetween] at hb
        simp only [Bool.and_eq_true, Option.all_eq_true] at hb
        constructor
        · intro v hv
          cases lower with
          | none => simp at hv
          | some x =>
              have hx : x = v := by simpa using hv
              exact beq_iff_eq.mp (hb.1.1 v (congrArg some hx))
        · intro v hv
          cases upper with
          | none => simp at hv
          | some x =>
              have hx : x = v := by simpa using hv
              exact beq_iff_eq.mp (hb.1.2 v (congrArg some hx))
      refine ⟨⟨leftOrd, rightOrd, ?_, ?_⟩, ?_⟩
      · intro stored hstored
        exact (leftBounds stored hstored).2 entry.key (by simp)
      · intro stored hstored
        exact (rightBounds stored hstored).1 entry.key (by simp)
      · intro e he
        simp only [entries, List.mem_append, List.mem_cons] at he
        rcases he with h | h | h
        · rcases leftBounds e h with ⟨hlo, hhi⟩
          exact ⟨hlo, fun v hv =>
            compareKey_lt_trans (hhi entry.key (by simp)) (hentry.2 v hv)⟩
        · subst h
          exact hentry
        · rcases rightBounds e h with ⟨hlo, hhi⟩
          exact ⟨fun v hv =>
            compareKey_lt_trans (hentry.1 v hv) (hlo entry.key (by simp)), hhi⟩

/-- **The executable ordering check implies low-endpoint ordering.** Let $t$ be an interval tree
and let $\ell$ and $u$ be optional keys in $\mathbb{Z} \times \mathbb{N}$. If the executable
ordering check of $t$ with lower bound $\ell$ and upper bound $u$ succeeds, then $t$ is
low-endpoint ordered, and every entry $e$ stored in $t$ satisfies $\ell < \operatorname{key}(e)$
when $\ell$ is present and $\operatorname{key}(e) < u$ when $u$ is present, where $<$ is the
lexicographic order on keys (low endpoint first, then identifier). -/
theorem lowOrdered_of_orderedValid {lower upper : Option (Int × Nat)}
    {tree : Tree} (h : tree.orderedValid lower upper = true) :
    tree.LowOrdered ∧
      ∀ e ∈ tree.entries,
        (∀ v ∈ lower, compareKey v e.key = .lt) ∧
          ∀ v ∈ upper, compareKey e.key v = .lt :=
  ⟨keyOrdered_lowOrdered (keyOrdered_of_orderedValid h).1,
    (keyOrdered_of_orderedValid h).2⟩


/-- **The ordering check implies interval validity.** Let $T$ be an interval tree and let
$\ell$ and $u$ be optional lower and upper key bounds. If the executable check of $T$ with
bounds $\ell$ and $u$, which tests that every key lies strictly between its bounds and that every
stored interval passes the Boolean validity test, returns true, then every interval stored in
$T$ is valid, that is, its low endpoint is at most its high endpoint. -/
theorem validInvariant_of_orderedValid {lower upper : Option (Int × Nat)}
    {tree : Tree} (h : tree.orderedValid lower upper = true) :
    tree.ValidInvariant := by
  induction tree generalizing lower upper with
  | empty => trivial
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [orderedValid, Bool.and_eq_true] at h
      exact ⟨leftIH h.1.2, by
        have hv := h.1.1.2
        unfold Interval.valid at hv
        exact @of_decide_eq_true _ (Int.decLe _ _) hv, rightIH h.2⟩

theorem key_nodup_of_id_nodup {tree : Tree}
    (h : (tree.entries.map (·.id)).Nodup) :
    (tree.entries.map Entry.key).Nodup := by
  have gen : ∀ l : List Entry, (l.map (·.id)).Nodup → (l.map Entry.key).Nodup := by
    intro l hl
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.nodup_cons] at hl ⊢
        refine ⟨?_, ih hl.2⟩
        intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨y, hy, hkey⟩ := hmem
        have hid : y.id = x.id := congrArg Prod.snd hkey
        exact hl.1 (List.mem_map.mpr ⟨y, hy, hid⟩)
  exact gen tree.entries h

theorem compareKey_eq_iff {a b : Int × Nat} :
    compareKey a b = .eq ↔ a = b := by
  unfold compareKey
  split_ifs with h1 h2 h3 h4 <;> simp_all [Prod.ext_iff] <;> omega

theorem compareKey_gt {a b : Int × Nat} (h : compareKey a b = .gt) :
    compareKey b a = .lt := by
  unfold compareKey at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem compareKey_ne_of_lt {a b : Int × Nat} (h : compareKey a b = .lt) :
    a ≠ b := by
  intro hab
  subst hab
  simp [compareKey] at h

theorem mem_insertKeyWithCost (newEntry e : Entry) {tree : Tree}
    (huniq : (tree.entries.map Entry.key).Nodup) (hord : KeyOrdered tree) :
    e ∈ (tree.insertKeyWithCost newEntry).1.entries ↔
      e = newEntry ∨ (e ∈ tree.entries ∧ e.key ≠ newEntry.key) := by
  induction tree with
  | empty =>
      simp [insertKeyWithCost, singleton, entries_mkNode, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [entries, List.map_append, List.map_cons] at huniq
      rw [List.nodup_append] at huniq
      obtain ⟨hleft, hmid, hdisj⟩ := huniq
      have hentryR : entry.key ∉ right.entries.map Entry.key :=
        (List.nodup_cons.mp hmid).1
      have hright : (right.entries.map Entry.key).Nodup :=
        (List.nodup_cons.mp hmid).2
      have hdisj' : ∀ e ∈ left.entries, e.key ≠ entry.key := by
        intro x hx
        exact hdisj x.key (List.mem_map (f := Entry.key).mpr ⟨x, hx, rfl⟩)
          entry.key (List.mem_map (f := Entry.key).mpr
            ⟨entry, (by simp : entry ∈ entry :: right.entries), rfl⟩)
      have hdisjR : ∀ e ∈ right.entries, e.key ≠ entry.key := by
        intro x hx hkey
        exact hentryR (List.mem_map (f := Entry.key).mpr ⟨x, hx, hkey⟩)
      unfold insertKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft hord.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · rcases ih.mp he with rfl | ⟨he, hne⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨by simp [entries, he], hne⟩
          · subst he
            exact Or.inr ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hlt
              exact compareKey_ne_of_lt hlt rfl⟩
          · exact Or.inr ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt (hord.2.2.2 e he))
                hkey.symm⟩
        · intro he
          rcases he with rfl | ⟨he, hne⟩
          · simp only [List.mem_append, List.mem_cons]
            exact Or.inl (ih.mpr (Or.inl rfl))
          · simp only [entries, List.mem_append, List.mem_cons] at he ⊢
            rcases he with he | he | he
            · exact Or.inl (ih.mpr (Or.inr ⟨he, hne⟩))
            · exact Or.inr (Or.inl he)
            · exact Or.inr (Or.inr he)
      · rename_i heq
        rw [entries_mkNode]
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact Or.inr ⟨by simp [entries, he], by
              intro hkey
              have hkk : newEntry.key = entry.key := compareKey_eq_iff.mp heq
              exact absurd (hkey.trans hkk) (hdisj' e he)⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨by simp [entries, he], by
              intro hkey
              have hkk : newEntry.key = entry.key := compareKey_eq_iff.mp heq
              exact absurd (hkey.trans hkk) (hdisjR e he)⟩
        · intro he
          rcases he with rfl | ⟨he, hne⟩
          · simp
          · simp only [entries, List.mem_append, List.mem_cons] at he ⊢
            rcases he with he | he | he
            · exact Or.inl he
            · subst he
              exact absurd (compareKey_eq_iff.mp heq).symm hne
            · exact Or.inr (Or.inr he)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright hord.2.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · exact Or.inr ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans (hord.2.2.1 e he) (compareKey_gt hgt))
                hkey⟩
          · subst he
            exact Or.inr ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hgt
              simp [compareKey] at hgt⟩
          · rcases ih.mp he with rfl | ⟨he, hne⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨by simp [entries, he], hne⟩
        · intro he
          rcases he with rfl | ⟨he, hne⟩
          · simp only [List.mem_append, List.mem_cons]
            exact Or.inr (Or.inr (ih.mpr (Or.inl rfl)))
          · simp only [entries, List.mem_append, List.mem_cons] at he ⊢
            rcases he with he | he | he
            · exact Or.inl he
            · exact Or.inr (Or.inl he)
            · exact Or.inr (Or.inr (ih.mpr (Or.inr ⟨he, hne⟩)))


theorem removeMinWithCost_spec {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (huniq : (tree.entries.map Entry.key).Nodup) :
    minimum ∈ tree.entries ∧
      ∀ e, e ∈ rest.entries ↔ e ∈ tree.entries ∧ e ≠ minimum := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          have hnotmem : minimum.key ∉ right.entries.map Entry.key := by
            have := huniq
            simp only [entries, List.map_append, List.map_cons] at this
            exact (List.nodup_cons.mp this).1
          refine ⟨by simp [entries], fun e => ?_⟩
          constructor
          · intro he
            exact ⟨by simp [entries, he], by
              intro hcon
              subst hcon
              exact hnotmem (List.mem_map (f := Entry.key).mpr ⟨e, he, rfl⟩)⟩
          · intro he
            rcases he with ⟨he, hne⟩
            simp only [entries, List.mem_append, List.mem_cons] at he
            rcases he with he | he | he
            · simp at he
            · subst he; exact absurd rfl hne
            · exact he
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            simp only [entries, List.map_append, List.map_cons] at huniq
            rw [List.nodup_append] at huniq
            have ih := leftIH hev (by simpa [entries] using huniq.1)
            rw [entries_rebalanceWithCost, entries_mkNode]
            have hminleft : minimum.key ∈
                List.map Entry.key ll.entries ++ le.key ::
                  List.map Entry.key lr.entries := by
              simpa [entries, List.map_append, List.map_cons] using
                (List.mem_map (f := Entry.key).mpr ⟨minimum, ih.1, rfl⟩)
            have hdisjLR : ∀ a ∈ List.map Entry.key ll.entries ++
                  le.key :: List.map Entry.key lr.entries,
                ∀ b ∈ (entry :: right.entries).map Entry.key, a ≠ b := huniq.2.2
            refine ⟨?_, fun e => ?_⟩
            · have h := ih.1
              simp only [entries, List.mem_append, List.mem_cons] at h ⊢
              rcases h with h | h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr (Or.inl h))
              · exact Or.inl (Or.inr (Or.inr h))
            · constructor
              · intro he
                simp only [List.mem_append, List.mem_cons] at he
                rcases he with he | he | he
                · rcases (ih.2 e).mp he with ⟨hmem, hne⟩
                  refine ⟨?_, hne⟩
                  have h := hmem
                  simp only [entries, List.mem_append, List.mem_cons] at h ⊢
                  rcases h with h | h | h
                  · exact Or.inl (Or.inl h)
                  · exact Or.inl (Or.inr (Or.inl h))
                  · exact Or.inl (Or.inr (Or.inr h))
                · exact ⟨by simp [entries, he], fun hcon =>
                    (hdisjLR minimum.key hminleft entry.key
                      (List.mem_map (f := Entry.key).mpr
                        ⟨entry, (by simp : entry ∈ entry :: right.entries), rfl⟩))
                      (by rw [← hcon, ← he])⟩
                · exact ⟨by simp [entries, he], fun hcon =>
                    (hdisjLR minimum.key hminleft minimum.key
                      (List.mem_map (f := Entry.key).mpr
                        ⟨e, List.mem_cons_of_mem entry he, congrArg Entry.key hcon⟩)) rfl⟩
              · intro he
                rcases he with ⟨hmem, hne⟩
                simp only [entries, List.mem_append, List.mem_cons] at hmem
                simp only [List.mem_append, List.mem_cons]
                rcases hmem with (he | rfl | he) | he | he
                · exact Or.inl ((ih.2 e).mpr ⟨List.mem_append_left _ he, hne⟩)
                · exact Or.inl ((ih.2 e).mpr
                    ⟨List.mem_append_right _ (List.mem_cons_self), hne⟩)
                · exact Or.inl ((ih.2 e).mpr
                    ⟨List.mem_append_right _ (List.mem_cons_of_mem _ he), hne⟩)
                · exact Or.inr (Or.inl he)
                · exact Or.inr (Or.inr he)

theorem removeMinWithCost_isSome {tree : Tree} (h : tree.entries ≠ []) :
    tree.removeMinWithCost.isSome := by
  induction tree with
  | empty => simp [entries] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty => simp [removeMinWithCost]
      | node hh ss mm ll le lr =>
          have ih := leftIH (by simp [entries])
          unfold removeMinWithCost
          split
          · rename_i hnone
            obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ih
            cases hnone.symm.trans hx
          · exact Option.isSome_some

theorem keyOrdered_mkNode {left right : Tree} {entry : Entry}
    (hleft : left.KeyOrdered) (hright : right.KeyOrdered)
    (hbl : ∀ e ∈ left.entries, compareKey e.key entry.key = .lt)
    (hbr : ∀ e ∈ right.entries, compareKey entry.key e.key = .lt) :
    (mkNode left entry right).KeyOrdered :=
  ⟨hleft, hright, hbl, hbr⟩

theorem keyOrdered_rotateRight {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateRight.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact h
      | node _ _ _ a x b =>
          obtain ⟨⟨ha, hb, hab, hxb⟩, hright, hleftb, hrightb⟩ := h
          change (mkNode a x (mkNode b entry right)).KeyOrdered
          apply keyOrdered_mkNode ha
          · apply keyOrdered_mkNode hb hright
            · intro e he
              exact hleftb e (by simp [entries, he])
            · exact hrightb
          · exact hab
          · intro e he
            simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact hxb e he
            · exact hleftb x (by simp [entries])
            · exact compareKey_lt_trans (hleftb x (by simp [entries])) (hrightb e he)

theorem keyOrdered_rotateLeft {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateLeft.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact h
      | node _ _ _ b y c =>
          obtain ⟨hleft, ⟨hb, hc, hby, hyc⟩, hleftb, hrightb⟩ := h
          change (mkNode (mkNode left entry b) y c).KeyOrdered
          apply keyOrdered_mkNode
          · apply keyOrdered_mkNode hleft hb
            · exact hleftb
            · intro e he
              exact hrightb e (by simp [entries, he])
          · exact hc
          · intro e he
            simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact compareKey_lt_trans (hleftb e he) (hrightb y (by simp [entries]))
            · exact hrightb y (by simp [entries])
            · exact hby e he
          · exact hyc

theorem keyOrdered_rotateLeftRight {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateLeftRight.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact h
      | node _ _ _ a x lr =>
          cases lr with
          | empty => exact h
          | node _ _ _ b y c =>
              obtain ⟨⟨ha, ⟨hb, hc, hbc, hcb⟩, hab, hxmid⟩, hright, hleftb, hrightb⟩ := h
              have hxy : compareKey x.key y.key = .lt :=
                hxmid y (by simp [entries])
              have hye : compareKey y.key entry.key = .lt :=
                hleftb y (by simp [entries])
              apply keyOrdered_mkNode
              · apply keyOrdered_mkNode ha hb hab
                intro e he
                exact hxmid e (by simp [entries, he])
              · apply keyOrdered_mkNode hc hright
                · intro e he
                  exact hleftb e (by simp [entries, he])
                · exact hrightb
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact compareKey_lt_trans (hab e he) hxy
                · exact hxy
                · exact hbc e he
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact hcb e he
                · exact hye
                · exact compareKey_lt_trans hye (hrightb e he)

theorem keyOrdered_rotateRightLeft {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateRightLeft.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact h
      | node _ _ _ rl y c =>
          cases rl with
          | empty => exact h
          | node _ _ _ b z d =>
              obtain ⟨hleft, ⟨⟨hb, hd, hbd, hdz⟩, hc, hmid, hzmid⟩, hleftb, hrightb⟩ := h
              have hzy : compareKey z.key y.key = .lt :=
                hmid z (by simp [entries])
              have hze : compareKey entry.key z.key = .lt :=
                hrightb z (by simp [entries])
              apply keyOrdered_mkNode
              · apply keyOrdered_mkNode hleft hb
                · exact hleftb
                · intro e he
                  exact hrightb e (by simp [entries, he])
              · apply keyOrdered_mkNode hd hc
                · intro e he
                  exact hmid e (by simp [entries, he])
                · exact hzmid
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact compareKey_lt_trans (hleftb e he) hze
                · exact hze
                · exact hbd e he
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact hdz e he
                · exact hzy
                · exact compareKey_lt_trans hzy (hzmid e he)

theorem keyOrdered_rebalance {tree : Tree} (h : tree.KeyOrdered) :
    (tree.rebalanceWithCost).1.KeyOrdered := by
  unfold rebalanceWithCost
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | exact h
      | exact keyOrdered_rotateRight h
      | exact keyOrdered_rotateLeft h
      | exact keyOrdered_rotateLeftRight h
      | exact keyOrdered_rotateRightLeft h

theorem mem_insertKeyWithCost_of_mem (newEntry e : Entry) (tree : Tree)
    (he : e ∈ (tree.insertKeyWithCost newEntry).1.entries) :
    e = newEntry ∨ e ∈ tree.entries := by
  induction tree with
  | empty =>
      exact Or.inl (by simpa [insertKeyWithCost, singleton, entries_mkNode,
        entries] using he)
  | node _ _ _ left entry right leftIH rightIH =>
      unfold insertKeyWithCost at he
      split at he
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · rcases leftIH he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (by simp [entries, he])
        · exact Or.inr (by simp [entries, he])
        · exact Or.inr (by simp [entries, he])
      · rw [entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | rfl | he
        · exact Or.inr (by simp [entries, he])
        · exact Or.inl rfl
        · exact Or.inr (by simp [entries, he])
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · exact Or.inr (by simp [entries, he])
        · exact Or.inr (by simp [entries, he])
        · rcases rightIH he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (by simp [entries, he])

theorem removeMinWithCost_min_mem {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost)) :
    minimum ∈ tree.entries := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, -, -⟩ := h
          simp [entries]
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, -, -⟩ := h
            have ih := leftIH hev
            simp only [entries, List.mem_append, List.mem_cons]
            simp only [entries, List.mem_append, List.mem_cons] at ih
            rcases ih with ih | ih | ih
            · exact Or.inl (Or.inl ih)
            · exact Or.inl (Or.inr (Or.inl ih))
            · exact Or.inl (Or.inr (Or.inr ih))

theorem mem_removeMinWithCost_of_mem {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost)) (e : Entry)
    (he : e ∈ rest.entries) : e ∈ tree.entries := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨-, rfl, -⟩ := h
          simp [entries, he]
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨-, rfl, -⟩ := h
            rw [entries_rebalanceWithCost, entries_mkNode] at he
            simp only [List.mem_append, List.mem_cons] at he
            rcases he with he | he | he
            · have ih := leftIH hev he
              simp only [entries, List.mem_append, List.mem_cons]
              simp only [entries, List.mem_append, List.mem_cons] at ih
              rcases ih with ih | ih | ih
              · exact Or.inl (Or.inl ih)
              · exact Or.inl (Or.inr (Or.inl ih))
              · exact Or.inl (Or.inr (Or.inr ih))
            · simp [entries, he]
            · simp [entries, he]

theorem mem_eraseKeyWithCost_of_mem (key : Int × Nat) (e : Entry) (tree : Tree)
    (he : e ∈ (tree.eraseKeyWithCost key).1.entries) : e ∈ tree.entries := by
  induction tree with
  | empty => simp [eraseKeyWithCost, entries] at he
  | node _ _ _ left entry right leftIH rightIH =>
      unfold eraseKeyWithCost at he
      split at he
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · exact by simp [entries, leftIH he]
        · exact by simp [entries, he]
        · exact by simp [entries, he]
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · exact by simp [entries, he]
        · exact by simp [entries, he]
        · exact by simp [entries, rightIH he]
      · split at he
        · exact by simp [entries, he]
        · rename_i successor newRight childCost hsome
          rw [entries_rebalanceWithCost, entries_mkNode] at he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact by simp [entries, he]
          · exact by simp [entries, removeMinWithCost_min_mem hsome]
          · exact by simp [entries, mem_removeMinWithCost_of_mem hsome e he]

theorem mem_eraseKeyWithCost (key : Int × Nat) (e : Entry) {tree : Tree}
    (huniq : (tree.entries.map Entry.key).Nodup) (hord : KeyOrdered tree) :
    e ∈ (tree.eraseKeyWithCost key).1.entries ↔
      e ∈ tree.entries ∧ e.key ≠ key := by
  induction tree with
  | empty => simp [eraseKeyWithCost, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [entries, List.map_append, List.map_cons] at huniq
      rw [List.nodup_append] at huniq
      obtain ⟨hleft, hmid, hdisj⟩ := huniq
      have hright : (right.entries.map Entry.key).Nodup :=
        (List.nodup_cons.mp hmid).2
      unfold eraseKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft hord.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · rcases ih.mp he with ⟨hmem, hne⟩
            exact ⟨by simp [entries, hmem], hne⟩
          · subst he
            exact ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hlt
              exact compareKey_ne_of_lt hlt rfl⟩
          · exact ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt
                (hord.2.2.2 e he)) hkey.symm⟩
        · intro he
          rcases he with ⟨hmem, hne⟩
          simp only [entries, List.mem_append, List.mem_cons] at hmem
          simp only [List.mem_append, List.mem_cons]
          rcases hmem with he | he | he
          · exact Or.inl (ih.mpr ⟨he, hne⟩)
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr he)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright hord.2.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · exact ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans (hord.2.2.1 e he) (compareKey_gt hgt))
                hkey⟩
          · subst he
            exact ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hgt
              simp [compareKey] at hgt⟩
          · rcases ih.mp he with ⟨hmem, hne⟩
            exact ⟨by simp [entries, hmem], hne⟩
        · intro he
          rcases he with ⟨hmem, hne⟩
          simp only [entries, List.mem_append, List.mem_cons] at hmem
          simp only [List.mem_append, List.mem_cons]
          rcases hmem with he | he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr (ih.mpr ⟨he, hne⟩))
      · rename_i heq
        have hkeyeq : key = entry.key := compareKey_eq_iff.mp heq
        split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          constructor
          · intro he
            exact ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (hord.2.2.1 e he) (by rw [hkey, hkeyeq])⟩
          · intro he
            rcases he with ⟨hmem, hne⟩
            simp only [entries, List.mem_append, List.mem_cons] at hmem
            rcases hmem with he | he | he
            · exact he
            · subst he; exact absurd hkeyeq.symm hne
            · simp at he
        · rename_i successor newRight childCost hsome
          rw [entries_rebalanceWithCost, entries_mkNode]
          have hspec := removeMinWithCost_spec hsome hright
          have hsuccmem : successor ∈ right.entries := hspec.1
          have hsucckey : successor.key ≠ key := by
            intro hkey
            have hlt : compareKey entry.key successor.key = .lt :=
              hord.2.2.2 successor hsuccmem
            rw [← hkeyeq] at hlt
            rw [hkey] at hlt
            simp [compareKey] at hlt
          constructor
          · intro he
            simp only [List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact ⟨by simp [entries, he], by
                intro hkey
                exact absurd (hkey.trans hkeyeq) (by
                  have hdisj2 : ∀ e ∈ left.entries, e.key ≠ entry.key := by
                    intro x hx
                    exact hdisj x.key (List.mem_map (f := Entry.key).mpr ⟨x, hx, rfl⟩)
                      entry.key (List.mem_map (f := Entry.key).mpr
                        ⟨entry, (by simp : entry ∈ entry :: right.entries), rfl⟩)
                  exact hdisj2 e he)⟩
            · exact ⟨by simp [entries, hsuccmem], hsucckey⟩
            · rcases (hspec.2 e).mp he with ⟨hmem, hne⟩
              exact ⟨by simp [entries, hmem], by
                intro hkey
                have hlt : compareKey entry.key e.key = .lt := hord.2.2.2 e hmem
                rw [← hkeyeq, hkey] at hlt
                simp [compareKey] at hlt⟩
          · intro he
            rcases he with ⟨hmem, hne⟩
            simp only [entries, List.mem_append, List.mem_cons] at hmem
            simp only [List.mem_append, List.mem_cons]
            rcases hmem with he | he | he
            · exact Or.inl he
            · subst he; exact absurd hkeyeq.symm hne
            · by_cases hsucc : e = successor
              · subst hsucc; exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr ((hspec.2 e).mpr ⟨he, hsucc⟩))

/-- **Removing the minimum preserves the other entries.** If removing the leftmost entry of a tree
$T$ returns an entry $m$, a tree $T'$ and a cost, then the list consisting of $m$ followed by the
in-order entries of $T'$ is a permutation of the in-order entries of $T$. -/
theorem removeMinWithCost_entries_perm {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost)) :
    (minimum :: rest.entries).Perm tree.entries := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          simp [entries]
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            rw [entries_rebalanceWithCost, entries_mkNode]
            have ih := leftIH hev
            simp only [entries] at ih ⊢
            exact List.Perm.append_right _ ih

/-- **Entries after keyed insertion.** Let $t$ be a tree whose entries are strictly ordered by key,
and let $x$ be an entry. The in-order list of entries of the tree obtained by inserting $x$ into $t$
by key is a permutation of the list consisting of $x$ followed by those entries of $t$ whose key
differs from the key of $x$. -/
theorem insertKeyWithCost_entries_perm (newEntry : Entry) {tree : Tree}
    (hord : tree.KeyOrdered) :
    ((tree.insertKeyWithCost newEntry).1.entries).Perm
      (newEntry :: tree.entries.filter (fun e => e.key ≠ newEntry.key)) := by
  induction tree with
  | empty =>
      simp [insertKeyWithCost, singleton, entries_mkNode, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hleft, hright, hbl, hbr⟩ := hord
      unfold insertKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft
        have hentry : entry.key ≠ newEntry.key := fun hk =>
          compareKey_ne_of_lt hlt (by rw [hk])
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ newEntry.key) =
            left.entries.filter (fun e => e.key ≠ newEntry.key) ++
              entry :: right.entries := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt (hbr e he)) hk.symm))]
          simp [hentry]
        exact (List.Perm.append_right _ ih).trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i heq
        rw [entries_mkNode]
        have hkeyeq : newEntry.key = entry.key := compareKey_eq_iff.mp heq
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ newEntry.key) =
            left.entries ++ right.entries := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (hbl e he) (by rw [hk, hkeyeq]))),
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (hbr e he) (hk.trans hkeyeq).symm))]
          simp [hkeyeq]
        exact List.perm_middle.trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright
        have hentry : entry.key ≠ newEntry.key := fun hk => by
          have := compareKey_gt hgt
          rw [hk] at this
          exact compareKey_ne_of_lt this rfl
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ newEntry.key) =
            left.entries ++ entry ::
              right.entries.filter (fun e => e.key ≠ newEntry.key) := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans (hbl e he)
                (compareKey_gt hgt)) hk))]
          simp [hentry]
        exact (List.Perm.append_left _
            (List.Perm.cons entry ih)).trans
          ((List.Perm.append_left _ (List.Perm.swap _ _ _)).trans
            (List.perm_middle.trans
              (by simp only [entries, hfilter]; exact List.Perm.refl _)))

/-- **Keyed erasure removes exactly the entries with that key.** The key of an entry is the pair
$(\ell, i) \in \mathbb{Z} \times \mathbb{N}$ of its low endpoint $\ell$ and identifier $i$; keys are
compared lexicographically. Let $T$ be an interval tree whose keys are strictly ordered (every key
in a left subtree is lexicographically below its node's key and every key in a right subtree is
above it), and let $k \in \mathbb{Z} \times \mathbb{N}$ be a key. Then the in-order list of entries
of the tree obtained by erasing $k$ from $T$ is a permutation of the in-order list of entries of $T$
with every entry of key $k$ removed. -/
theorem eraseKeyWithCost_entries_perm (key : Int × Nat) {tree : Tree}
    (hord : tree.KeyOrdered) :
    ((tree.eraseKeyWithCost key).1.entries).Perm
      (tree.entries.filter (fun e => e.key ≠ key)) := by
  induction tree with
  | empty => simp [eraseKeyWithCost, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hleft, hright, hbl, hbr⟩ := hord
      unfold eraseKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft
        have hentry : entry.key ≠ key := fun hk =>
          compareKey_ne_of_lt hlt hk.symm
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ key) =
            left.entries.filter (fun e => e.key ≠ key) ++
              entry :: right.entries := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt (hbr e he)) hk.symm))]
          simp [hentry]
        exact (List.Perm.append_right _ ih).trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright
        have hentry : entry.key ≠ key := fun hk => by
          have h2 := compareKey_gt hgt
          rw [← hk] at h2
          exact compareKey_ne_of_lt h2 rfl
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ key) =
            left.entries ++ entry ::
              right.entries.filter (fun e => e.key ≠ key) := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans (hbl e he)
                (compareKey_gt hgt)) hk))]
          simp [hentry]
        exact (List.Perm.append_left _
            (List.Perm.cons entry ih)).trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i heq
        have hkeyeq : key = entry.key := compareKey_eq_iff.mp heq
        split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          have hfilter : (left.entries ++ entry :: []).filter
              (fun e => e.key ≠ key) = left.entries := by
            rw [List.filter_append, List.filter_cons,
              (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
                compareKey_ne_of_lt (hbl e he) (by rw [hk, hkeyeq])))]
            simp [hkeyeq]
          exact (by simp only [entries, hfilter]; exact List.Perm.refl _)
        · rename_i successor newRight childCost hsome
          rw [entries_rebalanceWithCost, entries_mkNode]
          have hperm := removeMinWithCost_entries_perm hsome
          have hsucc : successor.key ≠ key := by
            intro hk
            have hlt : compareKey entry.key successor.key = .lt :=
              hbr successor (removeMinWithCost_min_mem hsome)
            rw [← hkeyeq, hk] at hlt
            simp [compareKey] at hlt
          have hpermR : (right.entries.filter (fun e => e.key ≠ key)).Perm
              (successor :: newRight.entries) := by
            have h1 : (right.entries.filter (fun e => e.key ≠ key)).Perm
                ((successor :: newRight.entries).filter
                  (fun e => e.key ≠ key)) :=
              List.Perm.filter _ hperm.symm
            rw [List.filter_cons,
              (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
                compareKey_ne_of_lt
                  (hbr e (mem_removeMinWithCost_of_mem hsome e he))
                  (by rw [hk, hkeyeq])))] at h1
            simpa [hsucc] using h1
          have hfilter : (left.entries ++ entry :: right.entries).filter
              (fun e => e.key ≠ key) =
              left.entries ++ right.entries.filter (fun e => e.key ≠ key) := by
            rw [List.filter_append, List.filter_cons,
              (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
                compareKey_ne_of_lt (hbl e he) (by rw [hk, hkeyeq])))]
            simp [hkeyeq]
          exact (List.Perm.append_left _ hpermR.symm).trans
            (by simp only [entries, hfilter]; exact List.Perm.refl _)

/-- **Strictly key-ordered trees have distinct keys.** If a tree is strictly ordered by key, then
the keys of its stored entries are pairwise distinct. -/
theorem keyNodup_of_keyOrdered {tree : Tree} (hord : tree.KeyOrdered) :
    (tree.entries.map Entry.key).Nodup := by
  induction tree with
  | empty => simp [entries]
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, hr, hbl, hbr⟩ := hord
      simp only [entries, List.map_append, List.map_cons]
      rw [List.nodup_append]
      refine ⟨leftIH hl, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨fun hmem => ?_, rightIH hr⟩
        simp only [List.mem_map] at hmem
        obtain ⟨e, he, hk⟩ := hmem
        have hlt := hbr e he
        rw [← hk] at hlt
        simp [compareKey] at hlt
      · intro a ha b hb hab
        simp only [List.mem_map] at ha
        obtain ⟨x, hx, rfl⟩ := ha
        rcases List.mem_cons.mp hb with rfl | hb
        · exact compareKey_ne_of_lt (hbl x hx) hab
        · simp only [List.mem_map] at hb
          obtain ⟨y, hy, rfl⟩ := hb
          exact compareKey_ne_of_lt
            (compareKey_lt_trans (hbl x hx) (hbr y hy)) hab

/-- **The removed minimum has the least key.** Let $T$ be a key-ordered interval tree: at every
node, the keys in the left subtree are strictly smaller and those in the right subtree strictly
larger than the node's key, where the key of an entry is the pair (low endpoint, identifier)
compared lexicographically. If removing the leftmost entry of $T$ returns the entry $m$ (together
with the remaining tree and a cost record), then every entry $e$ stored in $T$ is either $m$
itself or has a key strictly larger than the key of $m$. -/
theorem removeMinWithCost_min_le {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hord : tree.KeyOrdered) :
    ∀ e ∈ tree.entries, e = minimum ∨
      compareKey minimum.key e.key = .lt := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          intro e he
          simp only [entries, List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · simp at he
          · exact Or.inl rfl
          · exact Or.inr (hord.2.2.2 e he)
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            have ih := leftIH hev hord.1
            have hminmem := removeMinWithCost_min_mem hev
            intro e he
            simp only [entries, List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact ih e (by
                simp only [entries, List.mem_append, List.mem_cons]
                exact he)
            · exact Or.inr (hord.2.2.1 minimum hminmem)
            · have h1 : compareKey minimum.key entry.key = .lt :=
                hord.2.2.1 minimum hminmem
              exact Or.inr (compareKey_lt_trans h1 (hord.2.2.2 e he))

/-- **Insertion into an interval tree preserves key ordering.** Let $t$ be a key-ordered interval
tree and let $e$ be an entry. Then the tree returned by the cost-instrumented keyed insertion of
$e$ into $t$ (which replaces the entry with the same key, if there is one; the reported cost is
discarded) is again key-ordered. -/
theorem keyOrdered_insertKeyWithCost (newEntry : Entry) {tree : Tree}
    (hord : tree.KeyOrdered) :
    (tree.insertKeyWithCost newEntry).1.KeyOrdered := by
  induction tree with
  | empty =>
      exact keyOrdered_mkNode trivial trivial
        (fun e he => by simp [entries] at he)
        (fun e he => by simp [entries] at he)
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, hr, hbl, hbr⟩ := hord
      unfold insertKeyWithCost
      split
      · rename_i hlt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode (leftIH hl) hr
        · intro e he
          rcases mem_insertKeyWithCost_of_mem newEntry e left he with rfl | he
          · exact hlt
          · exact hbl e he
        · exact hbr
      · rename_i heq
        have hkeyeq : newEntry.key = entry.key := compareKey_eq_iff.mp heq
        apply keyOrdered_mkNode hl hr
        · intro e he
          rw [hkeyeq]
          exact hbl e he
        · intro e he
          rw [hkeyeq]
          exact hbr e he
      · rename_i hgt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode hl (rightIH hr)
        · exact hbl
        · intro e he
          rcases mem_insertKeyWithCost_of_mem newEntry e right he with rfl | he
          · exact compareKey_gt hgt
          · exact hbr e he

/-- **Removing the minimum from an interval tree preserves key ordering.** Let $t$ be a
key-ordered interval tree. If the cost-instrumented removal of the leftmost entry of $t$ succeeds,
returning that entry, a remaining tree $t'$ and a cost, then $t'$ is key-ordered. -/
theorem keyOrdered_removeMinWithCost {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hord : tree.KeyOrdered) : rest.KeyOrdered := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact hord.2.1
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            apply keyOrdered_rebalance
            apply keyOrdered_mkNode (leftIH hev hord.1) hord.2.1
            · intro e he
              exact hord.2.2.1 e (mem_removeMinWithCost_of_mem hev e he)
            · exact hord.2.2.2

/-- **Deletion from an interval tree preserves key ordering.** Let $t$ be a key-ordered interval
tree and let $k \in \mathbb{Z} \times \mathbb{N}$ be a key. Then the tree returned by the
cost-instrumented keyed deletion of $k$ from $t$ (the reported cost is discarded) is again
key-ordered. -/
theorem keyOrdered_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (hord : tree.KeyOrdered) :
    (tree.eraseKeyWithCost key).1.KeyOrdered := by
  induction tree with
  | empty => exact hord
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, hr, hbl, hbr⟩ := hord
      unfold eraseKeyWithCost
      split
      · rename_i hlt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode (leftIH hl) hr
        · intro e he
          exact hbl e (mem_eraseKeyWithCost_of_mem key e left he)
        · exact hbr
      · rename_i hgt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode hl (rightIH hr)
        · exact hbl
        · intro e he
          exact hbr e (mem_eraseKeyWithCost_of_mem key e right he)
      · rename_i heq
        split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          exact hl
        · rename_i successor newRight childCost hsome
          apply keyOrdered_rebalance
          apply keyOrdered_mkNode hl
            (keyOrdered_removeMinWithCost hsome hr)
          · intro e he
            exact compareKey_lt_trans (hbl e he)
              (hbr successor (removeMinWithCost_min_mem hsome))
          · intro e he
            have hmem : e ∈ right.entries :=
              mem_removeMinWithCost_of_mem hsome e he
            have hne : e ≠ successor := fun hcon =>
              ((removeMinWithCost_spec hsome
                (keyNodup_of_keyOrdered hr)).2 e).mp he |>.2 hcon
            rcases removeMinWithCost_min_le hsome hr e hmem with rfl | hlt
            · exact absurd rfl hne
            · exact hlt

theorem height_mkNode (l r : Tree) (e : Entry) :
    (mkNode l e r).height = max l.height r.height + 1 := rfl

/-- **Rebalancing an interval-tree node with exact stored height restores AVL balance.** Let $L$
and $R$ be interval trees that are AVL balanced with exact stored heights, with heights $h_L$ and
$h_R$ satisfying $h_L \le h_R + 2$ and $h_R \le h_L + 2$. Let $N$ be a node with left subtree $L$,
entry $e$ and right subtree $R$ whose stored height is $\max(h_L, h_R) + 1$ (its stored size and
stored maximum are arbitrary), and let $B$ be the tree obtained by rebalancing $N$ (the tree
component of the result; the cost is ignored). Then $B$ is AVL balanced with exact stored heights,
the height of $B$ is $\max(h_L, h_R) + 1$ or $\max(h_L, h_R)$, and it is $\max(h_L, h_R)$ only if
$h_L = h_R + 2$ or $h_R = h_L + 2$. -/
theorem balancedProp_rebalance_node {sh ss : Nat} {mm : Int}
    {l : Tree} {e : Entry} {r : Tree}
    (hstored : sh = max l.height r.height + 1)
    (hl : l.BalancedProp) (hr : r.BalancedProp)
    (hbal : l.height ≤ r.height + 2 ∧ r.height ≤ l.height + 2) :
    (rebalanceWithCost (.node sh ss mm l e r)).1.BalancedProp ∧
      ((rebalanceWithCost (.node sh ss mm l e r)).1.height =
          max l.height r.height + 1 ∨
        (rebalanceWithCost (.node sh ss mm l e r)).1.height + 1 =
          max l.height r.height + 1) ∧
      ((rebalanceWithCost (.node sh ss mm l e r)).1.height + 1 =
          max l.height r.height + 1 →
        l.height = r.height + 2 ∨ r.height = l.height + 2) := by
  have hnode : (Tree.node sh ss mm l e r).height = sh := rfl
  by_cases leftHeavy : l.height > r.height + 1
  · have hl2 : l.height = r.height + 2 := by omega
    simp only [rebalanceWithCost, ite_eq_left leftHeavy]
    cases l with
    | empty =>
        simp only [height] at leftHeavy
        omega
    | node lsh lss lm ll x lr =>
        have hlH : (Tree.node lsh lss lm ll x lr).height =
            max ll.height lr.height + 1 := hl.1
        dsimp only
        by_cases hsub : ll.height ≥ lr.height
        · simp only [ite_eq_left hsub]
          simp only [rotateRight]
          have hmid : (mkNode lr e r).height =
              max lr.height r.height + 1 := rfl
          have hres : (mkNode ll x (mkNode lr e r)).height =
              max ll.height (mkNode lr e r).height + 1 := rfl
          obtain ⟨hsh, hle1, hle2, hllB, hlrB⟩ := hl
          rw [hlH]
          refine ⟨⟨rfl, by omega, by omega, hllB,
            ⟨rfl, by omega, by omega, hlrB, hr⟩⟩, by omega,
            fun _ => Or.inl (by omega)⟩
        · simp only [ite_eq_right hsub]
          cases lr with
          | empty =>
              simp only [height] at hsub
              omega
          | node bsh bss bm b y c =>
              have hlrH : (Tree.node bsh bss bm b y c).height =
                  max b.height c.height + 1 := hl.2.2.2.2.1
              obtain ⟨hsh, hle1, hle2, hllB, hlrB⟩ := hl
              obtain ⟨hlrSh, hble1, hble2, hbB, hcB⟩ := hlrB
              simp only [rotateLeftRight]
              have hL : (mkNode ll x b).height =
                  max ll.height b.height + 1 := rfl
              have hR : (mkNode c e r).height =
                  max c.height r.height + 1 := rfl
              have hres : (mkNode (mkNode ll x b) y (mkNode c e r)).height =
                  max (mkNode ll x b).height (mkNode c e r).height + 1 := rfl
              rw [hlH, hlrH]
              refine ⟨⟨rfl, by omega, by omega,
                ⟨rfl, by omega, by omega, hllB, hbB⟩,
                ⟨rfl, by omega, by omega, hcB, hr⟩⟩, by omega,
                fun _ => Or.inl (by omega)⟩
  · by_cases rightHeavy : r.height > l.height + 1
    · have hr2 : r.height = l.height + 2 := by omega
      simp only [rebalanceWithCost, ite_eq_right leftHeavy,
        ite_eq_left rightHeavy]
      cases r with
      | empty =>
          simp only [height] at rightHeavy
          omega
      | node rsh rss rm rl y rr =>
          have hrH : (Tree.node rsh rss rm rl y rr).height =
              max rl.height rr.height + 1 := hr.1
          dsimp only
          by_cases hsub : rr.height ≥ rl.height
          · simp only [ite_eq_left hsub]
            simp only [rotateLeft]
            have hmid : (mkNode l e rl).height =
                max l.height rl.height + 1 := rfl
            have hres : (mkNode (mkNode l e rl) y rr).height =
                max (mkNode l e rl).height rr.height + 1 := rfl
            obtain ⟨hsh, hre1, hre2, hrlB, hrrB⟩ := hr
            rw [hrH]
            refine ⟨⟨rfl, by omega, by omega,
              ⟨rfl, by omega, by omega, hl, hrlB⟩,
              hrrB⟩, by omega, fun _ => Or.inr (by omega)⟩
          · simp only [ite_eq_right hsub]
            cases rl with
            | empty =>
                simp only [height] at hsub
                omega
            | node bsh bss bm b z d =>
                have hrlH : (Tree.node bsh bss bm b z d).height =
                    max b.height d.height + 1 := hr.2.2.2.1.1
                obtain ⟨hsh, hre1, hre2, hrlB, hrrB⟩ := hr
                obtain ⟨hrlSh, hde1, hde2, hbB, hdB⟩ := hrlB
                simp only [rotateRightLeft]
                have hL : (mkNode l e b).height =
                    max l.height b.height + 1 := rfl
                have hR : (mkNode d y rr).height =
                    max d.height rr.height + 1 := rfl
                have hres : (mkNode (mkNode l e b) z (mkNode d y rr)).height =
                    max (mkNode l e b).height (mkNode d y rr).height + 1 := rfl
                rw [hrH, hrlH]
                refine ⟨⟨rfl, by omega, by omega,
                  ⟨rfl, by omega, by omega, hl, hbB⟩,
                  ⟨rfl, by omega, by omega, hdB, hrrB⟩⟩, by omega,
                  fun _ => Or.inr (by omega)⟩
    · simp only [rebalanceWithCost, ite_eq_right leftHeavy,
        ite_eq_right rightHeavy]
      refine ⟨⟨hstored, by omega, by omega, hl, hr⟩, Or.inl hstored,
        fun hdrop => by omega⟩

/-- **Rebalancing a rebuilt interval-tree node restores AVL balance.** Let $L$ and $R$ be interval
trees that are AVL balanced with exact stored heights, with heights $h_L$ and $h_R$ satisfying
$h_L \le h_R + 2$ and $h_R \le h_L + 2$, and let $e$ be an entry. Let $B$ be the tree obtained by
rebalancing the node that the smart constructor builds from $L$, $e$ and $R$ (the tree component
of the result; the cost is ignored). Then $B$ is AVL balanced with exact stored heights, the
height of $B$ is $\max(h_L, h_R) + 1$ or $\max(h_L, h_R)$, and it is $\max(h_L, h_R)$ only if
$h_L = h_R + 2$ or $h_R = h_L + 2$. -/
theorem balancedProp_rebalance_mkNode {l : Tree} {e : Entry} {r : Tree}
    (hl : l.BalancedProp) (hr : r.BalancedProp)
    (hbal : l.height ≤ r.height + 2 ∧ r.height ≤ l.height + 2) :
    (rebalanceWithCost (mkNode l e r)).1.BalancedProp ∧
      ((rebalanceWithCost (mkNode l e r)).1.height =
          max l.height r.height + 1 ∨
        (rebalanceWithCost (mkNode l e r)).1.height + 1 =
          max l.height r.height + 1) ∧
      ((rebalanceWithCost (mkNode l e r)).1.height + 1 =
          max l.height r.height + 1 →
        l.height = r.height + 2 ∨ r.height = l.height + 2) :=
  balancedProp_rebalance_node rfl hl hr hbal

/-- **Keyed insertion preserves AVL balance in an interval tree.** Let $T$ be an interval tree that
is AVL balanced with exact stored heights, and let $e$ be an entry. The tree $T'$ returned by keyed
insertion of $e$ into $T$ (which replaces an entry with the same key, if there is one; we take the
tree component of the result and ignore the cost) is again AVL balanced with exact stored heights,
and the height of $T'$ is either the height of $T$ or one more. -/
theorem balancedProp_insertKeyWithCost (newEntry : Entry) {tree : Tree}
    (hb : tree.BalancedProp) :
    (tree.insertKeyWithCost newEntry).1.BalancedProp ∧
      ((tree.insertKeyWithCost newEntry).1.height = tree.height ∨
        (tree.insertKeyWithCost newEntry).1.height = tree.height + 1) := by
  induction tree with
  | empty =>
      refine ⟨⟨rfl, by omega, by omega, trivial, trivial⟩, Or.inr rfl⟩
  | node sh ss mm left entry right leftIH rightIH =>
      obtain ⟨hsh, hle1, hle2, hlB, hrB⟩ := hb
      have hnode : (Tree.node sh ss mm left entry right).height = sh := rfl
      unfold insertKeyWithCost
      split
      · obtain ⟨ihB, ihH⟩ := leftIH hlB
        have hres := balancedProp_rebalance_mkNode (e := entry) ihB hrB
          ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode (insertKeyWithCost newEntry left).1
            entry right)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode (insertKeyWithCost newEntry left).1
            entry right)).1.height =
            (Tree.node sh ss mm left entry right).height + 1
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega
      · refine ⟨⟨rfl, hle1, hle2, hlB, hrB⟩, Or.inl ?_⟩
        have hmk : (mkNode left newEntry right).height =
            max left.height right.height + 1 := rfl
        rw [hmk]
        exact hsh.symm
      · obtain ⟨ihB, ihH⟩ := rightIH hrB
        have hres := balancedProp_rebalance_mkNode (e := entry) hlB ihB ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode left entry
            (insertKeyWithCost newEntry right).1)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode left entry
            (insertKeyWithCost newEntry right).1)).1.height =
            (Tree.node sh ss mm left entry right).height + 1
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega

/-- **Removing the minimum preserves AVL balance in an interval tree.** Let $T$ be an interval tree
that is AVL balanced with exact stored heights. If removing the leftmost entry of $T$ succeeds and
returns an entry $m$, a remaining tree $R$ and a cost $c$, then $R$ is AVL balanced with exact
stored heights, and the height of $R$ is either the height of $T$ or one less. -/
theorem balancedProp_removeMinWithCost {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hb : tree.BalancedProp) :
    rest.BalancedProp ∧
      (rest.height = tree.height ∨ rest.height + 1 = tree.height) := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node sh ss mm left entry right leftIH _ =>
      obtain ⟨hsh, hle1, hle2, hlB, hrB⟩ := hb
      have hnode : (Tree.node sh ss mm left entry right).height = sh := rfl
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          refine ⟨hrB, Or.inr ?_⟩
          have hempty : (Tree.empty : Tree).height = 0 := rfl
          omega
      | node lsh lss lm ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            obtain ⟨ihB, ihH⟩ := leftIH hev hlB
            have hres := balancedProp_rebalance_mkNode (e := entry) ihB hrB ⟨by omega, by omega⟩
            refine ⟨hres.1, ?_⟩
            have hlH : (Tree.node lsh lss lm ll le lr).height =
                max ll.height lr.height + 1 := hlB.1
            rcases hres.2.1 with hh | hh
            · rcases ihH with ih | ih <;> omega
            · have hvy := hres.2.2 hh
              rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega

/-- **Keyed deletion preserves AVL balance in an interval tree.** Let $T$ be an interval tree that
is AVL balanced with exact stored heights, and let $k$ be a key (a pair of an integer low endpoint
and a natural-number identifier). The tree $T'$ returned by keyed deletion of $k$ from $T$ (the
tree component of the result; the cost is ignored) is again AVL balanced with exact stored
heights, and the height of $T'$ is either the height of $T$ or one less. -/
theorem balancedProp_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (hb : tree.BalancedProp) :
    (tree.eraseKeyWithCost key).1.BalancedProp ∧
      ((tree.eraseKeyWithCost key).1.height = tree.height ∨
        (tree.eraseKeyWithCost key).1.height + 1 = tree.height) := by
  induction tree with
  | empty => exact ⟨hb, Or.inl rfl⟩
  | node sh ss mm left entry right leftIH rightIH =>
      obtain ⟨hsh, hle1, hle2, hlB, hrB⟩ := hb
      have hnode : (Tree.node sh ss mm left entry right).height = sh := rfl
      unfold eraseKeyWithCost
      split
      · obtain ⟨ihB, ihH⟩ := leftIH hlB
        have hres := balancedProp_rebalance_mkNode (e := entry) ihB hrB
          ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode (eraseKeyWithCost key left).1
            entry right)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode (eraseKeyWithCost key left).1
            entry right)).1.height + 1 =
            (Tree.node sh ss mm left entry right).height
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega
      · obtain ⟨ihB, ihH⟩ := rightIH hrB
        have hres := balancedProp_rebalance_mkNode (e := entry) hlB ihB ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode left entry
            (eraseKeyWithCost key right).1)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode left entry
            (eraseKeyWithCost key right).1)).1.height + 1 =
            (Tree.node sh ss mm left entry right).height
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega
      · split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          refine ⟨hlB, Or.inr ?_⟩
          change left.height + 1 =
            (Tree.node sh ss mm left entry Tree.empty).height
          have hempty : (Tree.empty : Tree).height = 0 := rfl
          omega
        · rename_i successor newRight childCost hsome
          obtain ⟨rmB, rmH⟩ := balancedProp_removeMinWithCost hsome hrB
          have hres := balancedProp_rebalance_mkNode (e := successor) hlB rmB ⟨by omega, by omega⟩
          refine ⟨hres.1, ?_⟩
          change (rebalanceWithCost (mkNode left successor newRight)).1.height =
              (Tree.node sh ss mm left entry right).height ∨
            (rebalanceWithCost (mkNode left successor newRight)).1.height + 1 =
              (Tree.node sh ss mm left entry right).height
          rcases hres.2.1 with h | h
          · rcases rmH with ih | ih <;> omega
          · have hvy := hres.2.2 h
            rcases rmH with ih | ih <;> rcases hvy with hv | hv <;> omega

/-- **Node construction preserves interval validity.** If $L$ and $R$ are interval trees
satisfying the validity invariant and $e$ is an entry whose interval $[a, b]$ satisfies
$a \le b$, then the node with left subtree $L$, entry $e$ and right subtree $R$, built by the
node constructor that recomputes the cached fields, satisfies the validity invariant. -/
theorem validInvariant_mkNode {left right : Tree} {entry : Entry}
    (hl : left.ValidInvariant) (he : entry.interval.Valid)
    (hr : right.ValidInvariant) :
    (mkNode left entry right).ValidInvariant :=
  ⟨hl, he, hr⟩

theorem validInvariant_rotateRight {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateRight.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact hv
      | node _ _ _ a x b =>
          obtain ⟨⟨hva, hx, hvb⟩, hy, hvc⟩ := hv
          exact validInvariant_mkNode hva hx
            (validInvariant_mkNode hvb hy hvc)

theorem validInvariant_rotateLeft {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateLeft.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact hv
      | node _ _ _ b y c =>
          obtain ⟨hl, hx, ⟨hvb, hy, hvc⟩⟩ := hv
          exact validInvariant_mkNode
            (validInvariant_mkNode hl hx hvb) hy hvc

theorem validInvariant_rotateLeftRight {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateLeftRight.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact hv
      | node _ _ _ a x lr =>
          cases lr with
          | empty => exact hv
          | node _ _ _ b y c =>
              obtain ⟨⟨hva, hx, ⟨hvb, hy, hvc⟩⟩, he, hr⟩ := hv
              exact validInvariant_mkNode
                (validInvariant_mkNode hva hx hvb) hy
                (validInvariant_mkNode hvc he hr)

theorem validInvariant_rotateRightLeft {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateRightLeft.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact hv
      | node _ _ _ rl y c =>
          cases rl with
          | empty => exact hv
          | node _ _ _ b z d =>
              obtain ⟨hl, he, ⟨⟨hvb, hz, hvd⟩, hy, hvc⟩⟩ := hv
              exact validInvariant_mkNode
                (validInvariant_mkNode hl he hvb) hz
                (validInvariant_mkNode hvd hy hvc)

theorem validInvariant_rebalanceWithCost {tree : Tree}
    (hv : tree.ValidInvariant) :
    (tree.rebalanceWithCost).1.ValidInvariant := by
  unfold rebalanceWithCost
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | exact hv
      | exact validInvariant_rotateRight hv
      | exact validInvariant_rotateLeft hv
      | exact validInvariant_rotateLeftRight hv
      | exact validInvariant_rotateRightLeft hv

/-- **Stored intervals of a valid tree are valid.** If an interval tree $T$ satisfies the validity
invariant, then every entry stored in $T$ has an interval $[a, b]$ with $a \le b$. -/
theorem validInvariant_mem {tree : Tree} (hv : tree.ValidInvariant)
    (e : Entry) (he : e ∈ tree.entries) : e.interval.Valid := by
  induction tree with
  | empty => simp [entries] at he
  | node _ _ _ l en r lIH rIH =>
      obtain ⟨hl, hen, hr⟩ := hv
      simp only [entries, List.mem_append, List.mem_cons] at he
      rcases he with he | rfl | he
      · exact lIH hl he
      · exact hen
      · exact rIH hr he

/-- **Keyed insertion preserves interval validity.** Let $T$ be an interval tree in which every
stored interval $[a, b]$ satisfies $a \le b$, and let $e$ be an entry whose interval $[a, b]$
satisfies $a \le b$. Then the tree returned by keyed insertion of $e$ into $T$ also has every
stored interval $[a, b]$ satisfying $a \le b$. -/
theorem validInvariant_insertKeyWithCost (newEntry : Entry)
    (hnew : newEntry.interval.Valid) {tree : Tree}
    (hv : tree.ValidInvariant) :
    (tree.insertKeyWithCost newEntry).1.ValidInvariant := by
  induction tree with
  | empty => exact validInvariant_mkNode trivial hnew trivial
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, he, hr⟩ := hv
      unfold insertKeyWithCost
      split
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode (leftIH hl) he hr)
      · exact validInvariant_mkNode hl hnew hr
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode hl he (rightIH hr))

/-- **Removing the minimum preserves interval validity.** Let $T$ be an interval tree in which
every stored interval is valid (its low endpoint is at most its high endpoint). If the
instrumented removal of the leftmost entry of $T$ succeeds, returning that entry $m$, the
remaining tree $T'$ and a cost record $c$, then every interval stored in $T'$ is valid. -/
theorem validInvariant_removeMinWithCost {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hv : tree.ValidInvariant) : rest.ValidInvariant := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact hv.2.2
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            exact validInvariant_rebalanceWithCost
              (validInvariant_mkNode (leftIH hev hv.1) hv.2.1 hv.2.2)

/-- **Keyed erasure preserves interval validity.** Let $T$ be an interval tree in which every
stored interval $[a, b]$ satisfies $a \le b$. Then for every key $(\ell, i)$ with $\ell$ an
integer and $i$ a natural number, the tree returned by keyed erasure of $(\ell, i)$ from $T$ also
has every stored interval $[a, b]$ satisfying $a \le b$. -/
theorem validInvariant_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (hv : tree.ValidInvariant) :
    (tree.eraseKeyWithCost key).1.ValidInvariant := by
  induction tree with
  | empty => exact hv
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, he, hr⟩ := hv
      unfold eraseKeyWithCost
      split
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode (leftIH hl) he hr)
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode hl he (rightIH hr))
      · split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          exact hl
        · rename_i successor newRight childCost hsome
          exact validInvariant_rebalanceWithCost
            (validInvariant_mkNode hl
              (validInvariant_mem hr successor
                (removeMinWithCost_min_mem hsome))
              (validInvariant_removeMinWithCost hsome hr))

end Tree
/-- **Indexed interval tree.** An indexed interval tree consists of a root interval tree together
with an identifier index: a finite map, implemented as a balanced search tree, from natural-number
identifiers to integer low endpoints. -/
structure IndexedIntervalTree where
  root : Tree
  idIndex : Std.TreeMap Nat Int



namespace IndexedIntervalTree

def empty : IndexedIntervalTree :=
  ⟨.empty, .empty⟩

/-- **Insertion by identifier with cost.** Let $T$ be an indexed interval tree and let $e$ be an
entry with identifier $i$ and interval $[a, b]$. Inserting $e$ into $T$ first tests $a \le b$. If
$a > b$, it returns no tree, at a cost of one endpoint comparison. Otherwise, if the identifier
index of $T$ maps $i$ to a low endpoint $\ell$, the entry with key $(\ell, i)$ is erased from the
root tree of $T$ by keyed erasure; if $i$ is not in the index, the root tree is kept, at zero
cost. Then $e$ is inserted into the resulting tree by keyed insertion. The result is the indexed
interval tree with this new root tree and with the index updated to map $i$ to $a$, and the cost
is the cost of the erasure plus the cost of the insertion plus one endpoint comparison and two
index operations. -/
def insertWithCost
    (tree : IndexedIntervalTree) (entry : Entry) : Option IndexedIntervalTree × Cost :=
  if entry.interval.valid then
    let (withoutOld, eraseCost) :=
      match tree.idIndex.get? entry.id with
      | none => (tree.root, ({} : Cost))
      | some oldLow => tree.root.eraseKeyWithCost (oldLow, entry.id)
    let (newRoot, insertCost) := withoutOld.insertKeyWithCost entry
    (some ⟨newRoot, tree.idIndex.insert entry.id entry.interval.low⟩,
      eraseCost + insertCost +
        { endpointComparisons := 1, indexOperations := 2 })
  else
    (none, { endpointComparisons := 1 })

def insert (tree : IndexedIntervalTree) (entry : Entry) : Option IndexedIntervalTree :=
  (tree.insertWithCost entry).1

/-- **Erasure by identifier with cost.** To erase identifier $i$ from an indexed interval tree,
look $i$ up in the identifier index. If it is absent, the tree is returned unchanged at a cost of
one index operation. If the index maps $i$ to a low endpoint $\ell$, the entry with key
$(\ell, i)$ is erased from the underlying interval tree, $i$ is removed from the index, and the
cost is the cost of the keyed erasure plus two index operations.

When the representation invariant holds, this deletes exactly the stored entry with identifier
$i$. -/
def eraseWithCost (tree : IndexedIntervalTree) (id : Nat) : IndexedIntervalTree × Cost :=
  match tree.idIndex.get? id with
  | none => (tree, { indexOperations := 1 })
  | some low =>
      let (newRoot, eraseCost) := tree.root.eraseKeyWithCost (low, id)
      (⟨newRoot, tree.idIndex.erase id⟩,
        eraseCost + { indexOperations := 2 })

def erase (tree : IndexedIntervalTree) (id : Nat) : IndexedIntervalTree :=
  (tree.eraseWithCost id).1

def searchWithCost
    (tree : IndexedIntervalTree) (query : Interval) : Option Entry × Cost :=
  if query.valid then
    let (answer, cost) := tree.root.searchWithCost query
    (answer, cost + { endpointComparisons := 1 })
  else (none, { endpointComparisons := 1 })

def search (tree : IndexedIntervalTree) (query : Interval) : Option Entry :=
  (tree.searchWithCost query).1

def oracleSearch (tree : IndexedIntervalTree) (query : Interval) : Option Entry :=
  if query.valid then tree.root.oracleSearch query else none

/-- **Forward identifier-index check.** For an indexed interval tree, the forward index check
returns true exactly when the identifier index maps the identifier of every stored entry to the low
endpoint of that entry's interval. -/
def indexForwardOK (tree : IndexedIntervalTree) : Bool :=
  tree.root.entries.all fun entry =>
    tree.idIndex.get? entry.id == some entry.interval.low

/-- **Backward identifier-index check.** For an indexed interval tree, the backward index check
returns true exactly when, for every identifier $i$ that the identifier index maps to a low endpoint
$\ell$, some stored entry has identifier $i$ and an interval with low endpoint $\ell$. -/
def indexBackwardOK (tree : IndexedIntervalTree) : Bool :=
  tree.idIndex.toList.all fun pair =>
    tree.root.entries.any fun entry =>
      entry.id == pair.1 && entry.interval.low == pair.2

/-- **Representation check for the indexed interval tree.** For an indexed interval tree, the
check returns true exactly when all of the following hold: at every node the cached height and size
agree with the values recomputed from its children's cached heights and sizes, and the cached
maximum high endpoint equals the largest of the node's own high endpoint and its children's cached
maxima; the tree is AVL-balanced (sibling heights differ by at most one) with exact stored heights;
the entry keys (low endpoint, identifier), ordered lexicographically, are strictly ordered as a
binary search tree and every stored interval has low endpoint at most its high endpoint; the
identifiers of the stored entries are pairwise distinct; the identifier index maps the identifier of
every stored entry to that entry's low endpoint; and every identifier and low endpoint paired by the
index belong to some stored entry. -/
def check (tree : IndexedIntervalTree) : Bool :=
  tree.root.cacheOK && tree.root.balanced &&
    tree.root.orderedValid none none && tree.root.uniqueIds &&
    tree.indexForwardOK && tree.indexBackwardOK

/-- **Representation invariant of an indexed interval tree.** An indexed interval tree $T$
satisfies the representation invariant when its root tree has exact cached metadata (heights,
sizes, and attained maximum high endpoints), is strictly ordered by the composite key (low
endpoint, then identifier), is AVL balanced with exact stored heights, and stores only valid
intervals; the identifiers of the stored entries are pairwise distinct; the identifier index maps
the identifier of every stored entry to that entry's low endpoint; and every pair $(i, \ell)$ in
the identifier index is the identifier and low endpoint of some stored entry.

The ordering of low endpoints used by search follows from the strict key ordering. -/
def Invariant (tree : IndexedIntervalTree) : Prop :=
  tree.root.CacheInvariant ∧ tree.root.KeyOrdered ∧ tree.root.BalancedProp ∧
    tree.root.ValidInvariant ∧
    (tree.root.entries.map (·.id)).Nodup ∧
    (∀ e ∈ tree.root.entries, tree.idIndex.get? e.id = some e.interval.low) ∧
    ∀ p ∈ tree.idIndex.toList,
      ∃ e ∈ tree.root.entries, e.id = p.1 ∧ e.interval.low = p.2

end IndexedIntervalTree

end Cslib.Algorithms.Lean.IntervalTree

namespace Cslib.Algorithms.Lean.IntervalTree.Tree

private theorem le_maxWith (fallback : Int) (tree : Tree) :
    fallback ≤ maxWith fallback tree.cachedMax? := by
  cases tree <;> simp [maxWith, cachedMax?]

private theorem high_le_maxWith {tree : Tree} (cache : tree.CacheInvariant)
    {stored : Entry} (member : stored ∈ tree.entries) (fallback : Int) :
    stored.interval.high ≤ maxWith fallback tree.cachedMax? := by
  cases tree with
  | empty => simp [entries] at member
  | node height size maxHigh left entry right =>
      exact le_trans (cache.2.2.1 stored member) (le_max_right _ _)

private theorem maxWith_attained {tree : Tree} (cache : tree.CacheInvariant)
    (fallback : Int) :
    maxWith fallback tree.cachedMax? = fallback ∨
      ∃ stored ∈ tree.entries,
        stored.interval.high = maxWith fallback tree.cachedMax? := by
  cases tree with
  | empty => exact Or.inl rfl
  | node height size maxHigh left entry right =>
      by_cases bounded : maxHigh ≤ fallback
      · exact Or.inl (max_eq_left bounded)
      · rcases cache.2.2.2.1 with ⟨stored, member, attained⟩
        exact Or.inr ⟨stored, member, by
          simpa only [cachedMax?, maxWith, max_eq_right (le_of_not_ge bounded)] using
            attained⟩

/-- **The interval-tree smart constructor preserves the cache invariant.** If interval trees $L$
and $R$ satisfy the cache invariant (every cached maximum high endpoint, height and size is
exact), then for every entry $e$ the node that the smart constructor builds from $L$, $e$ and $R$
also satisfies the cache invariant. -/
theorem cacheInvariant_mkNode {left right : Tree} (entry : Entry)
    (leftCache : left.CacheInvariant) (rightCache : right.CacheInvariant) :
    (mkNode left entry right).CacheInvariant := by
  refine ⟨leftCache, rightCache, ?_, ?_, rfl, rfl⟩
  · intro stored member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with inLeft | atRoot | inRight
    · exact le_trans (high_le_maxWith leftCache inLeft entry.interval.high)
        (le_maxWith _ right)
    · subst stored
      exact le_trans (le_maxWith entry.interval.high left) (le_maxWith _ right)
    · exact high_le_maxWith rightCache inRight _
  · rcases maxWith_attained rightCache (maxWith entry.interval.high left.cachedMax?) with
      rootOrLeft | ⟨stored, member, attained⟩
    · rcases maxWith_attained leftCache entry.interval.high with
        atRoot | ⟨stored, member, attained⟩
      · exact ⟨entry, by simp, (rootOrLeft.trans atRoot).symm⟩
      · exact ⟨stored, by simp [member], attained.trans rootOrLeft.symm⟩
    · exact ⟨stored, by simp [member], attained⟩

/-- **The executable cache check implies the cache invariant.** If the executable cache check
returns true on an interval tree $t$, then $t$ satisfies the cache invariant. -/
theorem cacheInvariant_of_cacheOK {tree : Tree} (checked : tree.cacheOK = true) :
    tree.CacheInvariant := by
  induction tree with
  | empty => trivial
  | node height size maxHigh left entry right leftIH rightIH =>
      simp only [cacheOK, Bool.and_eq_true, beq_iff_eq] at checked
      have leftOK : left.cacheOK = true := checked.1.2
      have rightOK : right.cacheOK = true := checked.2
      have maximum : maxHigh = nodeMax left entry right := checked.1.1.2
      have heightEq : height = max left.height right.height + 1 := checked.1.1.1.1
      have sizeEq : size = left.size + right.size + 1 := checked.1.1.1.2
      have rebuilt := cacheInvariant_mkNode entry (leftIH leftOK) (rightIH rightOK)
      simpa only [mkNode, CacheInvariant, maximum, ← heightEq, ← sizeEq] using rebuilt

/-- **Right rotation preserves the interval-tree cache invariant.** If an interval tree $t$
satisfies the cache invariant, then so does the right rotation of $t$, which leaves $t$ unchanged
when $t$ is empty or has an empty left subtree. -/
theorem cacheInvariant_rotateRight {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateRight.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases left with
      | empty => exact cache
      | node leftHeight leftSize leftMaximum a x b =>
          exact cacheInvariant_mkNode x cache.1.1
            (cacheInvariant_mkNode entry cache.1.2.1 cache.2.1)

/-- **Left rotation preserves the interval-tree cache invariant.** If an interval tree $t$
satisfies the cache invariant, then so does the left rotation of $t$, which leaves $t$ unchanged
when $t$ is empty or has an empty right subtree. -/
theorem cacheInvariant_rotateLeft {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateLeft.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases right with
      | empty => exact cache
      | node rightHeight rightSize rightMaximum b y c =>
          exact cacheInvariant_mkNode y
            (cacheInvariant_mkNode entry cache.1 cache.2.1.1) cache.2.1.2.1

/-- **Left-right rotation preserves the interval-tree cache invariant.** If an interval tree $t$
satisfies the cache invariant, then so does the left-right double rotation of $t$, which leaves
$t$ unchanged unless $t$ has a nonempty left subtree whose right subtree is nonempty. -/
theorem cacheInvariant_rotateLeftRight {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateLeftRight.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases left with
      | empty => exact cache
      | node leftHeight leftSize leftMaximum a x middle =>
          cases middle with
          | empty => exact cache
          | node middleHeight middleSize middleMaximum b y c =>
              exact cacheInvariant_mkNode y
                (cacheInvariant_mkNode x cache.1.1 cache.1.2.1.1)
                (cacheInvariant_mkNode entry cache.1.2.1.2.1 cache.2.1)

/-- **Right-left rotation preserves the interval-tree cache invariant.** If an interval tree $t$
satisfies the cache invariant, then so does the right-left double rotation of $t$, which leaves
$t$ unchanged unless $t$ has a nonempty right subtree whose left subtree is nonempty. -/
theorem cacheInvariant_rotateRightLeft {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateRightLeft.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases right with
      | empty => exact cache
      | node rightHeight rightSize rightMaximum middle z d =>
          cases middle with
          | empty => exact cache
          | node middleHeight middleSize middleMaximum b y c =>
              exact cacheInvariant_mkNode y
                (cacheInvariant_mkNode entry cache.1 cache.2.1.1.1)
                (cacheInvariant_mkNode z cache.2.1.1.2.1 cache.2.1.2.1)

/-- **Rebalancing preserves the interval-tree cache invariant.** If an interval tree $t$
satisfies the cache invariant, then the tree returned by the rebalancing step at the root of $t$
also satisfies the cache invariant. -/
theorem cacheInvariant_rebalanceWithCost {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rebalanceWithCost.1.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      by_cases leftHeavy : left.height > right.height + 1
      · simp only [rebalanceWithCost, ite_eq_left leftHeavy]
        cases left with
        | empty => exact cache
        | node leftHeight leftSize leftMaximum ll x lr =>
            dsimp only
            split
            · exact cacheInvariant_rotateRight cache
            · exact cacheInvariant_rotateLeftRight cache
      · simp only [rebalanceWithCost, ite_eq_right leftHeavy]
        by_cases rightHeavy : right.height > left.height + 1
        · simp only [ite_eq_left rightHeavy]
          cases right with
          | empty => exact cache
          | node rightHeight rightSize rightMaximum rl x rr =>
              dsimp only
              split
              · exact cacheInvariant_rotateLeft cache
              · exact cacheInvariant_rotateRightLeft cache
        · simpa only [ite_eq_right rightHeavy] using cache

/-- **Keyed insertion preserves the interval-tree cache invariant.** Let $T$ be an interval tree
satisfying the cache invariant (every cached maximum high endpoint, height and size is exact), and
let $e$ be an entry. The tree returned by keyed insertion of $e$ into $T$ (the tree component of
the result; the cost is ignored) also satisfies the cache invariant. This includes the case where
an entry with the same key is replaced. -/
theorem cacheInvariant_insertKeyWithCost (newEntry : Entry) {tree : Tree}
    (cache : tree.CacheInvariant) :
    (tree.insertKeyWithCost newEntry).1.CacheInvariant := by
  induction tree with
  | empty => exact cacheInvariant_mkNode newEntry trivial trivial
  | node height size maximum left entry right leftIH rightIH =>
      unfold insertKeyWithCost
      split
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry (leftIH cache.1) cache.2.1)
      · exact cacheInvariant_mkNode newEntry cache.1 cache.2.1
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry cache.1 (rightIH cache.2.1))

/-- **Removing the minimum preserves the interval-tree cache invariant.** Let $t$ be an interval
tree that satisfies the cache invariant. If removing the leftmost entry of $t$ succeeds and
returns an entry, a tree $t'$ and an operation cost, then $t'$ satisfies the cache invariant. -/
theorem cacheInvariant_removeMinWithCost {tree : Tree} (cache : tree.CacheInvariant) :
    ∀ {minimum : Entry} {result : Tree} {cost : Cost},
      tree.removeMinWithCost = some (minimum, result, cost) → result.CacheInvariant := by
  induction tree with
  | empty =>
      intro minimum result cost returned
      simp only [removeMinWithCost, reduceCtorEq] at returned
  | node height size maximum left entry right leftIH rightIH =>
      intro minimum result cost returned
      cases left with
      | empty =>
          change some (entry, right, ({ nodeVisits := 1 } : Cost)) =
            some (minimum, result, cost) at returned
          cases returned
          exact cache.2.1
      | node leftHeight leftSize leftMaximum a x b =>
          unfold removeMinWithCost at returned
          split at returned
          · contradiction
          · rename_i removed newLeft childCost recursive
            cases returned
            exact cacheInvariant_rebalanceWithCost
              (cacheInvariant_mkNode entry (leftIH cache.1 recursive) cache.2.1)

/-- **Keyed deletion preserves the interval-tree cache invariant.** Let $T$ be an interval tree
satisfying the cache invariant (every cached maximum high endpoint, height and size is exact), and
let $k$ be a key (a pair of an integer low endpoint and a natural-number identifier). The tree
returned by keyed deletion of $k$ from $T$ (the tree component of the result; the cost is
ignored) also satisfies the cache invariant. This includes keys that do not occur in $T$. -/
theorem cacheInvariant_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (cache : tree.CacheInvariant) : (tree.eraseKeyWithCost key).1.CacheInvariant := by
  induction tree with
  | empty => exact cache
  | node height size maximum left entry right leftIH rightIH =>
      unfold eraseKeyWithCost
      split
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry (leftIH cache.1) cache.2.1)
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry cache.1 (rightIH cache.2.1))
      · split
        · exact cache.1
        · rename_i successor newRight childCost removed
          exact cacheInvariant_rebalanceWithCost
            (cacheInvariant_mkNode successor cache.1
              (cacheInvariant_removeMinWithCost cache.2.1 removed))

end Cslib.Algorithms.Lean.IntervalTree.Tree

namespace Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree

/-- **Soundness of the invariant checker.** If the executable checker returns true on an indexed
interval tree $T$, then $T$ satisfies the representation invariant. -/
theorem invariant_of_check {tree : IndexedIntervalTree}
    (h : tree.check = true) : tree.Invariant := by
  simp only [check, Bool.and_eq_true] at h
  have hcache := h.1.1.1.1.1
  have hbal := h.1.1.1.1.2
  have hord := h.1.1.1.2
  have huniq := h.1.1.2
  have hfwd := h.1.2
  have hbwd := h.2
  refine ⟨Tree.cacheInvariant_of_cacheOK hcache,
    (Tree.keyOrdered_of_orderedValid hord).1,
    Tree.balancedProp_of_balanced hbal,
    Tree.validInvariant_of_orderedValid hord, ?_, ?_, ?_⟩
  · simpa [Tree.uniqueIds] using huniq
  · intro e he
    have := List.all_eq_true.mp hfwd e he
    simpa using this
  · intro p hp
    have := List.all_eq_true.mp hbwd p hp
    simp only [List.any_eq_true] at this
    obtain ⟨e, he, hboth⟩ := this
    simp only [Bool.and_eq_true, beq_iff_eq] at hboth
    exact ⟨e, he, hboth.1, hboth.2⟩

theorem empty_invariant : Invariant empty := by
  refine ⟨trivial, trivial, trivial, trivial, by decide, ?_, ?_⟩
  · intro e he
    change e ∈ ([] : List Entry) at he
    cases he
  · intro p hp
    change p ∈ ([] : List (Nat × Int)) at hp
    cases hp

/-- **Soundness of indexed interval-tree search.** The search of an indexed interval tree $T$ for
a query interval $q = [c, d]$ returns nothing when $c > d$, and otherwise returns the entry, if
any, found by the instrumented overlap search of $q$ in the root tree of $T$. For every indexed
interval tree $T$, every query interval $q$ and every entry $e$, if this search returns $e$, then
$e$ is one of the entries stored in the root tree of $T$ and the interval of $e$ overlaps $q$.

The representation invariant of $T$ is not needed. -/
theorem search_sound {tree : IndexedIntervalTree}
    {query : Interval} {found : Entry}
    (h : tree.search query = some found) :
    found ∈ tree.root.entries ∧ found.interval.Overlaps query := by
  have hroot : tree.root.search query = some found := by
    by_cases hv : query.valid
    · have : tree.search query = tree.root.search query := by
        simp [search, searchWithCost, hv, Tree.searchWithCost_fst]
      rwa [this] at h
    · simp [search, searchWithCost, hv] at h
  have hsound := Tree.search_sound hroot
  exact ⟨hsound.1, Interval.overlaps_eq_true.mp hsound.2⟩

/-- **Completeness of indexed interval search.** Let $T$ be an indexed interval tree satisfying
its representation invariant, and let $Q$ be a valid query interval (low endpoint at most high
endpoint). If some entry stored in $T$ has an interval that overlaps $Q$ (each interval's low
endpoint is at most the other's high endpoint), then searching $T$ for $Q$ returns some entry. -/
theorem search_complete_of_invariant {tree : IndexedIntervalTree}
    (inv : tree.Invariant) {query : Interval} (hvalid : query.valid = true)
    {witness : Entry} (member : witness ∈ tree.root.entries)
    (overlap : witness.interval.Overlaps query) :
    ∃ found, tree.search query = some found := by
  rcases Tree.search_complete inv.1 (Tree.keyOrdered_lowOrdered inv.2.1)
    member overlap with ⟨found, hfound⟩
  refine ⟨found, ?_⟩
  have : tree.search query = tree.root.search query := by
    simp [search, searchWithCost, hvalid, Tree.searchWithCost_fst]
  rwa [this]

private theorem get?_insert_self (m : Std.TreeMap Nat Int) (k : Nat)
    (v : Int) : (m.insert k v).get? k = some v :=
  Std.TreeMap.getElem?_insert_self

private theorem get?_insert_of_ne {m : Std.TreeMap Nat Int} {k a : Nat}
    (h : k ≠ a) (v : Int) : (m.insert k v).get? a = m.get? a := by
  change (m.insert k v)[a]? = m[a]?
  rw [Std.TreeMap.getElem?_insert]
  simp [h]

private theorem get?_erase_of_ne {m : Std.TreeMap Nat Int} {k a : Nat}
    (h : k ≠ a) : (m.erase k).get? a = m.get? a := by
  change (m.erase k)[a]? = m[a]?
  rw [Std.TreeMap.getElem?_erase]
  simp [h]

private theorem mem_toList_iff_get? {m : Std.TreeMap Nat Int}
    {p : Nat × Int} : p ∈ m.toList ↔ m.get? p.1 = some p.2 :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- One insertion stage: inserting a valid entry whose identifier is
absent from a tree satisfying the tree-level invariants and the index
correspondence yields a tree satisfying the bundled invariant, contains
the new entry, and otherwise retains exactly the old entries. -/
private theorem insert_stage {root : Tree} {index : Std.TreeMap Nat Int}
    {entry : Entry}
    (hcache : root.CacheInvariant) (hord : root.KeyOrdered)
    (hbal : root.BalancedProp) (hval : root.ValidInvariant)
    (hnoid : (root.entries.map (·.id)).Nodup)
    (hfwd : ∀ e ∈ root.entries, index.get? e.id = some e.interval.low)
    (hbwd : ∀ p ∈ index.toList, p.1 ≠ entry.id →
      ∃ e ∈ root.entries, e.id = p.1 ∧ e.interval.low = p.2)
    (hvalidProp : entry.interval.Valid)
    (habsent : ∀ e ∈ root.entries, e.id ≠ entry.id) :
    (⟨(root.insertKeyWithCost entry).1,
      index.insert entry.id entry.interval.low⟩ :
        IndexedIntervalTree).Invariant ∧
      entry ∈ (root.insertKeyWithCost entry).1.entries ∧
      ∀ e, e ∈ (root.insertKeyWithCost entry).1.entries ↔
        e = entry ∨ (e ∈ root.entries ∧ e.id ≠ entry.id) := by
  have hkeyNodup : (root.entries.map Entry.key).Nodup :=
    Tree.keyNodup_of_keyOrdered hord
  have hmem : ∀ e, e ∈ (root.insertKeyWithCost entry).1.entries ↔
      e = entry ∨ (e ∈ root.entries ∧ e.key ≠ entry.key) :=
    fun e => Tree.mem_insertKeyWithCost entry e hkeyNodup hord
  have hperm := Tree.insertKeyWithCost_entries_perm entry hord
  have hfilterNodup :
      ((root.entries.filter (fun e => e.key ≠ entry.key)).map (·.id)).Nodup :=
    (List.filter_sublist.map (fun e : Entry => e.id)).nodup hnoid
  have hnoid' :
      ((root.insertKeyWithCost entry).1.entries.map (·.id)).Nodup := by
    apply (hperm.map (·.id)).nodup_iff.mpr
    rw [List.map_cons]
    apply List.nodup_cons.mpr
    refine ⟨fun hmem => ?_, hfilterNodup⟩
    rw [List.mem_map] at hmem
    obtain ⟨e, he, hid⟩ := hmem
    rw [List.mem_filter] at he
    exact habsent e he.1 hid
  refine ⟨⟨Tree.cacheInvariant_insertKeyWithCost entry hcache,
    Tree.keyOrdered_insertKeyWithCost entry hord,
    (Tree.balancedProp_insertKeyWithCost entry hbal).1,
    Tree.validInvariant_insertKeyWithCost entry hvalidProp hval,
    hnoid', ?_, ?_⟩, (hmem entry).mpr (Or.inl rfl), ?_⟩
  · intro e he
    rcases (hmem e).mp he with heq | ⟨hem, _⟩
    · rw [heq]
      exact get?_insert_self index entry.id entry.interval.low
    · rw [get?_insert_of_ne (k := entry.id)
        (Ne.symm (habsent e hem)) entry.interval.low]
      exact hfwd e hem
  · intro p hp
    have hpget : (index.insert entry.id entry.interval.low).get? p.1 =
        some p.2 := mem_toList_iff_get?.mp hp
    by_cases hpe : p.1 = entry.id
    · have hlow : p.2 = entry.interval.low := by
        rw [hpe, get?_insert_self] at hpget
        exact Option.some.inj hpget.symm
      exact ⟨entry, (hmem entry).mpr (Or.inl rfl), hpe.symm, hlow.symm⟩
    · have hold : index.get? p.1 = some p.2 := by
        rw [← get?_insert_of_ne (k := entry.id) (Ne.symm hpe)
          entry.interval.low]
        exact hpget
      obtain ⟨e, he, hid, hlow⟩ :=
        hbwd p (mem_toList_iff_get?.mpr hold) hpe
      refine ⟨e, (hmem e).mpr (Or.inr ⟨he, ?_⟩), hid, hlow⟩
      intro hk
      apply hpe
      have h2 := congrArg Prod.snd hk
      exact hid.symm.trans h2
  · intro e
    constructor
    · intro he
      rcases (hmem e).mp he with rfl | ⟨hem, _⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hem, habsent e hem⟩
    · intro he
      rcases he with heq | ⟨hem, hidne⟩
      · rw [heq]
        exact (hmem entry).mpr (Or.inl rfl)
      · apply (hmem e).mpr
        exact Or.inr ⟨hem, fun hk => hidne (congrArg Prod.snd hk)⟩

/-- **Correctness of insertion into an indexed interval tree.** Let $T$ be an indexed interval tree
satisfying the representation invariant, and let $x$ be an entry whose interval is valid (its low
endpoint is at most its high endpoint). If inserting $x$ into $T$ succeeds with result $T'$, then
$T'$ satisfies the representation invariant, $x$ is stored in the root tree of $T'$, and an entry
$e$ is stored in the root tree of $T'$ if and only if either $e = x$, or $e$ is stored in the root
tree of $T$ and the identifier of $e$ differs from the identifier of $x$. -/
theorem insert_spec {tree : IndexedIntervalTree} (inv : tree.Invariant)
    {entry : Entry} (hvalid : entry.interval.valid = true)
    {result : IndexedIntervalTree} (hres : tree.insert entry = some result) :
    result.Invariant ∧ entry ∈ result.root.entries ∧
      ∀ e, e ∈ result.root.entries ↔
        e = entry ∨ (e ∈ tree.root.entries ∧ e.id ≠ entry.id) := by
  obtain ⟨hcache, hord, hbal, hval, hnoid, hfwd, hbwd⟩ := inv
  have hvalidProp : entry.interval.Valid :=
    @of_decide_eq_true _ (Int.decLe _ _) (by
      have h2 : entry.interval.valid = true := hvalid
      unfold Interval.valid at h2
      exact h2)
  cases hget : tree.idIndex.get? entry.id with
  | none =>
      have hresult : result = ⟨(tree.root.insertKeyWithCost entry).1,
          tree.idIndex.insert entry.id entry.interval.low⟩ := by
        have h1 : tree.insert entry =
            some ⟨(tree.root.insertKeyWithCost entry).1,
              tree.idIndex.insert entry.id entry.interval.low⟩ := by
          simp only [insert, insertWithCost, hvalid, hget, ite_true]
        rw [h1] at hres
        exact (Option.some.inj hres).symm
      subst hresult
      exact insert_stage hcache hord hbal hval hnoid hfwd
        (fun p hp _ => hbwd p hp) hvalidProp
        (fun e he hid => by
          have h1 := hfwd e he
          rw [hid, hget] at h1
          simp at h1)
  | some oldLow =>
      have hresult : result =
          ⟨((tree.root.eraseKeyWithCost (oldLow, entry.id)).1
              |>.insertKeyWithCost entry).1,
            tree.idIndex.insert entry.id entry.interval.low⟩ := by
        have h1 : tree.insert entry =
            some ⟨((tree.root.eraseKeyWithCost (oldLow, entry.id)).1
                |>.insertKeyWithCost entry).1,
              tree.idIndex.insert entry.id entry.interval.low⟩ := by
          simp only [insert, insertWithCost, hvalid, hget, ite_true]
        rw [h1] at hres
        exact (Option.some.inj hres).symm
      subst hresult
      have hkeyNodup : (tree.root.entries.map Entry.key).Nodup :=
        Tree.keyNodup_of_keyOrdered hord
      have hpermW := Tree.eraseKeyWithCost_entries_perm (oldLow, entry.id) hord
      have hnoidW :
          ((tree.root.eraseKeyWithCost (oldLow, entry.id)).1.entries.map
            (·.id)).Nodup := by
        apply (hpermW.map (·.id)).nodup_iff.mpr
        exact (List.filter_sublist.map (fun e : Entry => e.id)).nodup hnoid
      have hfwdW : ∀ e ∈ (tree.root.eraseKeyWithCost (oldLow, entry.id)).1.entries,
          tree.idIndex.get? e.id = some e.interval.low :=
        fun e he => hfwd e (Tree.mem_eraseKeyWithCost_of_mem _ e _ he)
      have hmemW : ∀ e,
          e ∈ (tree.root.eraseKeyWithCost (oldLow, entry.id)).1.entries ↔
          e ∈ tree.root.entries ∧ e.key ≠ (oldLow, entry.id) :=
        fun e => Tree.mem_eraseKeyWithCost (oldLow, entry.id) e hkeyNodup hord
      obtain ⟨hinv, hmemEntry, hothers⟩ := insert_stage
        (Tree.cacheInvariant_eraseKeyWithCost (oldLow, entry.id) hcache)
        (Tree.keyOrdered_eraseKeyWithCost (oldLow, entry.id) hord)
        (Tree.balancedProp_eraseKeyWithCost (oldLow, entry.id) hbal).1
        (Tree.validInvariant_eraseKeyWithCost (oldLow, entry.id) hval)
        hnoidW hfwdW
        (fun p hp hpe => by
          obtain ⟨e, he, hid, hlow⟩ := hbwd p hp
          refine ⟨e, (hmemW e).mpr ⟨he, ?_⟩, hid, hlow⟩
          intro hk
          apply hpe
          have h2 := congrArg Prod.snd hk
          exact hid.symm.trans h2)
        hvalidProp
        (fun e he hid => by
          have hem := (hmemW e).mp he
          have h1 := hfwd e hem.1
          rw [hid, hget] at h1
          have hlow : e.interval.low = oldLow := (Option.some.inj h1).symm
          exact hem.2 (by
            show e.key = (oldLow, entry.id)
            rw [Prod.ext_iff]
            exact ⟨hlow, hid⟩))
      refine ⟨hinv, hmemEntry, fun e => ?_⟩
      constructor
      · intro he
        rcases (hothers e).mp he with rfl | ⟨hew, hidne⟩
        · exact Or.inl rfl
        · exact Or.inr
            ⟨Tree.mem_eraseKeyWithCost_of_mem _ e _ hew, hidne⟩
      · intro he
        apply (hothers e).mpr
        rcases he with rfl | ⟨heT, hidne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨(hmemW e).mpr
            ⟨heT, fun hk => hidne (congrArg Prod.snd hk)⟩, hidne⟩

/-- **Correctness of erasure from the indexed interval tree.** Let $T$ be an indexed interval tree
satisfying the representation invariant, and let $i$ be a natural number. Then the tree obtained by
erasing identifier $i$ from $T$ again satisfies the invariant, and an entry is stored in it if and
only if it is stored in $T$ and its identifier differs from $i$.

In particular, if no stored entry has identifier $i$, the stored entries are unchanged. -/
theorem erase_spec {tree : IndexedIntervalTree} (inv : tree.Invariant)
    (id : Nat) :
    (tree.erase id).Invariant ∧
      ∀ e, e ∈ (tree.erase id).root.entries ↔
        e ∈ tree.root.entries ∧ e.id ≠ id := by
  obtain ⟨hcache, hord, hbal, hval, hnoid, hfwd, hbwd⟩ := inv
  have hkeyNodup : (tree.root.entries.map Entry.key).Nodup :=
    Tree.keyNodup_of_keyOrdered hord
  cases hget : tree.idIndex.get? id with
  | none =>
      have hte : tree.erase id = tree := by
        unfold erase eraseWithCost
        rw [hget]
      rw [hte]
      refine ⟨⟨hcache, hord, hbal, hval, hnoid, hfwd, hbwd⟩, ?_⟩
      intro e
      constructor
      · intro he
        refine ⟨he, ?_⟩
        intro hid
        have h1 := hfwd e he
        rw [hid, hget] at h1
        simp at h1
      · intro he
        exact he.1
  | some low =>
      have hte : tree.erase id =
          ⟨(tree.root.eraseKeyWithCost (low, id)).1,
            tree.idIndex.erase id⟩ := by
        unfold erase eraseWithCost
        rw [hget]
      rw [hte]
      have hmem : ∀ e, e ∈ (tree.root.eraseKeyWithCost (low, id)).1.entries ↔
          e ∈ tree.root.entries ∧ e.key ≠ (low, id) :=
        fun e => Tree.mem_eraseKeyWithCost (low, id) e hkeyNodup hord
      have hperm := Tree.eraseKeyWithCost_entries_perm (low, id) hord
      have hnoid' :
          ((tree.root.eraseKeyWithCost (low, id)).1.entries.map (·.id)).Nodup := by
        apply (hperm.map (·.id)).nodup_iff.mpr
        exact (List.filter_sublist.map (fun e : Entry => e.id)).nodup hnoid
      have hkeyne : ∀ e ∈ tree.root.entries, e.id ≠ id →
          e.key ≠ (low, id) := by
        intro e _ hne hk
        exact hne (congrArg Prod.snd hk)
      refine ⟨⟨Tree.cacheInvariant_eraseKeyWithCost (low, id) hcache,
        Tree.keyOrdered_eraseKeyWithCost (low, id) hord,
        (Tree.balancedProp_eraseKeyWithCost (low, id) hbal).1,
        Tree.validInvariant_eraseKeyWithCost (low, id) hval,
        hnoid', ?_, ?_⟩, ?_⟩
      · intro e he
        have hem := (hmem e).mp he
        have hne : e.id ≠ id := by
          intro hid
          have h1 := hfwd e hem.1
          rw [hid, hget] at h1
          have hlow : e.interval.low = low := (Option.some.inj h1).symm
          exact hem.2 (by
            show e.key = (low, id)
            rw [Prod.ext_iff]
            exact ⟨hlow, hid⟩)
        rw [get?_erase_of_ne (k := id) (Ne.symm hne)]
        exact hfwd e hem.1
      · intro p hp
        have hpget : (tree.idIndex.erase id).get? p.1 = some p.2 :=
          mem_toList_iff_get?.mp hp
        have hne : id ≠ p.1 := by
          intro hid
          have h1 : (tree.idIndex.erase id).get? p.1 = none := by
            change (tree.idIndex.erase id)[p.1]? = none
            rw [Std.TreeMap.getElem?_erase]
            simp [hid]
          rw [h1] at hpget
          simp at hpget
        have hold : tree.idIndex.get? p.1 = some p.2 := by
          rw [← get?_erase_of_ne (k := id) hne]
          exact hpget
        obtain ⟨e, he, hid, hlow⟩ :=
          hbwd p (mem_toList_iff_get?.mpr hold)
        refine ⟨e, (hmem e).mpr ⟨he, ?_⟩, hid, hlow⟩
        apply hkeyne e he
        intro hid2
        exact hne (hid2.symm.trans hid)
      · intro e
        constructor
        · intro he
          have hem := (hmem e).mp he
          refine ⟨hem.1, ?_⟩
          intro hid
          have h1 := hfwd e hem.1
          rw [hid, hget] at h1
          have hlow : e.interval.low = low := (Option.some.inj h1).symm
          exact hem.2 (by
            show e.key = (low, id)
            rw [Prod.ext_iff]
            exact ⟨hlow, hid⟩)
        · intro he
          exact (hmem e).mpr ⟨he.1, hkeyne e he.1 he.2⟩

end Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree
