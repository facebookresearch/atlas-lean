/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree
public import CSLibExt.Algorithms.Lean.DataStructures.SplayTree
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A costed pointer model of rooted link-cut trees

Following E. Demaine, MIT 6.851, Lecture 19 (1 May 2012), §§2–3. Each allocated vertex has a
stable handle. Only the auxiliary child pointers and their reverse pointers are stored, not a
second copy of the represented forest. An up-pointer from an auxiliary root is dashed: it
points to the represented parent of the **first vertex in inorder**, not necessarily the
represented parent of the auxiliary root. A rotation transfers this pointer to the new root.
Inorder encodes relative depth; the algorithm never stores or recomputes depth keys.

`step` acts only on the handle table. One unit of `work` represents a bounded block of local
operations: one rotation (including two aggregate repairs), one splay completion, one expose
iteration outside splaying, one left-walk visit, or the fixed overhead of an operation. The
model counts direct record accesses, allocation of one record, and monoid operations on a
constant number of words at unit cost. It does not time Lean arrays, large payloads, or the
specification. Loop fuel is a safety limit obtained from the allocated vertex count; each
iteration consumes one unit of fuel, and reaching zero fails rather than giving a cheap result.

`specStep` independently specifies legality, represented-forest updates and answers using
`LinkCutTree.State`. Its tree searches and path lists are *not* subroutines of `step`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LinkCutTree.SplayForest

variable {M : Type}

/-- **Link-cut vertex record.** A record at a stable handle stores two ordinary auxiliary
children and an up-pointer. If its target does not list this handle as a child, the pointer is
a path-parent pointer. The payload is the incoming represented edge weight (identity at a
represented root); the cache is the ordered product for the auxiliary subtree. -/
structure Cell (M : Type) where
  left : Option Nat
  right : Option Nat
  up : Option Nat
  weight : M
  summary : M
  deriving DecidableEq

/-- **Link-cut pointer state.** Handles are the indices of allocated cells. A separate counter
records the cumulative number of constant-size local work blocks; it never affects control. -/
structure Heap (M : Type) where
  cells : Array (Cell M) := #[]
  work : Nat := 0
  deriving DecidableEq

variable [Monoid M]

def singletonCell : Cell M := ⟨none, none, none, 1, 1⟩

namespace Heap

def cell (h : Heap M) (x : Nat) : Cell M := h.cells[x]?.getD singletonCell

def writeAt (h : Heap M) (x : Nat) (c : Cell M) : Heap M :=
  { h with cells := h.cells.setIfInBounds x c }

def tick (h : Heap M) : Heap M := { h with work := h.work + 1 }

def setUp (h : Heap M) (x : Option Nat) (u : Option Nat) : Heap M :=
  match x with
  | none => h
  | some i => h.writeAt i { h.cell i with up := u }

def cached (h : Heap M) (x : Option Nat) : M :=
  match x with
  | none => 1
  | some i => (h.cell i).summary

def pull (h : Heap M) (x : Nat) : Heap M :=
  let c := h.cell x
  h.writeAt x { c with summary := h.cached c.left * c.weight * h.cached c.right }

-- The second component is true for a right child. Dashed up-pointers are not rotated.
def parentSide (h : Heap M) (x : Nat) : Option (Nat × Bool) := do
  let p ← (h.cell x).up
  if (h.cell p).left == some x then return (p, false)
  if (h.cell p).right == some x then return (p, true)
  none

def rotate (h : Heap M) (x p : Nat) (right : Bool) : Heap M :=
  let a := h.cell x
  let b := h.cell p
  let t := if right then a.left else a.right
  let h' := match h.parentSide p with
    | some (g, false) => h.writeAt g { h.cell g with left := some x }
    | some (g, true) => h.writeAt g { h.cell g with right := some x }
    | none => h
  let h' := h'.setUp t (some p)
  let h' := h'.writeAt p (if right then { b with right := t, up := some x }
    else { b with left := t, up := some x })
  let h' := h'.writeAt x (if right then { a with left := some p, up := b.up }
    else { a with right := some p, up := b.up })
  ((h'.pull p).pull x).tick

def splayLoop (x : Nat) : Nat → Heap M → Option (Heap M)
  | 0, _ => none
  | k + 1, h =>
    match h.parentSide x with
    | none => some h.tick
    | some (p, d) =>
      match h.parentSide p with
      | none => some ((h.rotate x p d).tick)
      | some (g, e) =>
        if d == e then splayLoop x k ((h.rotate p g e).rotate x p d)
        else splayLoop x k ((h.rotate x p d).rotate x g e)

/-- **Bottom-up handle splay.** Starting at a live handle, rotate within its auxiliary tree,
first rotating the parent in a zig-zig and the target in a zig-zag. A last unpaired edge gives
a zig at the top. Charge one unit per rotation and one for completion. -/
def splay (h : Heap M) (x : Nat) : Option (Heap M) := splayLoop x (h.cells.size + 1) h

/-- **Preferred-child switch at an auxiliary root.** Replace its ordinary right subtree by the
already exposed suffix (absent in the first iteration). The detached child's up-pointer now
serves as a path-parent pointer; the incoming suffix's existing path-parent pointer now serves
as an ordinary parent pointer. Only the root record needs a write and aggregate repair. -/
def splice (h : Heap M) (x : Nat) (suffix : Option Nat) : Heap M :=
  ((h.writeAt x { h.cell x with right := suffix }).pull x).tick

/-- **A preferred-child switch is local.** Replacing the right subtree at a handle costs one
work block and leaves the entire record of every other handle unchanged. -/
theorem splice_frame (h : Heap M) (x : Nat) (suffix : Option Nat) :
    (h.splice x suffix).work = h.work + 1 ∧
    ∀ j ≠ x, (h.splice x suffix).cells[j]? = h.cells[j]? := by
  refine ⟨rfl, fun j hj => ?_⟩
  simp [splice, tick, pull, writeAt, Ne.symm hj]

def exposeLoop (target : Nat) : Nat → Heap M → Nat → Option Nat → Option (Heap M)
  | 0, _, _, _ => none
  | k + 1, h, x, suffix => do
    let h ← h.splay x
    let u := (h.cell x).up
    let h := h.splice x suffix
    match u with
    | none => h.splay target
    | some p => exposeLoop target k h p (some x)

/-- **Physical access in a link-cut forest.** Splay the current handle, switch its right child
and follow its path-parent, successively joining the path segments. Finally splay the original
target in the joined path. All iterations, including those requiring no rotations, are charged. -/
def expose (h : Heap M) (x : Nat) : Option (Heap M) :=
  exposeLoop x (h.cells.size + 1) h x none

def walkLeft : Nat → Heap M → Nat → Option (Heap M × Nat)
  | 0, _, _ => none
  | k + 1, h, x =>
    match (h.cell x).left with
    | none => some (h.tick, x)
    | some y => walkLeft k h.tick y

end Heap

/-- **Rooted link-cut operations.** Make a fresh singleton; expose a root path; link a root to
a vertex of another tree with a specified edge weight; cut a non-root from its parent; find
the represented root; or query the root-to-vertex edge product. -/
inductive Call (M : Type) where
  | makeTree
  | access (v : Nat)
  | link (v w : Nat) (weight : M)
  | cut (v : Nat)
  | findRoot (v : Nat)
  | pathAggregate (v : Nat)
  deriving DecidableEq

/-- **Link-cut operation answers.** Updates and access acknowledge completion, make-tree and
find-root return one handle, and path-aggregate returns one monoid element. -/
inductive Answer (M : Type) where
  | done
  | vertex (v : Nat)
  | aggregate (a : M)
  deriving DecidableEq

/-- **Costed link-cut operation on handles.** Link exposes both arguments and puts the second
on the left of the first. Cut exposes its target, removes its left subtree and resets its edge
weight to the identity. Find-root exposes, walks left, then splays the vertex it returns.
A path query exposes and reads one cache. The caller supplies legal arguments; the pointer
machine does not validate global connectivity by a free search. -/
def step (s : Heap M) (op : Call M) : Option (Heap M × Answer M) := do
  let h := s.tick
  match op with
  | .makeTree => return ({ h with cells := h.cells.push singletonCell }, .vertex h.cells.size)
  | .access v => return (← h.expose v, .done)
  | .pathAggregate v =>
    let h ← h.expose v
    return (h, .aggregate (h.cell v).summary)
  | .findRoot v =>
    let h ← h.expose v
    let (h, r) ← Heap.walkLeft (h.cells.size + 1) h v
    return (← h.splay r, .vertex r)
  | .link v w a =>
    let h ← h.expose v
    let h ← h.expose w
    let h := h.setUp (some w) (some v)
    let h := h.writeAt v { h.cell v with left := some w, weight := a }
    return (h.pull v, .done)
  | .cut v =>
    let h ← h.expose v
    let l ← (h.cell v).left
    let h := h.setUp (some l) none
    let h := h.writeAt v { h.cell v with left := none, weight := 1 }
    return (h.pull v, .done)

/-- **Reference state of a weighted dynamic forest.** A represented forest with preferred
edges, a fresh-handle counter and an incoming edge weight per vertex (identity at roots).
This state is used to specify legal calls and their results, not to compute pointer costs. -/
structure Spec (M : Type) [Monoid M] where
  trees : State Nat := ⟨[], []⟩
  count : Nat := 0
  weight : Nat → M := fun _ => 1

/-- **Legal weighted link-cut operation.** Legality and answers are determined by the represented
forest alone. A link requires a root and a vertex of a different tree; a cut requires a non-root.
Access preserves off-path preferences. Link makes the new edge solid after exposing both endpoints;
cut removes only the exposed incoming edge. Queries make the queried path solid, even when a
subsequent auxiliary splay brings the represented root to the top. The path answer multiplies
incoming edge weights in root-to-target order, excluding the root. -/
def specStep (s : Spec M) (op : Call M) : Option (Spec M × Answer M) := do
  let f := s.trees
  match op with
  | .makeTree =>
    let v := s.count
    return (⟨{ f with forest := .node v [] :: f.forest }, v + 1, Function.update s.weight v 1⟩,
      .vertex v)
  | .access v =>
    let _ ← findTree v f.forest
    return ({ s with trees := f.access v }, .done)
  | .findRoot v =>
    let t ← findTree v f.forest
    return ({ s with trees := f.access v }, .vertex t.root)
  | .pathAggregate v =>
    let t ← findTree v f.forest
    let p ← rootPath v t
    return ({ s with trees := f.access v }, .aggregate ((p.tail.map s.weight).prod))
  | .link v w a =>
    let tv ← findTree v f.forest
    let tw ← findTree w f.forest
    guard (tv.root = v ∧ v ∉ tw.vertices)
    let pref := ((f.access v).access w).preferred ++ [(w, v)]
    return ({ s with trees := { f.link v w with preferred := pref },
                     weight := Function.update s.weight v a }, .done)
  | .cut v =>
    let t ← findTree v f.forest
    guard (t.root ≠ v)
    let pref := (f.access v).preferred.filter (fun e => e.2 != v)
    return ({ s with trees := { f.cut v with preferred := pref },
                     weight := Function.update s.weight v 1 }, .done)

/-- **Execution of a link-cut history.** Execute calls from left to right, threading either the
reference state or the pointer state and collecting one answer per call. Failure of any step
fails the whole run. Success of the reference run is the legality condition on the history. -/
def replay {S : Type*} (next : S → Call M → Option (S × Answer M)) :
    S → List (Call M) → Option (S × List (Answer M))
  | s, [] => some (s, [])
  | s, op :: ops => do
    let (s', a) ← next s op
    let (s'', as) ← replay next s' ops
    return (s'', a :: as)

/-- **Materializing an auxiliary tree.** The ordinary children reachable from the tree root
have exactly the given binary shape, with the specified up-pointer at the root, reciprocal
child pointers internally, the given incoming weights and locally correct ordered caches.
The empty tree places no constraint on the table. -/
def Stores (h : Heap M) (weight : Nat → M) (up : Option Nat) : BinaryTree Nat → Prop
  | .nil => True
  | .node x l r =>
    x < h.cells.size ∧ (h.cell x).up = up ∧ (h.cell x).left = SplayTree.root? l ∧
    (h.cell x).right = SplayTree.root? r ∧ (h.cell x).weight = weight x ∧
    (h.cell x).summary = h.cached (SplayTree.root? l) * weight x * h.cached (SplayTree.root? r) ∧
    Stores h weight (some x) l ∧ Stores h weight (some x) r

def pathParent (f : State Nat) (p : List Nat) (u : Option Nat) : Prop :=
  ∃ t ∈ f.forest, ∃ a, p.head? = some a ∧
    match u with
    | none => t.root = a
    | some x => ParentChild x a t

/-- **Representation by ordered auxiliary trees.** The reference state is valid, its roots have
identity weight and its vertices are exactly the allocated handles. Every maximal preferred
path is the inorder traversal of a stored auxiliary tree with consistent reverse pointers,
edge payloads and caches. Its root's up-pointer is the represented parent of the first vertex
of the path, or null at a represented root. Thus the auxiliary trees cover the handles
disjointly, in path order rather than handle order. -/
def Represents (h : Heap M) (s : Spec M) : Prop :=
  s.trees.Valid ∧ h.cells.size = s.count ∧ (∀ x, s.trees.Mem x ↔ x < s.count) ∧
    (∀ t ∈ s.trees.forest, s.weight t.root = 1) ∧
    ∀ p ∈ s.trees.paths, ∃ (t : BinaryTree Nat) (u : Option Nat),
      BinarySearchTree.inorder t = p ∧ Stores h s.weight u t ∧ pathParent s.trees p u

theorem represents_empty : Represents ({} : Heap M) ({} : Spec M) := by
  simp [Represents, State.Valid, State.Mem, State.paths]

private theorem cached_eq_prod (h : Heap M) (w : Nat → M) (t : BinaryTree Nat) (u : Option Nat)
    (hs : Stores h w u t) :
    h.cached (SplayTree.root? t) = ((BinarySearchTree.inorder t).map w).prod := by
  induction t generalizing u with
  | nil => rfl
  | node x l r ihl ihr =>
    obtain ⟨_, _, _, _, _, hc, hl, hr⟩ := hs
    change (h.cell x).summary = _
    rw [hc, ihl _ hl, ihr _ hr, BinarySearchTree.inorder_node]
    simp [mul_assoc]

/-- **Locally maintained caches give the inorder product.** For any nonempty stored auxiliary
tree, the record at its root contains the product of its payloads in inorder. This only needs
local cache consistency and associativity, not commutativity or a balance invariant. -/
theorem Stores.root_product {h : Heap M} {w : Nat → M} {u : Option Nat} {x : Nat}
    {l r : BinaryTree Nat} (hs : Stores h w u (.node x l r)) :
    ∃ c, h.cells[x]? = some c ∧
      c.summary = ((BinarySearchTree.inorder (.node x l r)).map w).prod := by
  have hi : x < h.cells.size := hs.1
  have hc : h.cells[x]? = some h.cells[x] := getElem?_pos h.cells x hi
  refine ⟨h.cells[x], hc, ?_⟩
  simpa [Heap.cached, Heap.cell, hc] using cached_eq_prod h w (.node x l r) u hs

end Cslib.Algorithms.Lean.LinkCutTree.SplayForest
