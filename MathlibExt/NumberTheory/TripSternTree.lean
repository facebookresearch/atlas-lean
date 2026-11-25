/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **TRIP-Stern tree.** A TRIP-Stern tree with node values in a type $\alpha$ consists of a root
seed in $\alpha$ together with two maps from $\alpha$ to $\alpha$, the left transition and the
right transition. No condition is imposed on the seed or on the two transitions; in the source
the seed is $(1,1,1)$ and the left and right transitions are induced by the maps $F_0$ and $F_1$
defined there.

Source: Ilya Amburg, Krishna Dasaratha, Laure Flapan, Thomas Garrity, Chansoo Lee, Cornelia Mihaila,
Nicholas Neumann-Chun, Sarah Peluse, and Matthew Stoffregen, *Stern Sequences for a Family of
Multidimensional Continued Fractions: TRIP-Stern Sequences*, Journal of Integer Sequences 20 (2017),
Article 17.1.7, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Garrity/garrity6.tex>. The tree
abstracts Definition TRIPSternDef, lines 471-481 (seed (1,1,1), even/odd recursion by F_0/F_1,
levels as index intervals), with F_0/F_1 from line 387; binary paths follow the triangle(v)
definition, lines 485-488. -/
structure TripSternTree (α : Type _) where
  /-- Distinguished root seed of the tree. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
  (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
  seed : α
  /-- Fixed left transition (induced by `F_0`), taken on a `false` edge.
  Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
  TRIPSternDef, lines 471-481. -/
  leftTransition : α → α
  /-- Fixed right transition (induced by `F_1`), taken on a `true` edge.
  Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
  TRIPSternDef, lines 471-481. -/
  rightTransition : α → α

/-- **Node selected by a binary path.** Let $T$ be a TRIP-Stern tree with seed $s$, left
transition $L$ and right transition $R$. A binary path is a finite sequence of steps, each left
or right. The node of $T$ selected by a path $(b_1, \dots, b_k)$ is obtained by starting at $s$
and applying, for $i = 1, \dots, k$ in order, $L$ if $b_i$ is a left step and $R$ if $b_i$ is a
right step.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
TRIPSternDef, lines 471-481. -/
def TripSternTree.nodeAtPath {α : Type _} (T : TripSternTree α)
    (path : List Bool) : α :=
  path.foldl (fun node bit =>
    if bit then T.rightTransition node else T.leftTransition node) T.seed

/-- **The empty path selects the seed.** For every TRIP-Stern tree $T$, the node of $T$ selected
by the empty binary path is the seed of $T$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeAtEmptyPath {α : Type _} (T : TripSternTree α) :
    T.nodeAtPath [] = T.seed :=
  rfl

/-- **Extending a path by a left step.** Let $T$ be a TRIP-Stern tree with left transition $L$.
For every binary path $p$, the node of $T$ selected by $p$ followed by one left step equals $L$
applied to the node of $T$ selected by $p$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7,
Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeAtPathAppendLeft {α : Type _}
    (T : TripSternTree α) (path : List Bool) :
    T.nodeAtPath (path ++ [false]) = T.leftTransition (T.nodeAtPath path) := by
  unfold TripSternTree.nodeAtPath
  rw [List.foldl_append]
  simp

/-- **Extending a path by a right step.** Let $T$ be a TRIP-Stern tree with right transition $R$.
For every binary path $p$, the node of $T$ selected by $p$ followed by one right step equals $R$
applied to the node of $T$ selected by $p$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7,
Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeAtPathAppendRight {α : Type _}
    (T : TripSternTree α) (path : List Bool) :
    T.nodeAtPath (path ++ [true]) = T.rightTransition (T.nodeAtPath path) := by
  unfold TripSternTree.nodeAtPath
  rw [List.foldl_append]
  simp

/-- **Nodes at a given depth of a TRIP-Stern tree.** Let $T$ be a TRIP-Stern tree and $n$ a
natural number. The set of nodes of $T$ at depth $n$ is the set of all values $y$ such that some
binary path of length $n$ selects $y$ in $T$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
TRIPSternDef, lines 471-481. -/
def TripSternTree.nodesAtDepth {α : Type _} (T : TripSternTree α)
    (n : ℕ) : Set α :=
  { y | ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y }

/-- **Membership in a level of a TRIP-Stern tree.** For every TRIP-Stern tree $T$, natural number
$n$ and node value $y$, $y$ lies in the set of nodes of $T$ at depth $n$ if and only if there is
a binary path of length $n$ whose selected node in $T$ is $y$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodeMembershipAtDepth {α : Type _} (T : TripSternTree α)
    (n : ℕ) (y : α) :
    y ∈ T.nodesAtDepth n ↔
      ∃ path : List Bool, path.length = n ∧ T.nodeAtPath path = y :=
  Iff.rfl

/-- **Depth zero is the seed.** For every TRIP-Stern tree $T$ and every node value $y$, $y$ lies
in the set of nodes of $T$ at depth $0$ if and only if $y$ is the seed of $T$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.nodesAtDepthZero {α : Type _}
    (T : TripSternTree α) (y : α) :
    y ∈ T.nodesAtDepth 0 ↔ y = T.seed := by
  constructor
  · intro h
    match h with
    | ⟨path, hlen, hnode⟩ =>
      rw [List.length_eq_zero_iff] at hlen
      subst hlen
      simp [TripSternTree.nodeAtPath] at hnode
      exact hnode.symm
  · intro h
    subst h
    exact ⟨[], rfl, rfl⟩

/-- **Left-most node of a TRIP-Stern tree.** Let $T$ be a TRIP-Stern tree with seed $s$ and left
transition $L$. The left-most node of $T$ at depth $n$ is $L^n(s)$, the result of applying $L$
$n$ times to $s$; that is, it is $s$ at depth $0$, and at depth $n + 1$ it is $L$ applied to the
left-most node at depth $n$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
def TripSternTree.leftmostNode {α : Type _} (T : TripSternTree α) : ℕ → α
  | 0 => T.seed
  | n + 1 => T.leftTransition (T.leftmostNode n)

/-- **Rightmost node of a TRIP-Stern tree.** For a TRIP-Stern tree $T$ and a natural number $n$,
the rightmost node of $T$ at depth $n$ is obtained from the seed of $T$ by applying the right
transition of $T$ exactly $n$ times: at depth $0$ it is the seed, and at depth $n + 1$ it is the
image of the rightmost node at depth $n$ under the right transition.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
(2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
def TripSternTree.rightmostNode {α : Type _} (T : TripSternTree α) : ℕ → α
  | 0 => T.seed
  | n + 1 => T.rightTransition (T.rightmostNode n)

/-- **Left-most node at depth zero.** For every TRIP-Stern tree $T$, the left-most node of $T$ at
depth $0$ is the seed of $T$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS
20 (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.leftmostNodeAtZero {α : Type _} (T : TripSternTree α) :
    T.leftmostNode 0 = T.seed :=
  rfl

/-- **Recursion for the left-most node.** Let $T$ be a TRIP-Stern tree with left transition
$L$. For every natural number $n$, the left-most node of $T$ at depth $n + 1$ equals $L$ applied
to the left-most node of $T$ at depth $n$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7,
Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.leftmostNodeAtSuccessor {α : Type _} (T : TripSternTree α)
    (n : ℕ) :
    T.leftmostNode (n + 1) = T.leftTransition (T.leftmostNode n) :=
  rfl

/-- **Rightmost node at depth zero.** For every TRIP-Stern tree $T$, the rightmost node of $T$ at
depth $0$ is the seed of $T$.

Source: Amburg et al., *TRIP-Stern Sequences*,
JIS 20 (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.rightmostNodeAtZero {α : Type _} (T : TripSternTree α) :
    T.rightmostNode 0 = T.seed :=
  rfl

/-- **Successor step of the rightmost node.** For every TRIP-Stern tree $T$ and every natural
number $n$, the rightmost node of $T$ at depth $n + 1$ is the image of the rightmost node of
$T$ at depth $n$ under the right transition of $T$.

Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article
17.1.7, Definition TRIPSternDef, lines 471-481. -/
theorem TripSternTree.rightmostNodeAtSuccessor {α : Type _} (T : TripSternTree α)
    (n : ℕ) :
    T.rightmostNode (n + 1) = T.rightTransition (T.rightmostNode n) :=
  rfl

end

end MetaMathlibExt
