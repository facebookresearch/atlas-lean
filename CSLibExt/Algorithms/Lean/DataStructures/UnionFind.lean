/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

/-!
# Persistent union-find with parent-path costs

This module models a finite parent forest. A `Forest n` stores one parent and a
natural-number depth certificate for every `Fin n`; every non-root parent edge
strictly decreases that certificate. `find` follows parent pointers to a root.

`union` is persistent: it links the root of the first class to the root of the
second class. It deliberately models neither union-by-rank nor path compression.
The explicit `TimeM Nat` model charges one unit per vertex visited by `find` and
one additional unit for a root link only when the two representatives are
distinct (no link is performed, or charged, when they already coincide). Thus
`find` is bounded by certified forest depth, and `union` by the two searches
plus at most one. These are abstract operation counts, not compiler or
wall-clock costs.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

/-- **Parent forest with a depth certificate.** A parent forest on the vertices
$\{0, \dots, n-1\}$ consists of a parent map $p$ from the vertices to themselves (a vertex $x$
with $p(x) = x$ is a root) and a depth certificate $d$ assigning a natural number to every
vertex, such that every non-root edge strictly decreases the certificate: if $p(x) \ne x$, then
$d(p(x)) < d(x)$. -/
public structure Forest (n : Nat) where
  /-- Parent pointer for every vertex; roots point to themselves. -/
  parent : Fin n → Fin n
  /-- A certificate bounding the remaining parent-path length. -/
  depth : Fin n → Nat
  /-- Every non-root edge strictly decreases the depth certificate. -/
  parent_lt : ∀ x, parent x ≠ x → depth (parent x) < depth x

/-- **Root of a vertex in a parent forest.** For a parent forest $F$ with parent map $p$ and a
vertex $x$, the root of $x$ is found by following parent pointers from $x$: it is $x$ itself
if $p(x) = x$, and otherwise it is the root of $p(x)$. -/
public def find {n : Nat} (forest : Forest n) (x : Fin n) : Fin n :=
  if _h : forest.parent x = x then x else find forest (forest.parent x)
termination_by forest.depth x
decreasing_by exact forest.parent_lt x _h

/-- **Path length to the root.** For a parent forest $F$ with parent map $p$ and a vertex $x$,
the path length of $x$ is the number of parent edges followed from $x$ to its root: it is $0$ if
$p(x) = x$, and otherwise one more than the path length of $p(x)$. -/
public def pathLength {n : Nat} (forest : Forest n) (x : Fin n) : Nat :=
  if h : forest.parent x = x then 0 else pathLength forest (forest.parent x) + 1
termination_by forest.depth x
decreasing_by exact forest.parent_lt x h

/-- **Find with cost.** For a vertex $x$ of a parent forest $F$, find with cost returns the root
that find returns for $x$, together with the cost $\ell(x) + 1$, where $\ell(x)$ is the path
length of $x$ (the number of non-root parent edges that find traverses from $x$). That is, it
charges one unit for every visited vertex, including the root. -/
public def findWithCost {n : Nat} (forest : Forest n) (x : Fin n) : TimeM Nat (Fin n) :=
  ⟨find forest x, pathLength forest x + 1⟩

/-- **Equivalent vertices of a parent forest.** Two vertices $x$ and $y$ of a parent forest $F$
are equivalent when find returns the same root for $x$ as for $y$ in $F$. -/
public def Equivalent {n : Nat} (forest : Forest n) (x y : Fin n) : Prop :=
  find forest x = find forest y

public instance equivalentDecidable {n : Nat} (forest : Forest n) (x y : Fin n) :
    Decidable (Equivalent forest x y) := by
  unfold Equivalent
  infer_instance

@[simp]
private theorem find_eq_self_of_parent_eq {n : Nat} (forest : Forest n) (x : Fin n)
    (h : forest.parent x = x) : find forest x = x := by
  rw [find]
  simp [h]

@[simp]
private theorem pathLength_eq_zero_of_parent_eq {n : Nat} (forest : Forest n) (x : Fin n)
    (h : forest.parent x = x) : pathLength forest x = 0 := by
  rw [pathLength]
  simp [h]

/-- **Find returns a root.** For every vertex $x$ of a parent forest $F$, the vertex $r$ that find
returns for $x$ is a root of $F$: the parent of $r$ in $F$ is $r$ itself. -/
public theorem find_isRoot {n : Nat} (forest : Forest n) (x : Fin n) :
    forest.parent (find forest x) = find forest x := by
  rw [find.eq_1 forest x]
  split
  · assumption
  · exact find_isRoot forest (forest.parent x)
termination_by forest.depth x
decreasing_by exact forest.parent_lt x ‹forest.parent x ≠ x›

/-- **Find is unchanged along a parent pointer.** For every vertex $x$ of a parent forest $F$,
find returns the same root for the parent of $x$ in $F$ as for $x$. -/
public theorem find_parent {n : Nat} (forest : Forest n) (x : Fin n) :
    find forest (forest.parent x) = find forest x := by
  by_cases h : forest.parent x = x
  · rw [h]
  · rw [find.eq_1 forest x]
    simp only [h, ↓reduceDIte]

@[simp]
private theorem find_find {n : Nat} (forest : Forest n) (x : Fin n) :
    find forest (find forest x) = find forest x :=
  find_eq_self_of_parent_eq forest _ (find_isRoot forest x)

/-- **Every vertex is equivalent to its representative.** For every vertex $x$ of a parent
forest $F$, the vertex $x$ is equivalent in $F$ to the root that find returns for $x$. -/
public theorem find_in_class {n : Nat} (forest : Forest n) (x : Fin n) :
    Equivalent forest x (find forest x) := by
  simp [Equivalent]

private theorem pathLength_le_depth {n : Nat} (forest : Forest n) (x : Fin n) :
    pathLength forest x ≤ forest.depth x := by
  rw [pathLength.eq_1 forest x]
  split
  · omega
  · have hrec := pathLength_le_depth forest (forest.parent x)
    have hlt := forest.parent_lt x ‹forest.parent x ≠ x›
    omega
termination_by forest.depth x
decreasing_by exact forest.parent_lt x ‹forest.parent x ≠ x›

/-- **The cost of find is the path length plus one.** For every vertex $x$ of a parent forest $F$,
the cost that find with cost charges on $x$ equals $\ell(x) + 1$, where $\ell(x)$ is the path
length of $x$: the number of non-root parent edges that find traverses from $x$. -/
public theorem findWithCost_time {n : Nat} (forest : Forest n) (x : Fin n) :
    (findWithCost forest x).time = pathLength forest x + 1 := rfl

/-- **The cost of find is at most the depth certificate plus one.** For every vertex $x$ of a
parent forest $F$ with depth certificate $d$, the cost that find with cost charges on $x$ is at
most $d(x) + 1$. -/
public theorem findWithCost_time_le_depth {n : Nat} (forest : Forest n) (x : Fin n) :
  (findWithCost forest x).time ≤ forest.depth x + 1 := by
  rw [findWithCost_time]
  have h := pathLength_le_depth forest x
  omega

/-- **Parent map after linking two roots.** Let $F$ be a parent forest with parent map $p$, and
let $r$ and $s$ be vertices. The linked parent map sends $r$ to $s$ and agrees with $p$ on every
other vertex: it maps $z$ to $s$ if $z = r$, and to $p(z)$ otherwise. -/
public def linkParent {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n) :
    Fin n → Fin n := fun z => if z = fromRoot then toRoot else forest.parent z

/-- **Depth certificate after linking two roots.** Let $F$ be a parent forest with depth
certificate $d$, and let $r$ and $s$ be vertices. The linked depth certificate assigns to a
vertex $z$ the number $d(z) + d(s) + 1$ if $z$ is equivalent to $r$ in $F$ (that is, $z$ and $r$
have the same root), and $d(z)$ otherwise. -/
public def linkDepth {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n) :
    Fin n → Nat := fun z =>
      if Equivalent forest z fromRoot
      then forest.depth z + forest.depth toRoot + 1
      else forest.depth z

/-- **Linking two roots of a parent forest.** Let $F$ be a parent forest with parent map $p$ and
depth certificate $d$, and let $r \ne s$ be two distinct roots of $F$. Linking $r$ to $s$ gives
the parent forest whose parent map is the linked parent map (the parent of $r$ becomes $s$ and
all other parents are unchanged) and whose depth certificate is the linked depth certificate (the
certificate of every vertex equivalent to $r$ grows by $d(s) + 1$ and all others are unchanged).
These still satisfy the decreasing-certificate condition. -/
public def link {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n)
    (hFrom : forest.parent fromRoot = fromRoot)
    (hTo : forest.parent toRoot = toRoot) (hne : fromRoot ≠ toRoot) : Forest n where
  parent := linkParent forest fromRoot toRoot
  depth := linkDepth forest fromRoot toRoot
  parent_lt z hz := by
    by_cases hzr : z = fromRoot
    · subst z
      have hFromEq : Equivalent forest fromRoot fromRoot := by
        simp [Equivalent]
      have hToNe : ¬Equivalent forest toRoot fromRoot := by
        intro h
        have : toRoot = fromRoot := by
          simpa [Equivalent, find_eq_self_of_parent_eq forest _ hTo,
            find_eq_self_of_parent_eq forest _ hFrom] using h
        exact hne this.symm
      simp [linkParent, linkDepth, hFromEq, hToNe]
      omega
    · have hparent : forest.parent z ≠ z := by
        intro h
        apply hz
        simp [linkParent, hzr, h]
      have hlt := forest.parent_lt z hparent
      have heq : Equivalent forest (forest.parent z) fromRoot ↔
          Equivalent forest z fromRoot := by
        simp only [Equivalent, find_parent]
      by_cases hzClass : Equivalent forest z fromRoot
      · have hpClass : Equivalent forest (forest.parent z) fromRoot := heq.mpr hzClass
        simp [linkParent, linkDepth, hzr, hzClass, hpClass]
        omega
      · have hpClass : ¬Equivalent forest (forest.parent z) fromRoot :=
          fun h => hzClass (heq.mp h)
        simpa [linkParent, linkDepth, hzr, hzClass, hpClass] using hlt

/-- **Union in a union-find forest.** Let $F$ be a union-find forest on $n$ vertices: each vertex
$z$ has a parent $p(z)$, where roots are their own parents, and a depth certificate
$d(z) \in \mathbb{N}$ with $d(p(z)) < d(z)$ whenever $p(z) \ne z$. Let $x$ and $y$ be vertices,
and let $r_x$ and $r_y$ be the roots reached from $x$ and $y$ by following parent pointers. If
$r_x = r_y$, the union of $x$ and $y$ in $F$ is $F$ itself. Otherwise it is the forest obtained
from $F$ by linking $r_x$ to $r_y$: the parent of $r_x$ becomes $r_y$, all other parent pointers
are unchanged, every vertex $z$ whose root is $r_x$ gets depth certificate $d(z) + d(r_y) + 1$,
and every other vertex keeps $d(z)$.

The operation is persistent: it returns a new forest and does not modify $F$. -/
public def union {n : Nat} (forest : Forest n) (x y : Fin n) : Forest n :=
  let fromRoot := find forest x
  let toRoot := find forest y
  if h : fromRoot = toRoot then forest
  else link forest fromRoot toRoot (find_isRoot forest x) (find_isRoot forest y) h

private theorem find_link {n : Nat} (forest : Forest n) (fromRoot toRoot : Fin n)
    (hFrom : forest.parent fromRoot = fromRoot)
    (hTo : forest.parent toRoot = toRoot) (hne : fromRoot ≠ toRoot) (z : Fin n) :
    find (link forest fromRoot toRoot hFrom hTo hne) z =
      if find forest z = fromRoot then toRoot else find forest z := by
  by_cases hzr : z = fromRoot
  · subst z
    have hne' : toRoot ≠ fromRoot := Ne.symm hne
    have hLinkFrom : (link forest fromRoot toRoot hFrom hTo hne).parent fromRoot =
        toRoot := by
      simp [link, linkParent]
    have hLinkTo : (link forest fromRoot toRoot hFrom hTo hne).parent toRoot =
        toRoot := by
      simp [link, linkParent, hne', hTo]
    rw [find.eq_1]
    simp only [hLinkFrom, hne', ↓reduceDIte]
    rw [find_eq_self_of_parent_eq _ _ hLinkTo]
    simp [find_eq_self_of_parent_eq forest _ hFrom]
  · by_cases hzRoot : forest.parent z = z
    · have hLinkRoot : (link forest fromRoot toRoot hFrom hTo hne).parent z = z := by
        simp [link, linkParent, hzr, hzRoot]
      rw [find_eq_self_of_parent_eq _ _ hLinkRoot]
      have hFind : find forest z = z := find_eq_self_of_parent_eq forest z hzRoot
      simp [hFind, hzr]
    · have hLinkParent :
          (link forest fromRoot toRoot hFrom hTo hne).parent z = forest.parent z := by
        simp [link, linkParent, hzr]
      have hLinkNe :
          (link forest fromRoot toRoot hFrom hTo hne).parent z ≠ z := by
        simpa [hLinkParent] using hzRoot
      rw [find.eq_1]
      simp only [hLinkNe, ↓reduceDIte]
      rw [hLinkParent]
      rw [find_link forest fromRoot toRoot hFrom hTo hne (forest.parent z)]
      rw [find_parent]
termination_by forest.depth z
decreasing_by exact forest.parent_lt z hzRoot

/-- **Representatives after a union.** Let $F$ be a parent forest, let $x, y, z$ be vertices of
$F$, and let $F'$ be the forest obtained from $F$ by the union of $x$ and $y$. If $z$ is
equivalent to $x$ in $F$, then find returns for $z$ in $F'$ the root that find returns for $y$
in $F$; otherwise find returns the same root for $z$ in $F'$ as in $F$. -/
public theorem find_union {n : Nat} (forest : Forest n) (x y z : Fin n) :
    find (union forest x y) z =
      if Equivalent forest z x then find forest y else find forest z := by
  by_cases hxy : find forest x = find forest y
  · simp only [union, hxy, ↓reduceDIte]
    by_cases hzx : Equivalent forest z x
    · have : find forest z = find forest y := by
        rw [Equivalent] at hzx
        exact hzx.trans hxy
      simp [hzx, this]
    · simp [hzx]
  · rw [union]
    simp only [hxy, ↓reduceDIte]
    rw [find_link]
    simp [Equivalent]

/-- **Union makes its arguments equivalent.** For every parent forest $F$ and vertices $x$ and
$y$, the vertices $x$ and $y$ are equivalent in the forest obtained from $F$ by the union of $x$
and $y$. -/
public theorem union_equivalent {n : Nat} (forest : Forest n) (x y : Fin n) :
    Equivalent (union forest x y) x y := by
  by_cases hxy : find forest x = find forest y <;>
    simp [Equivalent, find_union, hxy, eq_comm]

/-- **Union of equivalent vertices changes nothing.** If $x$ and $y$ are equivalent vertices of a
parent forest $F$, then the union of $x$ and $y$ in $F$ is $F$ itself. -/
public theorem union_eq_self_of_equivalent {n : Nat} {forest : Forest n} {x y : Fin n}
    (h : Equivalent forest x y) : union forest x y = forest := by
  unfold Equivalent at h
  rw [union]
  simp only [h, ↓reduceDIte]

/-- **Equivalence after a union.** Let $F$ be a parent forest and let $x, y, a, b$ be vertices of
$F$. Then $a$ and $b$ are equivalent in the forest obtained from $F$ by the union of $x$ and $y$
if and only if $a$ and $b$ are equivalent in $F$, or $a$ is equivalent to $x$ and $b$ is
equivalent to $y$ in $F$, or $a$ is equivalent to $y$ and $b$ is equivalent to $x$ in $F$.

Thus the union merges exactly the old classes of $x$ and $y$. -/
public theorem equivalent_union_iff {n : Nat} (forest : Forest n) (x y a b : Fin n) :
    Equivalent (union forest x y) a b ↔
      Equivalent forest a b ∨
        (Equivalent forest a x ∧ Equivalent forest b y) ∨
        (Equivalent forest a y ∧ Equivalent forest b x) := by
  simp only [Equivalent, find_union]
  by_cases hxy : find forest x = find forest y
  · constructor
    · intro h
      left
      by_cases hax : find forest a = find forest x <;>
        by_cases hbx : find forest b = find forest x <;> simp_all
    · rintro (hab | hclasses)
      · by_cases hax : find forest a = find forest x <;>
          by_cases hbx : find forest b = find forest x <;> simp_all
      · rcases hclasses with hclasses | hclasses <;> rcases hclasses with ⟨ha, hb⟩
        all_goals
          by_cases hax : find forest a = find forest x <;>
            by_cases hbx : find forest b = find forest x <;> simp_all
  · by_cases hax : find forest a = find forest x <;>
      by_cases hbx : find forest b = find forest x <;> simp_all [eq_comm]

/-- **Union preserves the representatives of unrelated classes.** Let $F$ be a parent forest and
let $x, y, z$ be vertices of $F$. If $z$ is not equivalent to $x$ in $F$, then find returns the
same root for $z$ in the forest obtained from $F$ by the union of $x$ and $y$ as in $F$.

No hypothesis on $y$ is needed. -/
public theorem find_union_of_unrelated {n : Nat} (forest : Forest n) (x y z : Fin n)
    (hx : ¬Equivalent forest z x) :
    find (union forest x y) z = find forest z := by
  simp [find_union, hx]

/-- **Union in a parent forest with cost.** For a parent forest $F$ and vertices $x$ and $y$, the
costed union returns the union of $x$ and $y$ in $F$ together with a cost equal to the cost of
finding the root of $x$ plus the cost of finding the root of $y$ (each one unit per visited
vertex, including the root), plus one more unit when the roots of $x$ and $y$ are distinct; when
they coincide, union performs no link and none is charged. -/
public def unionWithCost {n : Nat} (forest : Forest n) (x y : Fin n) :
    TimeM Nat (Forest n) :=
  ⟨union forest x y,
    (findWithCost forest x).time + (findWithCost forest y).time +
      (if find forest x = find forest y then 0 else 1)⟩

/-- **Cost bound for union in a parent forest.** For every parent forest $F$ with depth
certificate $d$ and vertices $x$ and $y$, the cost charged for the union of $x$ and $y$ in $F$
(two root searches at one unit per visited vertex, plus one unit for the link when the roots
differ) is at most $d(x) + d(y) + 3$. -/
public theorem unionWithCost_time_le_depth {n : Nat} (forest : Forest n) (x y : Fin n) :
    (unionWithCost forest x y).time ≤ forest.depth x + forest.depth y + 3 := by
  have hx := findWithCost_time_le_depth forest x
  have hy := findWithCost_time_le_depth forest y
  simp only [unionWithCost]
  split_ifs <;> omega

end Cslib.Algorithms.Lean.UnionFind
