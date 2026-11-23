/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.UnionFind.Lemmas
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod

import all CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find

/-!
# Canonical rank-directed union and link

The three public facts give the complete saved rank frame and the deterministic
rank-selected root of canonical Batteries LINK/UNION. Private source-refinement
proofs count actual rank tests and parent/rank assignments, and reuse the settled
FIND refinement through a private import rather than a copied implementation.

Distinct-root rank branches follow CLRS4 §19.3, printed530. Equal-index LINK
returns without events as a disclosed library extension. These selected events
are not the full inverse-Ackermann, RAM, bit or space bound. Codex conversion
under Adam Kiezun's explicit producer override.
-/

open Batteries Cslib.Algorithms.Lean

namespace Batteries.UnionFind

namespace LinkInternal
/-- **Ranks after linking two nodes of an array.** For an array $A$ of union-find nodes, write
$\rho_A(i)$ for the rank stored at index $i$ of $A$, or $0$ if $i$ is not an index of $A$. Let
$x, y$ be indices of $A$ and let $A'$ be the array obtained from $A$ by the Batteries link by rank
of $x$ and $y$. Then for every natural number $i$, $\rho_{A'}(i) = \rho_A(y) + 1$ if $x \ne y$,
$\rho_A(x) = \rho_A(y)$ and $i = y$, and $\rho_{A'}(i) = \rho_A(i)$ otherwise. -/
theorem rankD_linkAux (arr : Array UFNode) (x y : Fin arr.size) (i : Nat) :
    UnionFind.rankD (UnionFind.linkAux arr x y) i =
      if x.val ≠ y.val ∧ arr[x.val].rank = arr[y.val].rank ∧ y.val = i then
        arr[y.val].rank + 1 else UnionFind.rankD arr i := by
  have hx := UnionFind.rankD_eq x.isLt (arr := arr)
  have hy := UnionFind.rankD_eq y.isLt (arr := arr)
  dsimp only [UnionFind.linkAux]
  split
  · simp_all
  · split
    · rename_i hgt
      have hne := (Nat.ne_of_lt hgt).symm
      rw [UnionFind.rankD_set]
      split <;> simp_all
    · split
      · rw [UnionFind.rankD_set, UnionFind.rankD_set]
        split <;> split <;> simp_all
      · rw [UnionFind.rankD_set]
        split <;> simp_all

end LinkInternal

/-- **Ranks after linking in a union-find structure.** Let $S$ be a union-find structure, write
$\rho(i)$ for the rank of $i$ in $S$ ($0$ if $i$ is not a node of $S$), and let $x, y$ be nodes of
$S$ such that $y$ is a root, that is, the parent of $y$ is $y$. Let $S'$ be the result of linking
$x$ and $y$ by rank. Then for every natural number $i$, the rank of $i$ in $S'$ is $\rho(y) + 1$
if $x \ne y$, $\rho(x) = \rho(y)$ and $i = y$, and is $\rho(i)$ otherwise. -/
public theorem rank_link (self : UnionFind) (x y : Fin self.size)
    (yroot : self.parent y = y) (i : Nat) :
    (self.link x y yroot).rank i =
      if x.val ≠ y.val ∧ self.rank x = self.rank y ∧ y.val = i then
        self.rank y + 1 else self.rank i := by
  change UnionFind.rankD (UnionFind.linkAux self.arr x y) i = _
  simpa only [UnionFind.rank, UnionFind.rankD_eq x.isLt,
    UnionFind.rankD_eq y.isLt] using LinkInternal.rankD_linkAux self.arr x y i

/-- **Linking two roots by rank.** Let $U$ be a union-find structure on $\{0, \dots, n-1\}$ and
let $x, y < n$ be roots of $U$, i.e. each is its own parent. Let $U'$ be obtained by linking $x$
and $y$ by rank: nothing changes if $x = y$; otherwise, if $\operatorname{rank}(y) <
\operatorname{rank}(x)$ then $y$ gets parent $x$, and if not then $x$ gets parent $y$ and, when
the two ranks are equal, the rank of $y$ increases by one. Then for every natural number $i$,
where the root of an index $i \ge n$ is $i$ itself: if the root of $i$ in $U$ is $x$ or $y$, the
root of $i$ in $U'$ is $x$ when $\operatorname{rank}(y) < \operatorname{rank}(x)$ and $y$
otherwise; if the root of $i$ in $U$ is neither $x$ nor $y$, its root in $U'$ is the same as in
$U$. -/
public theorem rootD_link_eq_ite (self : UnionFind) (x y : Fin self.size)
    (xroot : self.parent x = x) (yroot : self.parent y = y) (i : Nat) :
    (self.link x y yroot).rootD i =
      if self.rootD i = x.val ∨ self.rootD i = y.val then
        if self.rank y < self.rank x then x.val else y.val
      else self.rootD i := by
  obtain ⟨r, _, hi⟩ := UnionFind.root_link xroot yroot
  let w : Fin self.size := if self.rank y < self.rank x then x else y
  have hw : (self.link x y yroot).parent w.val = w.val := by
    by_cases hxy : x.val = y.val
    · simp [UnionFind.parent_link, w, hxy, yroot]
    · by_cases hgt : self.rank y < self.rank x <;>
        simp [UnionFind.parent_link, w, hxy, hgt, xroot, yroot]
  have hold : self.rootD w.val = w.val := by
    apply UnionFind.rootD_eq_self.mpr
    by_cases hgt : self.rank y < self.rank x <;> simp [w, hgt, xroot, yroot]
  have hmem : self.rootD w.val = x.val ∨ self.rootD w.val = y.val := by
    rw [hold]
    by_cases hgt : self.rank y < self.rank x <;> simp [w, hgt]
  have hr : r.val = w.val := by
    have h := hi w.val
    rw [ite_eq_left hmem, UnionFind.rootD_eq_self.mpr hw] at h
    exact h.symm
  rw [hi i, hr]
  by_cases hgt : self.rank y < self.rank x <;> simp [w, hgt]

namespace LinkInternal

/-- **Union unfolds to two finds and a link.** Let $U$ be a union-find structure on
$\{0, \dots, n-1\}$ and let $x, y < n$. Run find with path compression on $x$ in $U$, giving a
structure $U_1$ and a root $r_x$; then run find on $y$ in $U_1$ (not in $U$), giving a structure
$U_2$ and a root $r_y$. Then the node array of the union of $x$ and $y$ in $U$ equals the array
obtained from the node array of $U_2$ by linking $r_x$ and $r_y$ by rank: nothing changes if
$r_x = r_y$; otherwise, if $\operatorname{rank}(r_y) < \operatorname{rank}(r_x)$ then $r_y$ gets
parent $r_x$, and if not then $r_x$ gets parent $r_y$ and, when the two ranks are equal, the rank
of $r_y$ increases by one. -/
theorem union_carried (self : UnionFind) (x y : Fin self.size) :
    let first := self.find x
    let y₁ : Fin first.1.size := ⟨y.val, by rw [first.2.property]; exact y.isLt⟩
    let second := first.1.find y₁
    let rx : Fin second.1.size :=
      ⟨first.2.val.val, by rw [second.2.property]; exact first.2.val.isLt⟩
    (self.union x y).arr = UnionFind.linkAux second.1.arr rx second.2.val := by
  rfl

/-- **Path compression preserves ranks.** Let $S$ be a union-find structure and $x$ a node of
$S$, and let $S'$ be the structure returned by FIND on $x$ with path compression. For every
natural number $i$, the rank of $i$ in $S'$ equals the rank of $i$ in $S$, where the rank of an
index that is not a node is $0$. -/
theorem rank_find (self : UnionFind) (x : Fin self.size) (i : Nat) :
    (self.find x).1.rank i = self.rank i := by
  exact UnionFind.rankD_findAux

end LinkInternal

/-- **Ranks after a union.** Let $S$ be a union-find structure, write $\rho(i)$ for the rank of
$i$ in $S$ ($0$ if $i$ is not a node of $S$) and $r(i)$ for the root of $i$ in $S$. For nodes
$x, y$ of $S$ and every natural number $i$, the rank of $i$ in the union of $x$ and $y$ in $S$
(union by rank with path compression) is $\rho(r(y)) + 1$ if $r(x) \ne r(y)$,
$\rho(r(x)) = \rho(r(y))$ and $r(y) = i$, and is $\rho(i)$ otherwise. -/
public theorem rank_union (self : UnionFind) (x y : Fin self.size) (i : Nat) :
    (self.union x y).rank i =
      if self.rootD x ≠ self.rootD y ∧
          self.rank (self.rootD x) = self.rank (self.rootD y) ∧ self.rootD y = i then
        self.rank (self.rootD y) + 1 else self.rank i := by
  simp only [UnionFind.union]
  rw [rank_link]
  simp only [LinkInternal.rank_find, UnionFind.find_root_2, UnionFind.find_root_1]

namespace LinkInternal

/-- **Linking by rank with operation counts.** Given an array $A$ of union-find nodes, each
storing a parent index and a rank, and indices $x, y$ of $A$, this computation returns an array
together with a count $(t, p, w)$ of rank tests $t$, parent writes $p$ and rank writes $w$. If
$x = y$ it returns $A$ with count $(0, 0, 0)$. Otherwise it makes one rank test; if the rank of $y$
is less than the rank of $x$, it sets the parent of $y$ to $x$ (one parent write). If not, it sets
the parent of $x$ to $y$ (one parent write) and makes a second rank test, and if the ranks of $x$
and $y$ are equal it also increases the rank of $y$ by one (one rank write).

The equality test $x = y$ is not counted as a rank test. -/
@[no_expose] def countedLinkAux (arr : Array UFNode) (x y : Fin arr.size) :
    TimeM (Nat × Nat × Nat) (Array UFNode) := do
  if x.val = y then
    pure arr
  else
    let nx := arr[x.val]
    let ny := arr[y.val]
    TimeM.tick (1, 0, 0)
    if ny.rank < nx.rank then
      TimeM.tick (0, 1, 0)
      pure (arr.set y { ny with parent := x })
    else
      TimeM.tick (0, 1, 0)
      let arr₁ := arr.set x { nx with parent := y }
      TimeM.tick (1, 0, 0)
      if nx.rank = ny.rank then
        TimeM.tick (0, 0, 1)
        pure (arr₁.set y { ny with rank := ny.rank + 1 } (by simp [arr₁]))
      else
        pure arr₁

/-- **Counted linking returns the linked array.** For an array $A$ of union-find nodes and
indices $x, y$ of $A$, the array returned by counted linking of $x$ and $y$ in $A$ is exactly the
array produced by the uncounted Batteries link by rank of $x$ and $y$ in $A$. -/
theorem countedLinkAux_ret (arr : Array UFNode) (x y : Fin arr.size) :
    (countedLinkAux arr x y).ret = UnionFind.linkAux arr x y := by
  by_cases hxy : x.val = y.val
  · simp [countedLinkAux, UnionFind.linkAux, hxy]
  · by_cases hgt : arr[y.val].rank < arr[x.val].rank
    · simp [countedLinkAux, UnionFind.linkAux, hxy, hgt]
    · by_cases heq : arr[x.val].rank = arr[y.val].rank <;>
        simp [countedLinkAux, UnionFind.linkAux, hxy, hgt, heq]

/-- **Operation counts of linking by rank.** Let $A$ be an array of union-find nodes, let $x, y$
be indices of $A$, and write $r_x$ and $r_y$ for the ranks stored at $x$ and $y$. Counted linking
of $x$ and $y$ in $A$ makes $(t, p, w)$ rank tests, parent writes and rank writes, where
$(t, p, w)$ is $(0, 0, 0)$ if $x = y$, is $(1, 1, 0)$ if $x \ne y$ and $r_y < r_x$, is
$(2, 1, 1)$ if $x \ne y$ and $r_x = r_y$, and is $(2, 1, 0)$ otherwise, that is, if $x \ne y$
and $r_x < r_y$. -/
theorem countedLinkAux_time (arr : Array UFNode) (x y : Fin arr.size) :
    (countedLinkAux arr x y).time =
      if x.val = y.val then (0, 0, 0)
      else if arr[y.val].rank < arr[x.val].rank then (1, 1, 0)
      else if arr[x.val].rank = arr[y.val].rank then (2, 1, 1)
      else (2, 1, 0) := by
  by_cases hxy : x.val = y.val
  · simp [countedLinkAux, hxy]
    rfl
  · by_cases hgt : arr[y.val].rank < arr[x.val].rank
    · simp [countedLinkAux, hxy, hgt]
    · by_cases heq : arr[x.val].rank = arr[y.val].rank <;>
        simp [countedLinkAux, hxy, hgt, heq]

/-- **Union by rank with operation counts.** For a union-find structure $S$ and indices $x, y$
of $S$, this computation runs counted FIND on $x$ in $S$, giving a structure $S_1$ and a root
$r_x$; then counted FIND on $y$ in $S_1$, giving a structure $S_2$ and a root $r_y$; then counted
linking of $r_x$ and $r_y$ in the node array of $S_2$. It returns the array produced by the
linking, with cost $((a, b), (t, p, w))$, where $a$ and $b$ are the total numbers of root tests
and parent writes of the two FIND calls, and $(t, p, w)$ counts the rank tests, parent writes and
rank writes of the linking. -/
@[no_expose] def countedUnion (self : UnionFind) (x y : Fin self.size) :
    TimeM ((Nat × Nat) × (Nat × Nat × Nat)) (Array UFNode) :=
  let first := Internal.countedFind self x
  let y₁ : Fin first.ret.1.size :=
    ⟨y.val, by rw [first.ret.2.property]; exact y.isLt⟩
  let second := Internal.countedFind first.ret.1 y₁
  let rx : Fin second.ret.1.size :=
    ⟨first.ret.2.val.val, by rw [second.ret.2.property]; exact first.ret.2.val.isLt⟩
  let linked := LinkInternal.countedLinkAux second.ret.1.arr rx second.ret.2.val
  ⟨linked.ret, (first.time + second.time, linked.time)⟩

/-- **Counted union returns the union's array.** For a union-find structure $S$ and indices
$x, y$ of $S$, the array returned by the counted union of $x$ and $y$ in $S$ equals the node array
of the Batteries union of $x$ and $y$ in $S$ (union by rank with path compression). -/
theorem countedUnion_ret (self : UnionFind) (x y : Fin self.size) :
    (countedUnion self x y).ret = (self.union x y).arr := by
  let last (first : (s : UnionFind) × {_root : Fin s.size // s.size = self.size})
      (second : (s : UnionFind) × {_root : Fin s.size // s.size = first.1.size}) :=
    let rx : Fin second.1.size :=
      ⟨first.2.val.val, by rw [second.2.property]; exact first.2.val.isLt⟩
    (LinkInternal.countedLinkAux second.1.arr rx second.2.val).ret
  let finish (first : (s : UnionFind) × {_root : Fin s.size // s.size = self.size}) :=
    let y₁ : Fin first.1.size := ⟨y.val, by rw [first.2.property]; exact y.isLt⟩
    last first (Internal.countedFind first.1 y₁).ret
  change finish (Internal.countedFind self x).ret = _
  rw [Internal.countedFind_ret]
  dsimp only [finish]
  rw [Internal.countedFind_ret]
  dsimp only [last]
  rw [LinkInternal.countedLinkAux_ret]
  exact (union_carried self x y).symm

/-- **The FIND phases of a union make two more root tests than parent writes.** For a
union-find structure $S$ and indices $x, y$ of $S$, in the counted union of $x$ and $y$ in $S$ the
total number of root tests made by its two FIND calls equals the total number of parent writes
they make plus $2$. -/
theorem countedUnion_find_balance (self : UnionFind) (x y : Fin self.size) :
    (countedUnion self x y).time.1.1 = (countedUnion self x y).time.1.2 + 2 := by
  let first := Internal.countedFind self x
  let y₁ : Fin first.ret.1.size :=
    ⟨y.val, by rw [first.ret.2.property]; exact y.isLt⟩
  let second := Internal.countedFind first.ret.1 y₁
  have hf : first.time.1 = first.time.2 + 1 :=
    Internal.countedAux_time_balance self x
  have hs : second.time.1 = second.time.2 + 1 :=
    Internal.countedAux_time_balance first.ret.1 y₁
  change first.time.1 + second.time.1 = (first.time.2 + second.time.2) + 2
  omega

end LinkInternal

end Batteries.UnionFind
