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
/-- Only a distinct-index tie increases the second node's saved rank. -/
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

/-- Canonical LINK changes no rank except the distinct tied second root. -/
public theorem rank_link (self : UnionFind) (x y : Fin self.size)
    (yroot : self.parent y = y) (i : Nat) :
    (self.link x y yroot).rank i =
      if x.val ≠ y.val ∧ self.rank x = self.rank y ∧ y.val = i then
        self.rank y + 1 else self.rank i := by
  change UnionFind.rankD (UnionFind.linkAux self.arr x y) i = _
  simpa only [UnionFind.rank, UnionFind.rankD_eq x.isLt,
    UnionFind.rankD_eq y.isLt] using LinkInternal.rankD_linkAux self.arr x y i

/-- Canonical LINK chooses the higher-rank root, and the second root on ties. -/
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

/-- UNION's second FIND reads the saved state of its first FIND. -/
theorem union_carried (self : UnionFind) (x y : Fin self.size) :
    let first := self.find x
    let y₁ : Fin first.1.size := ⟨y.val, by rw [first.2.property]; exact y.isLt⟩
    let second := first.1.find y₁
    let rx : Fin second.1.size :=
      ⟨first.2.val.val, by rw [second.2.property]; exact first.2.val.isLt⟩
    (self.union x y).arr = UnionFind.linkAux second.1.arr rx second.2.val := by
  rfl

/-- Canonical path compression preserves every rank, including default indices. -/
theorem rank_find (self : UnionFind) (x : Fin self.size) (i : Nat) :
    (self.find x).1.rank i = self.rank i := by
  exact UnionFind.rankD_findAux

end LinkInternal

/-- Both actual carried FIND calls preserve ranks before the canonical rank update. -/
public theorem rank_union (self : UnionFind) (x y : Fin self.size) (i : Nat) :
    (self.union x y).rank i =
      if self.rootD x ≠ self.rootD y ∧
          self.rank (self.rootD x) = self.rank (self.rootD y) ∧ self.rootD y = i then
        self.rank (self.rootD y) + 1 else self.rank i := by
  simp only [UnionFind.union]
  rw [rank_link]
  simp only [LinkInternal.rank_find, UnionFind.find_root_2, UnionFind.find_root_1]

namespace LinkInternal

/-- Private source refinement: rank tests, parent writes, rank writes.
The canonical equal-index guard is not a rank test; it performs none of these events. -/
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

/-- The saved array is exactly canonical linkAux's result, not a reference-only result. -/
theorem countedLinkAux_ret (arr : Array UFNode) (x y : Fin arr.size) :
    (countedLinkAux arr x y).ret = UnionFind.linkAux arr x y := by
  by_cases hxy : x.val = y.val
  · simp [countedLinkAux, UnionFind.linkAux, hxy]
  · by_cases hgt : arr[y.val].rank < arr[x.val].rank
    · simp [countedLinkAux, UnionFind.linkAux, hxy, hgt]
    · by_cases heq : arr[x.val].rank = arr[y.val].rank <;>
        simp [countedLinkAux, UnionFind.linkAux, hxy, hgt, heq]

/-- Branch counts concern the same saved-array execution that produced ret. -/
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

/-- Product coordinates preserve the frozen FIND and LINK event conventions.
Each phase executes once and the second FIND reads the first phase's saved store. -/
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

/-- Full array erasure is the direct canonical UNION result, not a detached class oracle. -/
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

/-- Exactly two FIND root tests remain after subtracting their actual carried writes. -/
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
