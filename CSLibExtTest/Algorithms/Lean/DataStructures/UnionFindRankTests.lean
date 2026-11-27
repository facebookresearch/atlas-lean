/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Rank
public meta import Batteries.Data.UnionFind.Basic
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Rank

/-!
# Tests for the rank bounds of union by rank

A structure on four nodes built by three unions has a root of rank two whose class has the four
nodes, so the bound `2 ^ rank ≤ class size` is attained; the theorems apply to it.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRankTests

open Batteries UnionByRank

/-- `union` on natural-number indices, ignoring out-of-range arguments. -/
def unionNat (uf : UnionFind) (x y : ℕ) : UnionFind :=
  if h : x < uf.size ∧ y < uf.size then uf.union ⟨x, h.1⟩ ⟨y, h.2⟩ else uf

theorem reachable_unionNat {uf : UnionFind} (h : Reachable uf) (x y : ℕ) :
    Reachable (unionNat uf x y) := by
  unfold unionNat
  split
  · exact Reachable.union _ _ h
  · exact h

/-- Four make-sets. -/
def four : UnionFind := UnionFind.empty.push.push.push.push

/-- Unions `{0, 1}`, `{2, 3}`, then the two pairs. -/
def merged : UnionFind := unionNat (unionNat (unionNat four 0 1) 2 3) 0 2

theorem reachable_four : Reachable four :=
  .push (.push (.push (.push .empty)))

theorem reachable_merged : Reachable merged :=
  reachable_unionNat (reachable_unionNat (reachable_unionNat reachable_four 0 1) 2 3) 0 2

#guard merged.size == 4
#guard merged.rootD 0 == 3 && merged.rootD 1 == 3 && merged.rootD 2 == 3
#guard merged.rank 3 == 2
#guard classSize merged 3 == 4

/-- The rank lemma on this structure; at its root `3` it is the tight case `2 ^ 2 ≤ 4` checked
above. -/
example (r : ℕ) (hr : r < merged.size) (hroot : merged.parent r = r) :
    2 ^ merged.rank r ≤ classSize merged r :=
  two_pow_rank_le_classSize reachable_merged hr hroot

example (i : ℕ) : merged.rank i ≤ Nat.log 2 merged.size :=
  rank_le_log reachable_merged i

example (i : ℕ) : merged.parent^[Nat.log 2 merged.size] i = merged.rootD i :=
  iterate_parent_log reachable_merged i

end Cslib.Algorithms.Lean.UnionByRankTests
