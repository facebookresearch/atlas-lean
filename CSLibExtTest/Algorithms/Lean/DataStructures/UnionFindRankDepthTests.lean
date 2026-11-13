/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.RankDepth
import Batteries.Data.UnionFind.Basic
import Mathlib.Data.Fin.VecNotation

/-! A finite-chain instance and canonical `Batteries.UnionFind` consumers of the rank/depth
bounds. -/

namespace Batteries.UnionFind

/-- Boundary check: on a two-node chain `0 -> 1` (root `1`) in `Fin 2`, the
find depth of `0` is at most the root's rank, with ranks `0, 5`. -/
example : (1 : ℕ) ≤ ![0, 5] ((fun i : Fin 2 => ![1, 1] i)^[1] (0 : Fin 2)) :=
  find_depth_le_rank (p := fun i : Fin 2 => ![1, 1] i) (r := ![0, 5])
    (by decide) 0 1 (by decide) (by decide)

/-- The canonical union-find: nonroot parent steps raise the saved rank (`rank_lt`), so
`rank_iterate` applies to `u.parent : ℕ → ℕ` and `u.rank`. -/
example (u : UnionFind) (x k : ℕ)
    (hk : ∀ j < k, u.parent (u.parent^[j] x) ≠ u.parent^[j] x) :
    u.rank x + k ≤ u.rank (u.parent^[k] x) :=
  rank_iterate (fun z h => rank_lt (self := u) (i := z) h) x k hk

/-- In the canonical union-find, a node whose parent chain reaches a root after `k` nonroot
steps has depth `k` at most that root's rank. -/
example (u : UnionFind) (x k : ℕ)
    (hk : ∀ j < k, u.parent (u.parent^[j] x) ≠ u.parent^[j] x)
    (hroot : u.parent (u.parent^[k] x) = u.parent^[k] x) :
    k ≤ u.rank (u.parent^[k] x) :=
  find_depth_le_rank (fun z h => rank_lt (self := u) (i := z) h) x k hk hroot

end Batteries.UnionFind
