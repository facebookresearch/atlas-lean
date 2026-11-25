/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.SequenceCost

/-!
# The inverse-Ackermann bound for union by rank with path compression

Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984)
245–281, §3, Theorem 3: the set union algorithm with linking by rank (or by size) and
compression (or splitting, or halving) runs in `O(n + m α(m + n, n))` time, where `n` is the
number of make-set operations, `m` the number of finds and `α` their inverse Ackermann
function. The bound is optimal for separable algorithms (their §1, Theorem 2). Their proof
uses, and extends, the multiple partition technique of Tarjan, *Efficiency of a good but not
linear set union algorithm*, J. ACM 22(2) (1975) 215–225 (their §3).

The statement uses the cost model of `CSLibExt.Algorithms.Lean.DataStructures.UnionFind.
SequenceCost` for the canonical Batteries union-find (`find` with path compression, union by
rank): a make-set and a link cost one, a find costs the number of nodes on its find path, and a
union is two finds and a link. The proof (their §3: Lemmas 4–6 and the proof of Theorem 3) is
not yet formalized; the weaker `O(n + m log n)` bound is proved as
`UnionByRank.run_empty_cost_le_log`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRank

/-- **Tarjan–van Leeuwen bound for union by rank with path compression.** There is a constant
`C` such that every sequence of set-union operations with `n ≥ 1` make-sets and `m` finds (a
union counting as two finds), run from the empty structure, costs at most
`C (n + m α(m + n, n))`, where `α` is the inverse Ackermann function of Tarjan and van Leeuwen
(Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984),
§3, Theorem 3, linking by rank with compression). -/
theorem_wanted run_empty_cost_le_inverseAckermann :
    ∃ C : ℕ, ∀ ops : List Op, 1 ≤ numMakeSet ops →
      (run ops Batteries.UnionFind.empty).2 ≤
        C * (numMakeSet ops +
          numFinds ops * inverseAckermannTvL (numFinds ops + numMakeSet ops) (numMakeSet ops))

end Cslib.Algorithms.Lean.UnionByRank
