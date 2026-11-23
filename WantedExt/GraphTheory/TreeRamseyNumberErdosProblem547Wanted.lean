/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramsey numbers of trees (Erdős Problem 547)

Erdős Problem 547: if `T` is a tree on `n` vertices then `R(T) ≤ 2n - 2`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.TreeRamseyNumberErdosProblem547Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #547, https://www.erdosproblems.com/547 (status
PROVED). UnsolvedMath record UM-30006927 (`EP-547`), dataset ulamai/UnsolvedMath v1.8.0.

`R(G)` is the two-colour Ramsey number, MathlibExt's `SimpleGraph.diagonalGraphRamsey`: the least
`N` such that for every graph `R` on `Fin N` (the red edges; the blue edges form the complement
`Rᶜ`) the graph `G` is a subgraph, not necessarily induced, of `R` or of `Rᶜ`. Trees are
`SimpleGraph.IsTree` on `Fin n`. The statement is for `n ≥ 2`: the one-vertex tree has `R = 1 > 2 ·
1 - 2`. Compared with the formal-conjectures statement `ErdosProblems/547.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 547: every tree `T` on `n ≥ 2` vertices has `R(T) ≤ 2n - 2`. -/
def treeRamseyAtMostTwiceOrder : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ T : SimpleGraph (Fin n), T.IsTree →
    SimpleGraph.diagonalGraphRamsey T ≤ 2 * n - 2

/--
Resolved true: erdosproblems.com/547 notes that the bound follows directly from the Erdős-Sós
conjecture (Erdős Problem 548: a graph on `N ≥ k + 1` vertices with at least `(k - 1) N / 2 + 1`
edges contains every tree on `k + 1` vertices), and the 548 page lists 548 as implying 547.
erdosproblems.com lists 548, for all `N` and `k`, as proved (a proof of the full conjecture by GPT-6
Astra, formalized in Lean) and 547 as proved; the refereed result is Zhao's `R(T) ≤ 2n - 2` for all
large `n`. Source: T. F. Bloom, Erdős Problems, Problem #547, https://www.erdosproblems.com/547
(status PROVED); resolution: Erdős-Sós theorem, erdosproblems.com/548 (proof by GPT-6 Astra,
exposition on the problem page, status PROVED (LEAN)); Y. Zhao, Proof of the (n/2-n/2-n/2)
conjecture for large n, Electron. J. Combin. (2011), Paper 27, erdosproblems.com/547: the bound
follows directly from the Erdős-Sós conjecture (Problem 548, which the 548 page lists as implying
547); Zhao proved R(T) ≤ 2n - 2 for all large n, https://www.erdosproblems.com/548.
-/
public theorem_wanted treeRamseyAtMostTwiceOrder_holds : treeRamseyAtMostTwiceOrder

end MathlibExt.GraphTheory.TreeRamseyNumberErdosProblem547Wanted
