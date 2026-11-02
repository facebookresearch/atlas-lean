/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 905
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Fin.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Clique
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem905Wanted

/-! Source record `FC-ErdosProblem905`, ported from FormalConjectures
`ErdosProblems/905.lean` and checked against erdosproblems.com/905.
`SimpleGraph.trianglesContaining` is reused from MathlibExt. Status: resolved
true externally by Edwards and Khadzhiivanov–Nikiforov [KhNi79]. This module
states the result but does not prove it; a pinned external Lean proof is linked
in the registry. -/

/-- **Erdős Problem 905 on edges in many triangles.** The proposition asserts that for every
natural number $n$ and every simple graph $G$ on $n$ vertices with more than $n^2/4$ edges, some
edge of $G$ lies in at least $n/6$ triangles of $G$. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) →
    ∃ e : G.edgeSet, (n : ℝ) / 6 ≤ ((G.trianglesContaining e).card : ℝ)

/--
**Edwards–Khadzhiivanov–Nikiforov theorem on edges in many triangles.** For every natural number
$n$, every simple graph $G$ on $n$ vertices with more than $n^2/4$ edges has an edge that lies in
at least $n/6$ triangles of $G$.

This was proved independently by Edwards and by Khadzhiivanov and Nikiforov, and answers Erdős
Problem 905 affirmatively.

Source: External Lean proof of Erdős Problem 905,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos905.lean.
Moved from `OpenConjectures/Combinatorics/ErdosProblem905`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem905Wanted
