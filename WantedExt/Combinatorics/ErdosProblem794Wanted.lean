/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 794
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph

@[expose] public section

open Filter

namespace MathlibExt.Combinatorics.ErdosProblem794Wanted

/-! Source record `FC-ErdosProblem794`, ported from FormalConjectures
`ErdosProblems/794.lean` and checked against erdosproblems.com/794.
The reusable finite-hypergraph predicates live in `MathlibExt`. The historical target remains
the positive proposition even though its external status is resolved false. -/

/-- **Erdős Problem 794 on dense 3-uniform hypergraphs.** The proposition asserts that for every
natural number $n$ and every family $H$ of $3$-element subsets of $\{0, 1, \dots, 3n - 1\}$ with
at least $n^3 + 1$ members, there is a $4$-element set $S$ such that at least $3$ members of $H$
are subsets of $S$, or there is a $5$-element set $S$ such that at least $7$ members of $H$ are
subsets of $S$.

This is Erdős's original question in its positive form; it is known to be false. -/
def conjecture : Prop :=
  ∀ n : ℕ, ∀ H : Finset (Finset (Fin (3 * n))), SetFamily.IsUniform H 3 →
    n ^ 3 + 1 ≤ H.card →
      SetFamily.ContainsSubgraph H 4 3 ∨ SetFamily.ContainsSubgraph H 5 7

/--
**Refutation of Erdős Problem 794.** It is not true that for every natural number $n$ and every
family $H$ of $3$-element subsets of $\{0, 1, \dots, 3n - 1\}$ with at least $n^3 + 1$ members,
there is a $4$-element set $S$ such that at least $3$ members of $H$ are subsets of $S$, or there
is a $5$-element set $S$ such that at least $7$ members of $H$ are subsets of $S$.

Phillip Harris gave an explicit counterexample on $9$ vertices.

Source: Phillip Harris counterexample, formalized by
Aristotle, ChatGPT, and Boris Alexeev at plby/lean-proofs commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos794.lean.
Moved from `OpenConjectures/Combinatorics/ErdosProblem794`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ErdosProblem794Wanted
