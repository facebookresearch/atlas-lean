/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/794.lean` (Formal Conjectures), for the conjecture statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/

module

public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
import Mathlib.Data.Fintype.Powerset

/-!
# Refutation of Erdős Problem 794

A family of ten triples on six vertices refutes the conjecture at $n = 2$.
Each four-vertex set contains exactly two triples, and each five-vertex set exactly five.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem794Wanted

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

/-- A six-vertex counterexample. On the cycle `1, 2, 3, 4, 5`, take each adjacent
pair together with either vertex `0` or the cycle vertex opposite the pair. -/
def sixVertexFamily : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 3, 4}, {0, 4, 5}, {0, 5, 1},
   {1, 2, 4}, {2, 3, 5}, {3, 4, 1}, {4, 5, 2}, {5, 1, 3}}

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
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  have hu : SetFamily.IsUniform sixVertexFamily 3 := by
    unfold SetFamily.IsUniform
    decide
  have havoid : ¬ (SetFamily.ContainsSubgraph sixVertexFamily 4 3 ∨
      SetFamily.ContainsSubgraph sixVertexFamily 5 7) := by
    unfold SetFamily.ContainsSubgraph
    decide
  exact havoid (h 2 sixVertexFamily hu (by decide))

end MathlibExt.Combinatorics.ErdosProblem794Wanted
