/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 923
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem923Wanted

/-! Source record `FC-ErdosProblem923`, ported from FormalConjectures
`ErdosProblems/923.lean` (`theorem erdos_923`) and checked against
erdosproblems.com/923. The upstream `answer(True)` is dropped; the
right-hand side is stated directly (FC's `open SimpleGraph` is replaced by
qualified names). Status: resolved true by Rödl [Ro77]; this repository records
the statement but does not include a proof module. -/

/-- **Erdős Problem 923 on triangle-free subgraphs of large chromatic number.** The proposition
asserts that for every natural number $n$ there is a natural number $k$ such that every simple
graph $G$, on any vertex set, whose chromatic number is at least $k$ has a triangle-free subgraph
$H$ on the same vertex set whose chromatic number is at least $n$. Chromatic numbers may be
infinite. -/
def conjecture : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, ∀ (V : Type*) (G : SimpleGraph V),
    (k : ℕ∞) ≤ G.chromaticNumber →
      ∃ H ≤ G, (n : ℕ∞) ≤ H.chromaticNumber ∧ H.CliqueFree 3

/--
**Rödl's theorem on triangle-free subgraphs.** For every natural number $n$ there is a natural
number $k$ such that every simple graph $G$, on any vertex set, whose chromatic number is at least
$k$ has a triangle-free subgraph $H$ on the same vertex set whose chromatic number is at least
$n$. Chromatic numbers may be infinite.

This answers Erdős Problem 923 affirmatively; it was proved by Rödl.

Source:
Vojtěch Rödl, On the chromatic number of subgraphs of a given graph, Proceedings of the American
Mathematical Society 64 (1977), 370–371, https://doi.org/10.1090/S0002-9939-1977-0469806-4.
Moved from `OpenConjectures/Combinatorics/ErdosProblem923`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem923Wanted
