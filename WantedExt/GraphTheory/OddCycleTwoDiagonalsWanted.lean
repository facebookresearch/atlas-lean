/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-1091: every K4-free graph with chromatic number 4 contains an odd cycle
with at least two diagonals.

Graphs are finite simple graphs. Chromatic number 4 is stated as 4-colorable
but not 3-colorable. An odd cycle is an injective cyclic adjacency map from
`ZMod m` for odd `m ≥ 3`; a diagonal is an edge between distinct
nonconsecutive cycle vertices, and two diagonals must differ as vertex
pairs. The record's generalization (an unbounded `f(r)`) is omitted.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.ZMod.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

universe u

namespace MathlibExt.GraphTheory.OddCycleTwoDiagonalsWanted

/-! Source record `EP-1091`. -/

/-- An odd cycle with two diagonals: an injective cyclic adjacency map from
`ZMod m` (`m` odd, `≥ 3`) plus two distinct nonconsecutive adjacent pairs. -/
def HasOddCycleTwoDiagonals {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧ Odd m ∧ ∃ v : ZMod m → V, Function.Injective v ∧
    (∀ i, G.Adj (v i) (v (i + 1))) ∧
    ∃ a b c d : ZMod m,
      a ≠ b ∧ b ≠ a + 1 ∧ a ≠ b + 1 ∧ G.Adj (v a) (v b) ∧
      c ≠ d ∧ d ≠ c + 1 ∧ c ≠ d + 1 ∧ G.Adj (v c) (v d) ∧
      ({a, b} : Finset (ZMod m)) ≠ {c, d}

/-- [EP-1091] Every K4-free 4-chromatic graph has an odd cycle with at least
two diagonals. -/
def conjecture : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.CliqueFree 4 → G.Colorable 4 → ¬ G.Colorable 3 →
    HasOddCycleTwoDiagonals G

/--
Resolved true: Resolved true: erdosproblems.com/1091 records that the K_4-free question was
solved in the affirmative by Voss (Graphs having circuits with at least two chords, J. Combin.
Theory Ser. B 32 (1982) 264-285). The omitted f(r) generalization was answered negatively
(Alexeev et al., arXiv:2604.06609). Source: T. F. Bloom, Erdős Problem #1091, erdosproblems.com
(live page, LaTeX source and forum threads read 2026-10-22), https://www.erdosproblems.com/1091;
H.-J. Voss, Graphs having circuits with at least two chords, J. Combin. Theory Ser. B 32 (1982),
264-285, https://doi.org/10.1016/0095-8956(82)90054-8. Moved from
`OpenConjectures/GraphTheory/OddCycleTwoDiagonals`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.OddCycleTwoDiagonalsWanted
