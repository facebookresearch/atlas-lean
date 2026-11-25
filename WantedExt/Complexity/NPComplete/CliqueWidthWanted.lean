/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE-WIDTH is NP-complete

Source:
M. R. Fellows, F. A. Rosamond, U. Rotics and S. Szeider, "Clique-width is NP-complete",
SIAM Journal on Discrete Mathematics 23(2) (2009), 909-939, doi:10.1137/070687256;
definition of `k`-expressions and clique-width: B. Courcelle and S. Olariu, "Upper bounds to the
clique width of graphs", Discrete Applied Mathematics 101(1-3) (2000), 77-114,
doi:10.1016/S0166-218X(99)00184-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Sum

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueWidth

/-!
# CLIQUE-WIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected, with at least one vertex) and an
integer `K`. QUESTION: is the clique-width of `G` at most `K`? Fellows, Rosamond, Rotics and Szeider (2009): "given a graph
`G` and an integer `k`, deciding whether the clique-width of `G` is at most `k` is NP-complete."

The clique-width of `G` (Courcelle and Olariu, 2000) is the least `k` such that `G` is the
graph of a `k`-expression: a term built from `k` vertex labels by the operations
- `i(v)`: create a single vertex `v` with label `i`;
- `G ⊕ H`: disjoint union of two labelled graphs;
- `η_{i,j}` with `i ≠ j`: add an edge between every vertex labelled `i` and every vertex
  labelled `j`;
- `ρ_{i→j}`: relabel every vertex with label `i` to label `j`.

`Generated k V H l` says that the graph `H` on the vertex type `V` with labelling
`l : V → Fin k` is the value of some `k`-expression; its four constructors are the four
operations (disjoint union is Mathlib's `SimpleGraph.sum`, `⊕g`, on `V ⊕ W`). The labels are
`Fin k`, so `k` labels. The clique-width of `G` is at most `K` when `G` is isomorphic (`≃g`) to
the graph of some `K`-expression, under any final labelling. Every `k`-expression creates at
least one vertex, so clique-width is defined only for graphs with a vertex, and `WellFormed`
requires `0 < n`. With `K = 0` no vertex can be created, so `K = 0` is a no-instance.

The graph is given by an edge list on `Fin n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev CliqueWidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueWidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- `Generated k V H l`: the graph `H` on `V` with vertex labels `l : V → Fin k` is the value of
a `k`-expression. -/
inductive Generated (k : ℕ) : (V : Type) → SimpleGraph V → (V → Fin k) → Prop
  /-- `i(v)`: a single vertex with label `i`. -/
  | vertex (i : Fin k) : Generated k Unit ⊥ fun _ => i
  /-- `G ⊕ H`: the disjoint union of two labelled graphs. -/
  | union {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {l : V → Fin k}
      {m : W → Fin k} :
      Generated k V G l → Generated k W H m → Generated k (V ⊕ W) (G ⊕g H) (Sum.elim l m)
  /-- `η_{i,j}`, `i ≠ j`: join every vertex labelled `i` to every vertex labelled `j`. -/
  | join {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i j : Fin k) (hij : i ≠ j) :
      Generated k V G l →
        Generated k V (G ⊔ SimpleGraph.fromRel fun u v => l u = i ∧ l v = j) l
  /-- `ρ_{i→j}`: relabel every vertex labelled `i` to `j`. -/
  | relabel {V : Type} {G : SimpleGraph V} {l : V → Fin k} (i j : Fin k) :
      Generated k V G l → Generated k V G fun v => if l v = i then j else l v

/-- Well-formedness of an instance: the graph has at least one vertex (clique-width is defined
for such graphs), and the edge list describes a simple graph (no duplicate edges in either
orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CliqueWidthInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- The clique-width of the graph is at most `K`: the graph is isomorphic to the graph of some
`K`-expression. -/
def CliqueWidthFeasible (i : CliqueWidthInstance) : Prop :=
  ∃ (V : Type) (H : SimpleGraph V) (l : V → Fin i.2.2), Generated i.2.2 V H l ∧
    Nonempty (Graph i ≃g H)

open Classical in
/-- CLIQUE-WIDTH as a decision problem over bitstrings. -/
noncomputable def cliqueWidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueWidthInstance) x with
  | some i => decide (WellFormed i ∧ CliqueWidthFeasible i)
  | none => false

/-- **CLIQUE-WIDTH is NP-complete.** Source: Fellows, Rosamond, Rotics and Szeider (2009). -/
public theorem_wanted cliqueWidth_npComplete :
    cliqueWidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueWidthDec

end MetaMathlibExt.Complexity.NPComplete.CliqueWidth
