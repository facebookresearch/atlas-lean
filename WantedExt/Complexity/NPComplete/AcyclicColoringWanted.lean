/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC COLORING is NP-complete

Source:
T. F. Coleman and J.-Y. Cai, "The cyclic coloring problem and estimation of sparse Hessian
matrices", SIAM Journal on Algebraic and Discrete Methods 7(2) (1986), 221-235,
doi:10.1137/0607026, Theorem 3.1;
A. V. Kostochka, *Upper bounds of chromatic functions of graphs* (in Russian), doctoral thesis,
Novosibirsk (1978);
Shalu M. A. and C. Antony, "Hardness transitions and uniqueness of acyclic colouring", Discrete
Applied Mathematics 345 (2024), 77-98, doi:10.1016/j.dam.2023.11.030, Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted
public import WantedExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicColoring

open GraphColoring (GraphColoringInstance Graph)
open MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted (IsAcyclicColoring)

/-!
# ACYCLIC COLORING is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have an acyclic `K`-coloring, i.e. a function `f : V → {1, …, K}` with
`f(u) ≠ f(v)` whenever `{u, v} ∈ E`, such that every two color classes together induce a forest
(equivalently, every cycle of `G` uses at least three colors)?

Coleman and Cai (Section 3) define a cyclic `p`-coloring as "a `p`-coloring [that] uses at least
3 colors in every cycle of `G`" and prove (Theorem 3.1, by a transformation from graph
coloring) that the cyclic coloring decision problem, "Given an integer `p ≥ 3` and an arbitrary
graph `G`, is it possible to assign a cyclic `p`-coloring to the nodes of `G`?", is NP-complete.
Shalu and Antony (Section 1) state ACYCLIC COLOURABILITY with input "a graph `G` and a positive
integer `k`" and record that Kostochka (1978) and Coleman and Cai independently proved it
NP-complete. Coleman and Cai exclude `p = 1, 2` only because these cases are solvable in
polynomial time, so the two instance classes give the same complexity; this module follows the
positive-integer form. An acyclic coloring is the one of
`AcyclicChromaticMaxDegreeErdosProblem797Wanted` (`IsAcyclicColoring`): a proper coloring
`f : V → Fin K` in which, for all colors `i, j`, the subgraph induced by the vertices of color
`i` or `j` is acyclic.

The instance type (vertex count, edge list, `K`), the graph (`Graph`, a simple graph on `Fin n`
given by an edge list) and the simple-edge-list well-formedness are reused from
`GraphColoringWanted`; `WellFormed` adds `0 < K`. The vertex count `n` and the bound `K`
are binary, but isolated vertices can take any color, so a certificate needs colors (each below
`K`) only for the at most `2|E|` endpoints of edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: well-formed for GRAPH COLORING (the edge list describes a
simple graph on `Fin n`), and `0 < K`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2

/-- The graph has an acyclic coloring with `K` colors: a proper coloring by `Fin K` in which
every two color classes induce a forest. -/
def AcyclicColoringFeasible (i : GraphColoringInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.2, IsAcyclicColoring (Graph i) f

open Classical in
/-- ACYCLIC COLORING as a decision problem over bitstrings. -/
noncomputable def acyclicColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ AcyclicColoringFeasible i)
  | none => false

/-- **ACYCLIC COLORING is NP-complete.** Source: Coleman and Cai (1986), Theorem 3.1;
Kostochka (1978); Shalu and Antony (2024). -/
public theorem_wanted acyclicColoring_npComplete :
    acyclicColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L acyclicColoringDec

end MetaMathlibExt.Complexity.NPComplete.AcyclicColoring
