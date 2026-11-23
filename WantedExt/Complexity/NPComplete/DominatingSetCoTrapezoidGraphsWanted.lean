/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for co-trapezoid graphs is NP-complete

Source:
J. M. Keil and P. Belleville, "Dominating the complements of bounded tolerance graphs and the
complements of trapezoid graphs", Discrete Applied Mathematics 140(1-3) (2004), 73-89,
doi:10.1016/j.dam.2003.04.004;
I. Dagan, M. C. Golumbic and R. Y. Pinter, "Trapezoid graphs and their coloring", Discrete
Applied Mathematics 21 (1988), 35-46, doi:10.1016/0166-218X(88)90032-7 (trapezoid graphs);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetCoTrapezoidGraphs

/-!
# DOMINATING SET for co-trapezoid graphs is NP-complete

INSTANCE: a co-trapezoid graph `G = (V, E)`, that is, a graph whose complement is a trapezoid
graph, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex not in `V'` is joined to at least one member of `V'`?

A trapezoid graph (Dagan, Golumbic and Pinter 1988) is the intersection graph of a family of
trapezoids between two parallel lines, each trapezoid having two corners on each line. Here the
lines are `y = 1` and `y = 0` in `ℝ × ℝ`; vertex `v` gets the trapezoid with top side
`[a v, b v]` and bottom side `[c v, d v]` (`a v ≤ b v`, `c v ≤ d v`), the convex hull (Mathlib's
`convexHull`) of its four corners (`trapezoid`), and two distinct vertices are adjacent exactly
when their trapezoids meet (`IsTrapezoidGraph`). The complement of `G` is Mathlib's `Gᶜ`.

This is the restriction of DOMINATING SET ([GT2], `DominatingSetWanted`) to co-trapezoid graphs.
The instance type, the graph and the question are the parent's
(`DominatingSet.DominatingSetInstance`, `DominatingSet.Graph`,
`DominatingSet.DominatingSetFeasible`); `WellFormed` is the parent's plus the restriction and
Garey and Johnson's bounds `0 < K ≤ |V|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The trapezoid between the lines `y = 1` and `y = 0` with top side `[a, b]` and bottom side
`[c, d]`: the convex hull of its corners `(a, 1)`, `(b, 1)`, `(c, 0)`, `(d, 0)`. -/
def trapezoid (a b c d : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(a, 1), (b, 1), (c, 0), (d, 0)}

/-- `H` is a trapezoid graph: each vertex `v` has a trapezoid with top side `[a v, b v]` and
bottom side `[c v, d v]`, and two distinct vertices are adjacent exactly when their trapezoids
intersect. -/
def IsTrapezoidGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ a b c d : V → ℝ, (∀ v, a v ≤ b v ∧ c v ≤ d v) ∧
    ∀ u v, u ≠ v → (H.Adj u v ↔
      (trapezoid (a u) (b u) (c u) (d u) ∩ trapezoid (a v) (b v) (c v) (d v)).Nonempty)

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the complement
of the graph is a trapezoid graph, and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSet.DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ IsTrapezoidGraph (DominatingSet.Graph i)ᶜ ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET for co-trapezoid graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetCoTrapezoidGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSet.DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSet.DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET for co-trapezoid graphs is NP-complete.** Source: Keil and Belleville
(2004); Garey and Johnson (1979), [GT2]. -/
public theorem_wanted dominatingSetCoTrapezoidGraphs_npComplete :
    dominatingSetCoTrapezoidGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetCoTrapezoidGraphsDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetCoTrapezoidGraphs
