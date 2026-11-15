/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on unit 2-interval graphs is NP-complete

Source:
M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple interval
graphs", Algorithmica 71 (2015), 812-836, doi:10.1007/s00453-013-9828-6, Section 5 (Theorem 10
of arXiv:1201.0043v2: MAXIMUM CLIQUE is NP-complete for unit 2-interval graphs);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.SetNotation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueUnitTwoInterval

/-!
# CLIQUE on unit 2-interval graphs is NP-complete

INSTANCE: a unit `2`-interval graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, i.e., a set `V' ⊆ V` with `|V'| ≥ K`
such that every two vertices in `V'` are joined by an edge?

This is CLIQUE ([GT19]) restricted to the unit `2`-interval graphs (ISGCI `gc_877`). Following
Francis, Gonçalves and Ochem (Section 1), a `2`-interval is the union of two intervals on the
real line, a `2`-interval graph is the intersection graph of a family of `2`-intervals, one per
vertex, two distinct vertices being adjacent exactly when their `2`-intervals intersect, and the
unit `2`-interval graphs are those with such a representation in which all the intervals have
the same length. This is the representation of `IntervalNumberAtMostK.IsMultipleIntervalGraph 2`
(closed intervals indexed by `Fin 2`, possibly repeated) with every interval of length `1`; a
common length `c > 0` scales to `1`, and a common length `0` (points) can first be widened to a
common small length without changing which intervals meet, the model being finite. The model is
not part of the input; when a real model exists, one with rational endpoints of polynomial size
exists too (the conditions are linear inequalities in the left endpoints), so a model is a
certificate. The graph is simple and given by an edge list on `Fin n`. The bound `0 < K ≤ |V|`
is the instance class of [GT19].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CliqueUnitTwoIntervalInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueUnitTwoIntervalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- `H` is a unit `2`-interval graph: each vertex `v` is assigned two closed real intervals of
length one, `[l v j, l v j + 1]` (`j : Fin 2`, possibly equal), and two distinct vertices are
adjacent in `H` exactly when the unions of their intervals intersect. -/
def IsUnitTwoIntervalGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ l : Fin n → Fin 2 → ℝ, ∀ u v, u ≠ v →
    (H.Adj u v ↔
      ((⋃ j, Set.Icc (l u j) (l u j + 1)) ∩ (⋃ j, Set.Icc (l v j) (l v j + 1))).Nonempty)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ n`, and the
graph is a unit `2`-interval graph. -/
def WellFormed (i : CliqueUnitTwoIntervalInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ IsUnitTwoIntervalGraph (Graph i)

/-- The graph has a clique of size `K` or more. -/
def CliqueUnitTwoIntervalFeasible (i : CliqueUnitTwoIntervalInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on unit 2-interval graphs as a decision problem over bitstrings. -/
noncomputable def cliqueUnitTwoIntervalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueUnitTwoIntervalInstance) x with
  | some i => decide (WellFormed i ∧ CliqueUnitTwoIntervalFeasible i)
  | none => false

/-- **CLIQUE on unit 2-interval graphs is NP-complete.** Source: Francis, Gonçalves and Ochem
(2015), Section 5; Garey and Johnson (1979), [GT19]. -/
public theorem_wanted cliqueUnitTwoInterval_npComplete :
    cliqueUnitTwoIntervalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueUnitTwoIntervalDec

end MetaMathlibExt.Complexity.NPComplete.CliqueUnitTwoInterval
