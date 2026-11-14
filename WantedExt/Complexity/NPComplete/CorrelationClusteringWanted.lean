/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CORRELATION CLUSTERING is NP-complete

Source:
N. Bansal, A. Blum and S. Chawla, "Correlation clustering", Machine Learning 56 (2004),
89-113, doi:10.1023/B:MACH.0000033116.57574.95, Section 3 (decision version of minimizing
disagreements; reduction from PARTITION INTO TRIANGLES).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CorrelationClustering

/-!
# CORRELATION CLUSTERING is NP-complete

INSTANCE: a complete graph on `n` vertices in which every edge `{u, v}` is labeled `+` or `-`,
and an integer `K ≥ 0`.
QUESTION: is there a clustering (a partition of the vertices) with at most `K` disagreements,
where an edge is a disagreement (a mistake) if it is labeled `+` and its endpoints lie in
different clusters, or it is labeled `-` and its endpoints lie in the same cluster?

The vertices are `0, …, n - 1` and the labels are given as an `n × n` Boolean matrix (row `u`,
column `v` is `true` iff the edge `{u, v}` is labeled `+`), which must be symmetric; its
diagonal is not used. This is the input of the source, a complete graph with a label on each
edge, so the vertex count is not succinct. A clustering is given by a map
`c : Fin n → Fin n` sending each vertex to the index of its cluster: every partition of `n`
vertices has at most `n` blocks, and unused indices are empty blocks, which do not affect the
count. The edges are counted once each, as the pairs `u < v`.

The problem is also known as CLUSTER EDITING: the `+` edges form a graph, and the
disagreements of a clustering are the edges that must be deleted or added to turn that graph
into the disjoint union of cliques given by the clusters.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the `n × n` label matrix (`true` is `+`, `false` is `-`) and the
bound `K`. -/
abbrev CorrelationClusteringInstance := List (List Bool) × ℕ

/-- The label of the edge `{u, v}`: entry `(u, v)` of the matrix (`false` outside it). -/
def label (i : CorrelationClusteringInstance) (u v : ℕ) : Bool :=
  (i.1.getD u []).getD v false

/-- Well-formedness of an instance: the label matrix is square and symmetric. -/
def WellFormed (i : CorrelationClusteringInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    ∀ u < i.1.length, ∀ v < i.1.length, label i u v = label i v u

/-- The number of disagreements of the clustering `c`: the edges `{u, v}` (`u < v`) labeled `+`
whose endpoints lie in different clusters, plus those labeled `-` whose endpoints lie in the
same cluster. -/
def disagreements (i : CorrelationClusteringInstance) (c : Fin i.1.length → Fin i.1.length) :
    ℕ :=
  ((Finset.univ : Finset (Fin i.1.length × Fin i.1.length)).filter fun e =>
    e.1 < e.2 ∧
      ((label i e.1 e.2 = true ∧ c e.1 ≠ c e.2) ∨
        (label i e.1 e.2 = false ∧ c e.1 = c e.2))).card

/-- Some clustering has at most `K` disagreements. -/
def CorrelationClusteringFeasible (i : CorrelationClusteringInstance) : Prop :=
  ∃ c : Fin i.1.length → Fin i.1.length, disagreements i c ≤ i.2

open Classical in
/-- CORRELATION CLUSTERING as a decision problem over bitstrings. -/
noncomputable def correlationClusteringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CorrelationClusteringInstance) x with
  | some i => decide (WellFormed i ∧ CorrelationClusteringFeasible i)
  | none => false

/-- **CORRELATION CLUSTERING is NP-complete.** Source: Bansal, Blum and Chawla (2004),
Section 3. -/
public theorem_wanted correlationClustering_npComplete :
    correlationClusteringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L correlationClusteringDec

end MetaMathlibExt.Complexity.NPComplete.CorrelationClustering
