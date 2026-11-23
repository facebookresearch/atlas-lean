/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [6] CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE
(reference: A. M. Frieze, "On equitably partitioning a connected graph into connected
subgraphs", technical report; transformation from 3DM);
M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected
subgraphs", Discrete Applied Mathematics 10 (1985), 139-153,
doi:10.1016/0166-218X(85)90008-3, Theorem 2.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CutIntoConnectedComponentsBoundedSize

/-!
# CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer bound `K ≥ |V| / 2`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that
`max(|V₁|, |V₂|) ≤ K`, and both `V₁` and `V₂` induce connected subgraphs of `G`?

Johnson's column, problem [6], credits the result to a technical report of Frieze (not
available), by a transformation from 3DM. Dyer and Frieze (1985), Theorem 2.2 with `k = 2`,
prove that deciding whether a bipartite graph on `n` vertices can be partitioned into two
connected induced subgraphs with `n / 2` vertices each is NP-complete; this is the case
`K = |V| / 2` of the question above. Membership in NP: `V₁` is a certificate. A yes-instance
has two connected parts, so at least `n - 2` edges, and the certificate is polynomial in the
input size even though `n` is written in binary.

The column's instance is an arbitrary graph `G = (V, E)`, not required to be connected (only the
title of Frieze's report speaks of a connected graph), and the statement follows the column. A
disconnected graph is a yes-instance exactly when it has two connected components, each with at
most `K` vertices; this is checked in polynomial time, so adding a connectivity requirement would
not change the complexity of the problem.

The graph is given by its vertex count `n` and a simple edge list, as the `SimpleGraph (Fin n)`
of `GraphColoring.Graph` (the instance shape of GRAPH COLORING, with `K` read as the size
bound). The bound `K ≥ |V| / 2` is `|V| ≤ 2 K`. `V₂` is the complement of `V₁`; "connected" is
Mathlib's `SimpleGraph.Connected` of the induced subgraph, which includes being nonempty, as in
`IntegrityPreservingCutWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance `(n, E, K)`: a simple edge list on the vertices
`0, …, n - 1` (`GraphColoring.WellFormed`), and the bound `K ≥ |V| / 2`, that is
`n ≤ 2 K`. -/
def WellFormed (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.1 ≤ 2 * i.2.2

/-- Some set `V₁` with complement `V₂` has `|V₁| ≤ K`, `|V₂| ≤ K`, and both induced subgraphs
connected. -/
def CutIntoConnectedComponentsBoundedSizeFeasible (i : GraphColoring.GraphColoringInstance) :
    Prop :=
  ∃ V₁ : Finset (Fin i.1), V₁.card ≤ i.2.2 ∧ V₁ᶜ.card ≤ i.2.2 ∧
    ((GraphColoring.Graph i).induce (V₁ : Set (Fin i.1))).Connected ∧
    ((GraphColoring.Graph i).induce ((V₁ᶜ : Finset (Fin i.1)) : Set (Fin i.1))).Connected

open Classical in
/-- CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE as a decision problem over bitstrings. -/
noncomputable def cutIntoConnectedComponentsBoundedSizeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ CutIntoConnectedComponentsBoundedSizeFeasible i)
  | none => false

/-- **CUT INTO CONNECTED COMPONENTS OF BOUNDED SIZE is NP-complete.** Source: Johnson (1982),
problem [6] (Frieze); Dyer and Frieze (1985), Theorem 2.2. -/
public theorem_wanted cutIntoConnectedComponentsBoundedSize_npComplete :
    cutIntoConnectedComponentsBoundedSizeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cutIntoConnectedComponentsBoundedSizeDec

end MetaMathlibExt.Complexity.NPComplete.CutIntoConnectedComponentsBoundedSize
