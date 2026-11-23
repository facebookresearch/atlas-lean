/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for K₃,₃-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment:
remains NP-complete if all edge weights are equal, even if ... `G` is planar;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-free", column STEINER TREE);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row K3,3-FREE*, column ST TREE: "N [GJ]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted
public import WantedExt.Complexity.NPComplete.DominatingSetK33FreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeK33Free

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free (HasK33Subdivision)

/-!
# STEINER TREE IN GRAPHS (unit weights) for K₃,₃-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no subgraph homeomorphic to `K₃,₃`, a subset `R ⊆ V`, and a
positive integer `K`. QUESTION: is there a subtree of `G` that includes all the vertices of `R`
and has at most `K` edges?

This is STEINER TREE IN GRAPHS (`WantedExt.Complexity.NPComplete.SteinerTreeWanted`, [ND12]) with
unit edge weights, restricted to the class that Johnson's 1985 table calls "K3,3-free" and de
Figueiredo et al. call K3,3-FREE*: "the class of graphs that contain no subgraphs homeomorphic to
K3,3; in other words, the class of graphs that do not contain K3,3 as a topological minor". The
predicate is `DominatingSetK33Free.HasK33Subdivision` (a subgraph homeomorphic to `K₃,₃`, i.e. a
subdivision of `K₃,₃`: six distinct branch vertices joined by nine paths that meet only at common
endpoints). The instance, the parent well-formedness condition (simple weighted edge list, positive
weights, distinct terminals in range) and the question (a sublist of edges of total weight at most
`K` connecting all terminals, which with unit weights is a subtree with at most `K` edges) are that
module's; unit weights, at least one vertex (a tree is nonempty, so the empty graph has no subtree),
`K > 0` and the restriction are added to `WellFormed`, as in `SteinerTreeBipartiteWanted`. Every
planar graph is K3,3-free (Kuratowski), so the class contains the planar graphs on which [ND12]
records the unit-weight problem NP-complete; de Figueiredo et al. derive the K3,3-free entries from
the planar ones in this way.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed STEINER TREE IN GRAPHS instance in which every
edge has weight `1`, with at least one vertex and `K > 0`, whose graph has no subgraph homeomorphic
to `K₃,₃`. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧ 0 < i.1 ∧ 0 < i.2.2.2 ∧
    ¬ HasK33Subdivision (SteinerTree.Graph i i.2.1)

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) for K₃,₃-free graphs as a decision problem over
bitstrings. -/
noncomputable def steinerTreeK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS (unit weights) for K₃,₃-free graphs is NP-complete.** Source: Garey and
Johnson (1979), [ND12], comment; Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva
(2022), Table 1. -/
public theorem_wanted steinerTreeK33Free_npComplete :
    steinerTreeK33FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeK33FreeDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeK33Free
