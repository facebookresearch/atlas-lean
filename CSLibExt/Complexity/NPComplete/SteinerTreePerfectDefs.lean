/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for perfect graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS;
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreePerfect

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted (IsPerfect)

/-- Well-formedness of an instance: a well-formed STEINER TREE IN GRAPHS instance in which every
edge has weight `1`, whose graph is perfect, and `0 < K`. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    IsPerfect (SteinerTree.Graph i i.2.1) ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) for perfect graphs as a decision problem over bitstrings.
-/
noncomputable def steinerTreePerfectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreePerfect
