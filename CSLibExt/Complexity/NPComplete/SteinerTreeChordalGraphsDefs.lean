/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights on chordal graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS;
K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly chordal
graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, its graph is chordal (no induced cycle of length at least `4`), it has at
least one vertex, and `K` is positive. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (SteinerTree.Graph i i.2.1)) ∧
      0 < i.1 ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights on chordal graphs as a decision problem over
bitstrings. -/
noncomputable def steinerTreeChordalGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalGraphs
