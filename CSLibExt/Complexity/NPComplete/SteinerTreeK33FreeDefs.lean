/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for K₃,₃-free graphs: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs
public import CSLibExt.Complexity.NPComplete.DominatingSetK33FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeK33Free

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free (HasK33Subdivision)

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

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeK33Free
