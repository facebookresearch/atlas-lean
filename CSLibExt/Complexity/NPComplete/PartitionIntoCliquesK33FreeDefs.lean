/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for K₃,₃-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES (the
unrestricted problem);
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed, "Partition
into cliques for cubic graphs: Planar case, complexity and approximation", Discrete Applied
Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015 (NP-complete for planar
cubic graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-free", column PARTITION INTO CLIQUES);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row K3,3-FREE*, column CLI PAR: "N [77]").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs
public import CSLibExt.Complexity.NPComplete.DominatingSetK33FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK33Free

open MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliques
  (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)
open MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free (HasK33Subdivision)

/-- Well-formedness of an instance: a well-formed PARTITION INTO CLIQUES instance (simple edge list,
`0 < K ≤ |V|`) whose graph has no subgraph homeomorphic to `K₃,₃`. -/
def WellFormed (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ ¬ HasK33Subdivision (Graph i)

open Classical in
/-- PARTITION INTO CLIQUES for K₃,₃-free graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesK33Free
