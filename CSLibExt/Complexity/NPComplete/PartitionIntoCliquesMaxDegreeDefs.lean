/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on graphs of maximum degree at most k (fixed k ≥ 3): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES, the
problem restricted here;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (degree-k graphs, PARTITION INTO
CLIQUES: NP-complete);
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed,
"Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete
Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMaxDegree

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

open Classical in
/-- Well-formedness of an instance for the fixed degree bound `k`: well formed for PARTITION
INTO CLIQUES (a simple graph on `Fin n` and `0 < K ≤ n`), and no vertex has degree exceeding
`k`. -/
def WellFormed (k : ℕ) (i : PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ ∀ v, (Graph i).degree v ≤ k

open Classical in
/-- PARTITION INTO CLIQUES on graphs of maximum degree at most `k`, for the fixed `k`, as a
decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesMaxDegreeDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed k i ∧ PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesMaxDegree
