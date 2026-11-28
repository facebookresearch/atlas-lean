/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES for graphs of thickness at most k: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES;
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed,
"Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete
Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015 (NP-complete for
planar cubic graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (PARTITION INTO CLIQUES on planar and on thickness-`k`
graphs: NP-complete, citing F. Berman, D. S. Johnson, F. T. Leighton, P. W. Shor and L. Snyder,
"Generalized planar matching", manuscript, 1985).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThicknessPartitionIntoCliques

/-- Well-formedness of an instance for the thickness bound `k`: a well-formed PARTITION INTO CLIQUES
instance (a simple edge list on `0, ..., n - 1` and `0 < K ≤ n`) whose graph has thickness at most
`k`. -/
def WellFormed (k : ℕ) (i : PartitionIntoCliques.PartitionIntoCliquesInstance) : Prop :=
  PartitionIntoCliques.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (i.1, i.2.1, k)

open Classical in
/-- PARTITION INTO CLIQUES for graphs of thickness at most `k`, as a decision problem over
bitstrings. -/
noncomputable def thicknessPartitionIntoCliquesDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliques.PartitionIntoCliquesInstance) x with
  | some i => decide (WellFormed k i ∧ PartitionIntoCliques.PartitionIntoCliquesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThicknessPartitionIntoCliques
