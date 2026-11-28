/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for claw-free graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN5] CHROMATIC INDEX;
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30 (1991), 15-27, doi:10.1016/0166-218X(91)90010-T;
E. Galby, P. T. Lima, D. Paulusma and B. Ries, "Classifying k-edge colouring for H-free
graphs", Information Processing Letters 146 (2019), 39-43, doi:10.1016/j.ipl.2019.02.006;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexClawFree

open EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

/-- Well-formedness of an instance: a well-formed EDGE COLORING instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is claw-free, and `0 < K`. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsClawFree ∧ 0 < i.2.2

open Classical in
/-- CHROMATIC INDEX for claw-free graphs as a decision problem over bitstrings. -/
noncomputable def chromaticIndexClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexClawFree
