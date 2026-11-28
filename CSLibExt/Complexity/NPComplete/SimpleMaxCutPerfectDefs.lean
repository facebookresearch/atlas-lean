/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for perfect graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT (comment: SIMPLE MAX
CUT, all weights 1);
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal of
Computing 7(1) (2000), 14-31 (conference version: STACS 94, Lecture Notes in Computer Science 775
(1994), 769-780, doi:10.1007/3-540-57785-8_189);
L. Lovász, "Normal hypergraphs and the perfect graph conjecture", Discrete Mathematics 2 (1972),
253-267, doi:10.1016/0012-365X(72)90006-4;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutPerfect

open MaxCut (MaxCutInstance MaxCutFeasible)
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted (IsPerfect)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is perfect, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ IsPerfect (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for perfect graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutPerfectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutPerfect
