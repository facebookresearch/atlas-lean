/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE PARTITION INTO TRIANGLES for K₄-free graphs: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9 (problem [1] EDGE-PARTITION INTO TRIANGLES and its
comment);
I. Holyer, "The NP-completeness of some edge-partition problems", SIAM Journal on Computing 10
(1981), 713-717, doi:10.1137/0210054;
C. J. Colbourn, "The complexity of completing partial Latin squares", Discrete Applied
Mathematics 8 (1984), 25-30, doi:10.1016/0166-218X(84)90075-1.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgePartitionIntoTrianglesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTrianglesK4Free

open EdgePartitionIntoTriangles (EdgePartitionIntoTrianglesInstance Graph
  EdgePartitionIntoTrianglesFeasible)

/-- Well-formedness of an instance: a well-formed EDGE PARTITION INTO TRIANGLES instance (a
simple edge list on `Fin n`) whose graph has no 4-clique. -/
def WellFormed (i : EdgePartitionIntoTrianglesInstance) : Prop :=
  EdgePartitionIntoTriangles.WellFormed i ∧ (Graph i).CliqueFree 4

open Classical in
/-- EDGE PARTITION INTO TRIANGLES for `K₄`-free graphs as a decision problem over bitstrings. -/
noncomputable def edgePartitionIntoTrianglesK4FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgePartitionIntoTrianglesInstance) x with
  | some i => decide (WellFormed i ∧ EdgePartitionIntoTrianglesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTrianglesK4Free
