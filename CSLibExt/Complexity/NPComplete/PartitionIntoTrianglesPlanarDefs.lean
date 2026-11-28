/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO TRIANGLES for planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT11] PARTITION INTO TRIANGLES;
D. S. Johnson, "The NP-completeness column: an ongoing guide" (tenth edition), Journal of
Algorithms 5 (1984), 147-160, doi:10.1016/0196-6774(84)90045-2 (update to [GT11]:
"NP-complete for planar graphs [4,22]");
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U;
M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7 (1986),
174-184, doi:10.1016/0196-6774(86)90002-7.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.PartitionIntoTrianglesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoTrianglesPlanar

/-- Well-formedness of an instance: the parent's simple edge list on vertices below `n`, the
graph is planar, and the vertex count is a multiple of 3. -/
def WellFormed (i : PartitionIntoTriangles.PartitionIntoTrianglesInstance) : Prop :=
  PartitionIntoTriangles.WellFormed i ∧ (PartitionIntoTriangles.Graph i).IsPlanar ∧ 3 ∣ i.1

open Classical in
/-- PARTITION INTO TRIANGLES for planar graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoTrianglesPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoTriangles.PartitionIntoTrianglesInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoTriangles.PartitionIntoTrianglesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoTrianglesPlanar
