/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3-DIMENSIONAL MATCHING: definitions

Source:
M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7(2) (1986),
174-184, doi:10.1016/0196-6774(86)90002-7;
S. Borgwardt and S. Patterson, "On the computational complexity of finding a sparse Wasserstein
barycenter", Journal of Combinatorial Optimization 41(3) (2021), arXiv:1910.07568, Section 2.2
(definition of planar 3-dimensional matching; "P3DM itself is NP-hard", credited to Dyer and
Frieze);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeDimensionalMatching

open MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching

/-- The element-triple incidence graph: vertex `3q + j` (the `j`-th triple `(w, x, y)`) is
adjacent to the element vertices `w`, `q + x` and `2q + y`. -/
def incidenceGraph (i : ThreeDimensionalMatchingInstance) :
    SimpleGraph (Fin (3 * i.1 + i.2.length)) :=
  SimpleGraph.fromRel fun u v => ∃ j < i.2.length, u.val = 3 * i.1 + j ∧
    (v.val = (i.2.getD j (0, 0, 0)).1 ∨ v.val = i.1 + (i.2.getD j (0, 0, 0)).2.1 ∨
      v.val = 2 * i.1 + (i.2.getD j (0, 0, 0)).2.2)

/-- Well-formedness of an instance: a well-formed 3DM instance with distinct triples whose
incidence graph is planar. -/
def WellFormed (i : ThreeDimensionalMatchingInstance) : Prop :=
  ThreeDimensionalMatching.WellFormed i ∧ i.2.Nodup ∧ (incidenceGraph i).IsPlanar

/-- `M` contains a matching of size `q` (the 3DM question). -/
def PlanarThreeDimensionalMatchingFeasible (i : ThreeDimensionalMatchingInstance) : Prop :=
  ThreeDimensionalMatchingFeasible i

open Classical in
/-- PLANAR 3-DIMENSIONAL MATCHING as a decision problem over bitstrings. -/
noncomputable def planarThreeDimensionalMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ PlanarThreeDimensionalMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeDimensionalMatching
