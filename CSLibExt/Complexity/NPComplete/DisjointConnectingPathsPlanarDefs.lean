/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISJOINT CONNECTING PATHS for planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS,
p. 217, comment ("Remains NP-complete for planar graphs [Lynch, 1974], [Lynch, 1975]");
J. F. Lynch, "The equivalence of theorem proving and the interconnection problem", ACM SIGDA
Newsletter 5(3) (1975), 31-36, doi:10.1145/1061425.1061430.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPathsPlanar

open DisjointConnectingPaths
  (DisjointConnectingPathsInstance Graph DisjointConnectingPathsFeasible)

/-- Well-formedness of an instance: a well-formed DISJOINT CONNECTING PATHS instance (a simple
edge list on `Fin n`, pairs of vertices, the `2k` paired vertices pairwise distinct) whose graph
is planar (`SimpleGraph.IsPlanar`). -/
def WellFormed (i : DisjointConnectingPathsInstance) : Prop :=
  DisjointConnectingPaths.WellFormed i ∧ (Graph i).IsPlanar

open Classical in
/-- DISJOINT CONNECTING PATHS for planar graphs as a decision problem over bitstrings. -/
noncomputable def disjointConnectingPathsPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DisjointConnectingPathsInstance) x with
  | some i => decide (WellFormed i ∧ DisjointConnectingPathsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPathsPlanar
