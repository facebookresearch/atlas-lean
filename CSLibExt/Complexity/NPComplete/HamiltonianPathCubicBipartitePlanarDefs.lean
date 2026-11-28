/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on cubic bipartite planar graphs: definitions

Source:
A. Munaro, "On line graphs of subcubic triangle-free graphs", Discrete Mathematics 340 (2017),
1210-1226, doi:10.1016/j.disc.2017.01.006, Theorem 23 ("Hamiltonian Path is NP-complete even for
planar cubic bipartite graphs");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicBipartitePlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph)

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance (`0 < n`, a simple
graph given by an edge list) that is bipartite, cubic and planar. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsBipartite ∧ (Graph i).IsRegularOfDegree 3 ∧
    (Graph i).IsPlanar

open Classical in
/-- HAMILTONIAN PATH on cubic bipartite planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathCubicBipartitePlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧
      HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicBipartitePlanar
