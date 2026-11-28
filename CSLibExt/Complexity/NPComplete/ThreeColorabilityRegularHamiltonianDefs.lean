/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY on k-regular Hamiltonian graphs (k ≥ 4): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
H. Fleischner and G. Sabidussi, "3-colorability of 4-regular Hamiltonian graphs", Journal of
Graph Theory 42(2) (2003), 125-140, doi:10.1002/jgt.10079 (`k = 4`);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 4.9 (`k = 4`,
attributed to Fleischner and Sabidussi) and Theorem 4.10 (every fixed `k ≥ 4`);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes
"4-regular ∩ hamiltonian" (gc_1318) and "5-regular ∩ hamiltonian" (gc_1317), problem
3-Colourability: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityRegularHamiltonian

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

open Classical in
/-- Well-formedness of an instance for a fixed `k`: a well-formed GRAPH K-COLORABILITY instance
(a simple edge list on `Fin n`) with `K = 3` whose graph is `k`-regular and Hamiltonian. -/
def WellFormed (k : ℕ) (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).IsRegularOfDegree k ∧
    (Graph i).IsHamiltonian

open Classical in
/-- 3-COLORABILITY on `k`-regular Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def threeColorabilityRegularHamiltonianDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed k i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityRegularHamiltonian
