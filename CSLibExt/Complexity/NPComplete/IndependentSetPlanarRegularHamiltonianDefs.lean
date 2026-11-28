/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on planar k-regular Hamiltonian graphs (k = 4, 5): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (the parent
problem);
H. Fleischner, G. Sabidussi and V. I. Sarvanov, "Maximum independent sets in 3- and 4-regular
Hamiltonian graphs", Discrete Mathematics 310(20) (2010), 2742-2749,
doi:10.1016/j.disc.2010.05.028 (`k = 4`; Proposition 4.3 as cited by Cavallaro);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 5.7 (`k = 4`,
attributed to Fleischner, Sabidussi and Sarvanov) and Theorem 5.8 (`k = 5`);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes
"4-regular ∩ hamiltonian ∩ planar" (gc_1315) and "5-regular ∩ hamiltonian ∩ planar" (gc_1320),
problem Independent set: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetPlanarRegularHamiltonian

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

open Classical in
/-- Well-formedness of an instance for a fixed `k`: the edge list describes a simple graph on
`Fin n` (no duplicate edges in either orientation, no self-loops, endpoints in range),
`0 < K ≤ |V|`, and the graph is planar, `k`-regular and Hamiltonian. -/
def WellFormed (k : ℕ) (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsPlanar ∧ (Graph i).IsRegularOfDegree k ∧
      (Graph i).IsHamiltonian

open Classical in
/-- INDEPENDENT SET on planar `k`-regular Hamiltonian graphs as a decision problem over
bitstrings. -/
noncomputable def independentSetPlanarRegularHamiltonianDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed k i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetPlanarRegularHamiltonian
