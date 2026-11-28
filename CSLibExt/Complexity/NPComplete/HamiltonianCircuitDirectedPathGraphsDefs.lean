/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT ON DIRECTED PATH GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, the problem
restricted here;
G. Narasimhan, "A note on the Hamiltonian circuit problem on directed path graphs", Information
Processing Letters 32 (1989), 167-170, doi:10.1016/0020-0190(89)90038-0;
C. L. Monma and V. K. Wei, "Intersection graphs of paths in a tree", Journal of Combinatorial
Theory, Series B 41 (1986), 141-181, doi:10.1016/0095-8956(86)90042-1 (the class).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Combinatorics.SimpleGraph.Dichromatic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitDirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-- `G` is a directed path graph: for some tree `T` on `Fin m` and some orientation `D` of its
edges (MathlibExt's `SimpleGraph.IsOrientation`), each vertex `v` of `G` has the vertex set `P v`
of a path of `T` whose edges all follow `D`, and distinct vertices are adjacent in `G` exactly when
their paths share a vertex. -/
def IsDirectedPathGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (D : Fin m → Fin m → Prop), T.IsTree ∧
    T.IsOrientation D ∧
    ∃ P : Fin n → Finset (Fin m),
      (∀ v, ∃ (a b : Fin m) (p : T.Walk a b), p.IsPath ∧ (∀ d ∈ p.darts, D d.fst d.snd) ∧
        p.support.toFinset = P v) ∧
      ∀ u v, u ≠ v → (G.Adj u v ↔ (P u ∩ P v).Nonempty)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (`0 < n`, simple
edge list) whose graph is a directed path graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ IsDirectedPathGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT ON DIRECTED PATH GRAPHS as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitDirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitDirectedPathGraphs
