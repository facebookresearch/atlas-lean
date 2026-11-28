/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on cubic Hamiltonian planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
H. Fleischner, G. Sabidussi and V. I. Sarvanov, "Maximum independent sets in 3- and 4-regular
Hamiltonian graphs", Discrete Mathematics 310(20) (2010), 2742-2749,
doi:10.1016/j.disc.2010.05.028.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetCubicHamiltonianPlanar

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSetCubicHamiltonianPlanarInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSetCubicHamiltonianPlanarInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is cubic, Hamiltonian and planar, and `0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSetCubicHamiltonianPlanarInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsHamiltonian ∧ (Graph i).IsPlanar ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def IndependentSetCubicHamiltonianPlanarFeasible
    (i : IndependentSetCubicHamiltonianPlanarInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on cubic Hamiltonian planar graphs as a decision problem over bitstrings. -/
noncomputable def independentSetCubicHamiltonianPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSetCubicHamiltonianPlanarInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSetCubicHamiltonianPlanarFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetCubicHamiltonianPlanar
