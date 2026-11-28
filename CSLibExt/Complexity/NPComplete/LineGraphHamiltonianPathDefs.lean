/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN LINE GRAPHS: definitions

Source:
A. A. Bertossi, "The edge Hamiltonian path problem is NP-complete", Information Processing
Letters 13 (1981), 157-159, doi:10.1016/0020-0190(81)90048-X;
recorded in M. Lampis, K. Makino, V. Mitsou and Y. Uno, "Parameterized edge Hamiltonicity",
Discrete Applied Mathematics 248 (2018), 68-78, doi:10.1016/j.dam.2017.04.045, Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance WellFormed HamiltonianPathUndirectedFeasible)

/-- Two edges, given as vertex pairs, share an endpoint. -/
abbrev ShareEndpoint (e f : ℕ × ℕ) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

/-- The edges of the line graph: the pairs `(a, b)` of edge positions with `a < b < |E|` whose
edges share an endpoint. -/
def lineEdges (i : HamiltonianPathUndirectedInstance) : List (ℕ × ℕ) :=
  (List.range i.2.length).flatMap fun a =>
    ((List.range i.2.length).filter fun b =>
      decide (a < b ∧ ShareEndpoint (i.2.getD a (0, 0)) (i.2.getD b (0, 0)))).map fun b => (a, b)

/-- The line graph of `G` as a HAMILTONIAN PATH (UNDIRECTED) instance: `|E|` vertices and the
line-graph edges. -/
def toLineGraphInstance (i : HamiltonianPathUndirectedInstance) :
    HamiltonianPathUndirectedInstance :=
  (i.2.length, lineEdges i)

open Classical in
/-- HAMILTONIAN PATH IN LINE GRAPHS as a decision problem over bitstrings. -/
noncomputable def lineGraphHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible (toLineGraphInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianPath
