/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH SQUARE ROOT: definitions

Source:
R. Motwani and M. Sudan, "Computing roots of graphs is hard", Discrete Applied Mathematics 54
(1994), 81-88, doi:10.1016/0166-218X(94)00023-9;
recorded in B. Farzad and M. Karimi, "Square-root finding problem in graphs, a complete dichotomy
theorem", arXiv:1210.7684 (2012), Section 1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Square

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphSquareRoot

/-- An instance: vertex count `n` and edge list. -/
abbrev GraphSquareRootInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GraphSquareRootInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : GraphSquareRootInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- Some graph `H` on the same vertices has square `G`. -/
def GraphSquareRootFeasible (i : GraphSquareRootInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H.square = Graph i

open Classical in
/-- GRAPH SQUARE ROOT as a decision problem over bitstrings. -/
noncomputable def graphSquareRootDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphSquareRootInstance) x with
  | some i => decide (WellFormed i ∧ GraphSquareRootFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphSquareRoot
