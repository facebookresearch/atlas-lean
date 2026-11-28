/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOOK THICKNESS AT MOST 2: definitions

Source:
F. R. K. Chung, F. T. Leighton and A. L. Rosenberg, "Embedding graphs in books: a layout
problem with applications to VLSI design", SIAM Journal on Algebraic and Discrete Methods 8
(1987), 33-58, doi:10.1137/0608002 (Corollary 4.4: "The problem of deciding 2-page
embeddability is NP-complete", from A. Wigderson, "The complexity of the Hamiltonian circuit
problem for maximal planar graphs", Technical Report 298, EECS Department, Princeton University,
1982).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.GraphTheory.BookThicknessOfSubdivisionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BookThicknessTwo

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev BookThicknessTwoInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BookThicknessTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BookThicknessTwoInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph has a 2-page book embedding (`HasBookEmbedding` with `k = 2`). -/
def BookThicknessTwoFeasible (i : BookThicknessTwoInstance) : Prop :=
  MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted.HasBookEmbedding (Graph i) 2

open Classical in
/-- BOOK THICKNESS AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def bookThicknessTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BookThicknessTwoInstance) x with
  | some i => decide (WellFormed i ∧ BookThicknessTwoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BookThicknessTwo
