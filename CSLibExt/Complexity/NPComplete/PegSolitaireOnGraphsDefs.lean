/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SOLVABILITY OF PEG SOLITAIRE ON GRAPHS: definitions

Source:
K. Ito and Y. Takenaga, "Solvability of peg solitaire on graphs is NP-complete", IEICE
Transactions on Information and Systems E106-D (2023), 1111-1116,
doi:10.1587/transinf.2022EDP7092.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PegSolitaireOnGraphs

/-- An instance: vertex count `n` (vertices `Fin n`) and the edge list. -/
abbrev PegSolitaireOnGraphsInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PegSolitaireOnGraphsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: a simple edge list on the vertices `Fin n` (no repeated
edges, in either orientation, and no loops). -/
def WellFormed (i : PegSolitaireOnGraphsInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- One jump `x → y → z` from the position `P` (the vertices with a peg) to the position `Q`:
`xy` and `yz` are edges, `x` and `y` carry pegs, `z` is a hole, and afterwards `x` and `y` are
holes and `z` carries a peg. -/
def Jump {V : Type*} [DecidableEq V] (G : SimpleGraph V) (P Q : Finset V) : Prop :=
  ∃ x y z, G.Adj x y ∧ G.Adj y z ∧ x ∈ P ∧ y ∈ P ∧ z ∉ P ∧ Q = insert z ((P.erase x).erase y)

/-- `G` is solvable with respect to the initial hole `s`: starting with a peg on every vertex
but `s`, a sequence of jumps leaves exactly one peg. -/
def SolvableFrom {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : V) : Prop :=
  ∃ Q, Relation.ReflTransGen (Jump G) (Finset.univ.erase s) Q ∧ Q.card = 1

/-- The graph of the instance is solvable: it is solvable with respect to some initial hole. -/
def PegSolitaireOnGraphsFeasible (i : PegSolitaireOnGraphsInstance) : Prop :=
  ∃ s, SolvableFrom (Graph i) s

open Classical in
/-- SOLVABILITY OF PEG SOLITAIRE ON GRAPHS as a decision problem over bitstrings. -/
noncomputable def pegSolitaireOnGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PegSolitaireOnGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PegSolitaireOnGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PegSolitaireOnGraphs
