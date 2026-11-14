/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SOLVABILITY OF PEG SOLITAIRE ON GRAPHS is NP-complete

Source:
K. Ito and Y. Takenaga, "Solvability of peg solitaire on graphs is NP-complete", IEICE
Transactions on Information and Systems E106-D (2023), 1111-1116,
doi:10.1587/transinf.2022EDP7092.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PegSolitaireOnGraphs

/-!
# SOLVABILITY OF PEG SOLITAIRE ON GRAPHS is NP-complete

Peg solitaire on graphs (Beeler and Hoilman) as stated by Ito and Takenaga (2023): "if
`xy, yz ∈ E`, pegs are placed on `x` and `y` and `z` is a hole, the peg on `x` can jump over the
peg on `y` and be placed on `z`, and the peg on `y` is removed." "A graph is called solvable
with respect to initial hole `s`, if it is possible to remove all but one peg starting with `s`
as the initial hole", and "a graph [is] solvable if there exists a vertex `s` such that the
graph is solvable with respect to `s`." Theorem 8: "Given a graph `G`, it is NP-complete to
decide if `G` is solvable."

The graph is a finite simple graph on `Fin n` given by its edge list. A position is the finset
of vertices that carry a peg; the initial position for hole `s` has a peg on every vertex but
`s`. A jump `x → y → z` turns the pegs on `x` and `y` into holes and puts a peg on `z`.

Vertices are given by their number `n`. Every vertex that lies on no edge keeps its initial
contents forever, so in a solvable graph such a vertex is the initial hole or carries the final
peg; there are at most two of them and `n ≤ 2|E| + 2`. The certificate (the initial hole and a
sequence of fewer than `n` jumps) is therefore polynomial in the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SOLVABILITY OF PEG SOLITAIRE ON GRAPHS is NP-complete.** Source: Ito and Takenaga (2023),
Theorem 8. -/
public theorem_wanted pegSolitaireOnGraphs_npComplete :
    pegSolitaireOnGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pegSolitaireOnGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PegSolitaireOnGraphs
