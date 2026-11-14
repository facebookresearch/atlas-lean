/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOOK THICKNESS AT MOST 2 is NP-complete

Source:
F. R. K. Chung, F. T. Leighton and A. L. Rosenberg, "Embedding graphs in books: a layout
problem with applications to VLSI design", SIAM Journal on Algebraic and Discrete Methods 8
(1987), 33-58, doi:10.1137/0608002 (Corollary 4.4: "The problem of deciding 2-page
embeddability is NP-complete", from A. Wigderson, "The complexity of the Hamiltonian circuit
problem for maximal planar graphs", Technical Report 298, EECS Department, Princeton University,
1982).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import WantedExt.GraphTheory.BookThicknessOfSubdivisionsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BookThicknessTwo

/-!
# BOOK THICKNESS AT MOST 2 is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: can `G` be embedded in a book with two pages, i.e.,
can the vertices be placed in a line (the spine) and each edge be assigned to one of two pages
so that no two edges on the same page cross?

This is Chung, Leighton and Rosenberg's 2-page embeddability, in their Formulation 3 (vertices
in order on a line or circle, edges as chords assigned to pages, chords on one page must not
cross). It reuses `HasBookEmbedding G 2` from
`WantedExt/GraphTheory/BookThicknessOfSubdivisionsWanted`: an injective spine position
`pos : V → ℕ` and a colouring of the edge set with `Fin 2` (the pages) such that crossing edges
get different pages, where two edges cross (`IsCrossing`) when their endpoints interleave along
the spine, `v ≺ x ≺ w ≺ y` for `e₁ = {v, w}` and
`e₂ = {x, y}` (or with the edges exchanged). Edges with a common end never cross, and using
fewer than two pages is allowed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **BOOK THICKNESS AT MOST 2 is NP-complete.** Source: Chung, Leighton and Rosenberg (1987),
Corollary 4.4 (from Wigderson (1982)). -/
public theorem_wanted bookThicknessTwo_npComplete :
    bookThicknessTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bookThicknessTwoDec

end MetaMathlibExt.Complexity.NPComplete.BookThicknessTwo
