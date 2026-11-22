/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
145-159, doi:10.1016/0196-6774(85)90025-2, comment on entry [4] DEGREE CONSTRAINED SUBGRAPH:
"If, however, we are given just the desired degrees, and are not constrained as to which
vertices get which degrees, the problem once more becomes NP-complete", attributed to Camerini
and Maffioli;
P. M. Camerini and F. Maffioli, "Unlabelled partition systems: optimization and complexity",
SIAM Journal on Algebraic and Discrete Methods 5 (1984), 426-441, doi:10.1137/0605041 (cited by
Johnson as Report LCE83-1, Politecnico di Milano, 1983; full text not available here).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphUnlabelledDegreeSequence

/-!
# SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE is NP-complete

INSTANCE: a graph `G = (V, E)` and a multiset `{d₁, …, dₙ}` of desired degrees, `n = |V|`.
QUESTION: does `G` contain a spanning subgraph `G' = (V, E')`, `E' ⊆ E`, whose multiset of
vertex degrees is `{d₁, …, dₙ}`, with no constraint on which vertex gets which degree?

Johnson's column states DEGREE CONSTRAINED SUBGRAPH (each vertex `v` has its own set `D_v` of
allowable degrees, NP-complete by a reduction of Plesník and Wawruch) and records in its comment
that the variant in which only the desired degrees are given, without prescribing which vertices
get which degrees, is NP-complete as well, citing Camerini and Maffioli. Their abstract
introduces unlabelled partition systems, which arise in degree-constrained subgraph problems
when only the number of vertices with each prescribed degree is assigned, disregarding the
identities of the vertices.

The vertices are `0, …, n - 1`, and the graph is given by a simple edge list (no loops, no
repeated edge in either orientation, endpoints below `n`); the desired degrees are a list of
`n` natural numbers, read as a multiset. `E'` is a sublist of the edge list, `G'` is the
spanning subgraph `edgeGraph n E'` on all `n` vertices, and degrees are Mathlib's
`SimpleGraph.degree`, as in `DegreeBoundedConnectedSubgraphWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the list of desired
degrees. -/
abbrev SubgraphUnlabelledDegreeSequenceInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and there are `n`
desired degrees. -/
def WellFormed (i : SubgraphUnlabelledDegreeSequenceInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1

open Classical in
/-- Some sublist `E'` of the edge list spans a subgraph `(V, E')` whose multiset of vertex
degrees equals the multiset of desired degrees. -/
def SubgraphUnlabelledDegreeSequenceFeasible (i : SubgraphUnlabelledDegreeSequenceInstance) :
    Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧
    (Finset.univ : Finset (Fin i.1)).val.map
        (fun v => (Cslib.Complexity.Karp.edgeGraph i.1 es).degree v) = (i.2.2 : Multiset ℕ)

open Classical in
/-- SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE as a decision problem over bitstrings. -/
noncomputable def subgraphUnlabelledDegreeSequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphUnlabelledDegreeSequenceInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphUnlabelledDegreeSequenceFeasible i)
  | none => false

/-- **SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE is NP-complete.** Source: Johnson (1985),
NP-completeness column, DEGREE CONSTRAINED SUBGRAPH; Camerini and Maffioli (1984). -/
public theorem_wanted subgraphUnlabelledDegreeSequence_npComplete :
    subgraphUnlabelledDegreeSequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subgraphUnlabelledDegreeSequenceDec

end MetaMathlibExt.Complexity.NPComplete.SubgraphUnlabelledDegreeSequence
