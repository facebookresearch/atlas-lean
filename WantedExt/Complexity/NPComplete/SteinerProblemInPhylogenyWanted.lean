/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER PROBLEM IN PHYLOGENY (maximum parsimony for binary sequences) is NP-complete

Source:
L. R. Foulds and R. L. Graham, "The Steiner problem in phylogeny is NP-complete", Advances in
Applied Mathematics 3(1) (1982), 43-49, doi:10.1016/S0196-8858(82)80004-3;
N. Misra, G. Blelloch, R. Ravi, and R. Schwartz, "Generalized Buneman pruning for inferring the
most parsimonious multi-state phylogeny", arXiv:0910.1830 (maximum parsimony is NP-hard
[Foulds and Graham] and, for discrete characters, equivalent to finding a minimum Steiner tree
displaying the input taxa).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerProblemInPhylogeny

/-!
# STEINER PROBLEM IN PHYLOGENY (maximum parsimony for binary sequences) is NP-complete

INSTANCE: a set of species, each given by a binary sequence of length `m`, and an integer `K`.
QUESTION: is there a phylogenetic tree whose vertices are labeled by binary sequences of length
`m`, containing every species, whose total length (the sum over its edges of the Hamming
distance between the endpoint labels) is at most `K`?

This is the Steiner tree problem in the hypercube `Q_m` (`SimpleGraph.hypercubeGraph m`,
vertices `Fin m → Bool`, edges between sequences at Hamming distance `1`): a tree of total
Hamming length `L` becomes a subtree of `Q_m` with at most `L` edges by subdividing each edge
along a shortest path, and a subtree of `Q_m` is such a tree of total length its edge count. The
question is stated in that form: some subgraph of `Q_m` that is a tree contains every species
and has at most `K` edges. The species are listed explicitly, at least one of them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sequence length `m`, the species' sequences, and the bound `K`. -/
abbrev SteinerProblemInPhylogenyInstance := ℕ × List (List Bool) × ℕ

/-- A listed sequence as a vertex `Fin m → Bool` of the hypercube `Q_m`. -/
def toVertex (m : ℕ) (s : List Bool) : Fin m → Bool :=
  fun k => s.getD k false

/-- Well-formedness of an instance: there is at least one species, and every species is a
sequence of length `m`. -/
def WellFormed (i : SteinerProblemInPhylogenyInstance) : Prop :=
  i.2.1 ≠ [] ∧ ∀ s ∈ i.2.1, s.length = i.1

/-- Some subtree of the hypercube `Q_m` contains every species and has at most `K` edges. -/
def SteinerProblemInPhylogenyFeasible (i : SteinerProblemInPhylogenyInstance) : Prop :=
  ∃ T : (SimpleGraph.hypercubeGraph i.1).Subgraph, T.coe.IsTree ∧
    (∀ s ∈ i.2.1, toVertex i.1 s ∈ T.verts) ∧ T.edgeSet.ncard ≤ i.2.2

open Classical in
/-- STEINER PROBLEM IN PHYLOGENY as a decision problem over bitstrings. -/
noncomputable def steinerProblemInPhylogenyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerProblemInPhylogenyInstance) x with
  | some i => decide (WellFormed i ∧ SteinerProblemInPhylogenyFeasible i)
  | none => false

/-- **STEINER PROBLEM IN PHYLOGENY is NP-complete.** Source: Foulds and Graham (1982). -/
public theorem_wanted steinerProblemInPhylogeny_npComplete :
    steinerProblemInPhylogenyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerProblemInPhylogenyDec

end MetaMathlibExt.Complexity.NPComplete.SteinerProblemInPhylogeny
