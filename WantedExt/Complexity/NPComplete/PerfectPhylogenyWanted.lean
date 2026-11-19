/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERFECT PHYLOGENY is NP-complete

Source:
H. L. Bodlaender, M. R. Fellows, and T. J. Warnow, "Two strikes against perfect phylogeny",
Automata, Languages and Programming (ICALP 1992), Lecture Notes in Computer Science 623, 273-283,
doi:10.1007/3-540-55719-9_80, Section 1 (the problem) and Section 3 (Theorem 1 and its
consequence that Perfect Phylogeny is NP-complete);
M. A. Steel, "The complexity of reconstructing trees from qualitative characters and subtrees",
Journal of Classification 9 (1992), 91-116, doi:10.1007/BF02618470.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PerfectPhylogeny

/-!
# PERFECT PHYLOGENY is NP-complete

INSTANCE: a set of `n ≥ 1` species described by `m` characters: each species has a state
(a natural number) for each character, and the number of states of a character is unbounded.
QUESTION: does a perfect phylogeny exist (Bodlaender, Fellows and Warnow, Section 1), i.e., a
tree whose nodes include the species, in which every node is assigned a state of each character
(one of the states the species have), each species keeps its own states, and "for each state of
each character, the set of nodes in the tree having that state should form a connected
component"?

The tree is a `SimpleGraph (Fin N)` with `SimpleGraph.IsTree`, for some `N`; the species are
placed at nodes by a map `f`, as in Steel's definition of compatible characters (a tree with a
labelling of its vertices by the species). Placing species at internal nodes, or several species
at one node, gives the same yes-instances as requiring the species to be distinct leaves: a pendant
leaf carrying a node's states can be attached to it without breaking connectivity. "Connected"
for a state class `{v | lab v c = x}` is `Preconnected` of the induced subgraph (classes of unused
states are empty).

The problem is polynomial for binary characters and for a fixed number of characters or of states;
with an unbounded number of states it is NP-complete (Bodlaender, Fellows and Warnow, Section 3,
via the polynomial equivalence with Triangulating Colored Graphs; Steel 1992).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of characters and, for each species, its list of `m` states. -/
abbrev PerfectPhylogenyInstance := ℕ × List (List ℕ)

/-- Well-formedness: there is at least one species, and every species has a state for each of
the `m` characters. -/
def WellFormed (i : PerfectPhylogenyInstance) : Prop :=
  i.2 ≠ [] ∧ ∀ s ∈ i.2, s.length = i.1

/-- The state of species `s` for character `c`. -/
def state (i : PerfectPhylogenyInstance) (s c : ℕ) : ℕ :=
  (i.2.getD s []).getD c 0

/-- `(T, f, lab)` is a perfect phylogeny for the instance: `T` is a tree, species `s` sits at node
`f s` and keeps its states there, every node carries for each character a state that some species
has, and for each character `c` and state `x` the nodes with state `x` induce a connected
subgraph. -/
def IsPerfectPhylogeny (i : PerfectPhylogenyInstance) {N : ℕ} (T : SimpleGraph (Fin N))
    (f : Fin i.2.length → Fin N) (lab : Fin N → Fin i.1 → ℕ) : Prop :=
  T.IsTree ∧ (∀ s c, lab (f s) c = state i s c) ∧
    (∀ v c, ∃ s : Fin i.2.length, lab v c = state i s c) ∧
    ∀ c x, (T.induce {v | lab v c = x}).Preconnected

/-- A perfect phylogeny exists. -/
def PerfectPhylogenyFeasible (i : PerfectPhylogenyInstance) : Prop :=
  ∃ N, ∃ T : SimpleGraph (Fin N), ∃ f lab, IsPerfectPhylogeny i T f lab

open Classical in
/-- PERFECT PHYLOGENY as a decision problem over bitstrings. -/
noncomputable def perfectPhylogenyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PerfectPhylogenyInstance) x with
  | some i => decide (WellFormed i ∧ PerfectPhylogenyFeasible i)
  | none => false

/-- **PERFECT PHYLOGENY is NP-complete.** Source: Bodlaender, Fellows and Warnow (1992),
Section 3; Steel (1992). -/
public theorem_wanted perfectPhylogeny_npComplete :
    perfectPhylogenyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L perfectPhylogenyDec

end MetaMathlibExt.Complexity.NPComplete.PerfectPhylogeny
