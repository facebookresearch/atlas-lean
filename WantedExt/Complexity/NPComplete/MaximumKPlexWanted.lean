/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM K-PLEX is NP-complete

Source:
B. Balasundaram, S. Butenko and I. V. Hicks, "Clique relaxations in social network analysis: the
maximum k-plex problem", Operations Research 59(1) (2011), 133-142, doi:10.1287/opre.1100.0851.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumKPlex

/-!
# MAXIMUM K-PLEX is NP-complete

Fix a positive integer `k`. INSTANCE: a simple undirected graph `G = (V, E)` and a positive
integer `c`. QUESTION: does there exist a `k`-plex of size `c` in `G`, where `S ⊆ V` is a
`k`-plex if every vertex of `S` has at least `|S| - k` neighbors in `S`
(`deg_{G[S]}(v) = |N(v) ∩ S| ≥ |S| - k` for all `v ∈ S`)? This is k-PLEX of Balasundaram,
Butenko and Hicks (Definition 1 and Section 2.1); their Theorem 2: "k-PLEX is NP-complete for
any fixed positive integer k". For `k = 1` a `k`-plex is a clique.

The family is stated as one theorem with `k` and `1 ≤ k` as parameters. `S` is a `Finset` of
vertices `Fin n` of the graph `Cslib.Complexity.Karp.edgeGraph n E`, and `N(v) ∩ S` is the set
of vertices of `S` adjacent to `v`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the size `c`. -/
abbrev MaximumKPlexInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MaximumKPlexInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- `S` is a `k`-plex of `G`: every vertex of `S` is adjacent to at least `|S| - k` vertices of
`S`. -/
def IsKPlex {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ S, S.card - k ≤ (S.filter fun u => G.Adj v u).card

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `c` is
positive. -/
def WellFormed (i : MaximumKPlexInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- Some `k`-plex of the graph has exactly `c` vertices. -/
def MaximumKPlexFeasible (k : ℕ) (i : MaximumKPlexInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card = i.2.2 ∧ IsKPlex (Graph i) k S

open Classical in
/-- MAXIMUM K-PLEX for a fixed `k` as a decision problem over bitstrings. -/
noncomputable def maximumKPlexDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumKPlexInstance) x with
  | some i => decide (WellFormed i ∧ MaximumKPlexFeasible k i)
  | none => false

/-- **MAXIMUM K-PLEX is NP-complete** for every fixed positive integer `k`. Source:
Balasundaram, Butenko and Hicks (2011), Theorem 2. -/
public theorem_wanted maximumKPlex_npComplete (k : ℕ) (hk : 1 ≤ k) :
    maximumKPlexDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (maximumKPlexDec k)

end MetaMathlibExt.Complexity.NPComplete.MaximumKPlex
