/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# H-MATCHING is NP-complete for every fixed H with a component of at least 3 vertices

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem [GT14]
MAXIMUM H-MATCHING (the decision version of the optimization problem stated here);
D. G. Kirkpatrick and P. Hell, "On the completeness of a generalized matching
problem", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(1978), 240-245, doi:10.1145/800133.804353;
D. G. Kirkpatrick and P. Hell, "On the complexity of general graph factor
problems", SIAM Journal on Computing 12(3) (1983), 601-609, doi:10.1137/0212040;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), comment to problem [GT12]
PARTITION INTO ISOMORPHIC SUBGRAPHS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PerfectHPackingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HMatching

/-!
# H-MATCHING is NP-complete for every fixed H with a component of at least 3 vertices

For a fixed graph `H = (V_H, E_H)` with at least three vertices in some connected component:
INSTANCE: a graph `G = (V_G, E_G)` and a positive integer `K`.
QUESTION: is there an `H`-matching for `G` of cardinality at least `K`, i.e., a collection
`G₁, G₂, …, G_k` (`k ≥ K`) of disjoint subgraphs of `G`, each isomorphic to `H`?

This is the decision version of Crescenzi and Kann's MAXIMUM H-MATCHING (also called maximum
`H`-packing). Kirkpatrick and Hell prove that deciding whether `G` has a perfect `H`-matching
(an `H`-factor: disjoint copies of `H` covering every vertex) is NP-complete whenever `H` has a
component with at least three vertices; that question is this one with `K = |V_G| / |V_H|`
(and a fixed no-instance when `|V_H|` does not divide `|V_G|`), so this problem is NP-hard for
the same patterns. Membership in NP: the certificate is the `K` copies.

`H` is not part of the instance: it is the pattern `(m, hs)` (vertices `Fin m`, simple edge list
`hs`), a parameter of the decision problem `hMatchingDec m hs`, and the theorem is stated for
every pattern satisfying `PerfectHPacking.ValidPattern` from
`WantedExt.Complexity.NPComplete.PerfectHPackingWanted` (a simple edge list whose graph has a
connected component, Mathlib's `SimpleGraph.ConnectedComponent`, with at least `3` vertices),
the pattern condition of the perfect version. A subgraph of `G` isomorphic to `H` is the image of
an injective graph homomorphism from `H` to `G`, Mathlib's `SimpleGraph.Copy`; the subgraphs are
disjoint when the vertex images are pairwise disjoint. Asking for exactly `K` disjoint copies is
the same as asking for at least `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list of `G`, bound `K`. -/
abbrev HMatchingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HMatchingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : HMatchingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- `K` pairwise vertex-disjoint subgraphs of `G` isomorphic to `H`: copies of the pattern in `G`
(injective homomorphisms from the pattern graph `edgeGraph m hs`) with pairwise disjoint vertex
images. -/
def HMatchingFeasible (m : ℕ) (hs : List (ℕ × ℕ)) (i : HMatchingInstance) : Prop :=
  ∃ f : Fin i.2.2 → (Cslib.Complexity.Karp.edgeGraph m hs).Copy (Graph i),
    Pairwise fun j j' => Disjoint (Set.range (f j)) (Set.range (f j'))

open Classical in
/-- H-MATCHING for the fixed pattern `(m, hs)` as a decision problem over bitstrings. -/
noncomputable def hMatchingDec (m : ℕ) (hs : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HMatchingInstance) x with
  | some i => decide (WellFormed i ∧ HMatchingFeasible m hs i)
  | none => false

/-- **H-MATCHING is NP-complete for every fixed `H` with a connected component of at least 3
vertices.** Source: Crescenzi and Kann, [GT14]; Kirkpatrick and Hell (1978, 1983). -/
public theorem_wanted hMatching_npComplete (m : ℕ) (hs : List (ℕ × ℕ))
    (_hH : PerfectHPacking.ValidPattern m hs) :
    hMatchingDec m hs ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hMatchingDec m hs)

end MetaMathlibExt.Complexity.NPComplete.HMatching
