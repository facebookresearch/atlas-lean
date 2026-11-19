/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC SPANNING TREE for 3-stars is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND8] ISOMORPHIC SPANNING TREE
(p. 207), comment "Remains NP-complete even if ... (c) T is a 3-star (that is,
V_T = {v₀} ∪ {uᵢ, vᵢ, wᵢ : 1 ≤ i ≤ n}, E_T = {{v₀, uᵢ}, {uᵢ, vᵢ}, {vᵢ, wᵢ} : 1 ≤ i ≤ n})"
(credited there to Garey and Johnson, unpublished).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IsomorphicSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeThreeStar

open MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree

/-!
# ISOMORPHIC SPANNING TREE for 3-stars is NP-complete

INSTANCE: a graph `G = (V, E)` and a 3-star `T = (V_T, E_T)`, that is,
`V_T = {v₀} ∪ {uᵢ, vᵢ, wᵢ : 1 ≤ i ≤ n}` and
`E_T = {{v₀, uᵢ}, {uᵢ, vᵢ}, {vᵢ, wᵢ} : 1 ≤ i ≤ n}`. QUESTION: does `G` contain a spanning tree
isomorphic to `T`?

This is the restriction of ISOMORPHIC SPANNING TREE ([ND8], `IsomorphicSpanningTreeWanted`) to
3-stars `T`. The instance type, `IsomorphicSpanningTree.WellFormed` (simple edge lists, `T` a
tree) and `IsomorphicSpanningTree.IsomorphicSpanningTreeFeasible` are the parent's, unchanged;
`WellFormed` adds that `T` is isomorphic to the 3-star `threeStar n` for some `n`, the graph on
`0, ..., 3n` with `v₀ = 0`, `uᵢ = 3i + 1`, `vᵢ = 3i + 2`, `wᵢ = 3i + 3` (`0 ≤ i < n`). `T` is
given by an arbitrary edge list, so a 3-star is recognized up to isomorphism, as the property
"`T` is a 3-star" reads. `n = 0` (the one-vertex tree) is allowed, as the empty range
`1 ≤ i ≤ 0` gives; it adds only trivial instances.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The edges of the 3-star with `n` legs: for each `k < n`, the leg `0 - (3k + 1) - (3k + 2) -
(3k + 3)`. -/
def threeStarEdges (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun k =>
    [(0, 3 * k + 1), (3 * k + 1, 3 * k + 2), (3 * k + 2, 3 * k + 3)]

/-- The 3-star with `n` legs as a `SimpleGraph (Fin (3n + 1))`. -/
def threeStar (n : ℕ) : SimpleGraph (Fin (3 * n + 1)) :=
  Cslib.Complexity.Karp.edgeGraph (3 * n + 1) (threeStarEdges n)

/-- Well-formedness of an instance: the parent's (simple edge lists, `T` a tree), and `T` is
isomorphic to a 3-star. -/
def WellFormed (i : IsomorphicSpanningTreeInstance) : Prop :=
  IsomorphicSpanningTree.WellFormed i ∧ ∃ n : ℕ, Nonempty (TreeGraph i ≃g threeStar n)

open Classical in
/-- ISOMORPHIC SPANNING TREE for 3-stars as a decision problem over bitstrings. -/
noncomputable def isomorphicSpanningTreeThreeStarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IsomorphicSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ IsomorphicSpanningTreeFeasible i)
  | none => false

/-- **ISOMORPHIC SPANNING TREE is NP-complete for 3-stars.** Source: Garey and Johnson (1979),
[ND8], comment (c) (Garey and Johnson, unpublished). -/
public theorem_wanted isomorphicSpanningTreeThreeStar_npComplete :
    isomorphicSpanningTreeThreeStarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L isomorphicSpanningTreeThreeStarDec

end MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeThreeStar
