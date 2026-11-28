/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC SPANNING TREE for 3-stars: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND8] ISOMORPHIC SPANNING TREE
(p. 207), comment "Remains NP-complete even if ... (c) T is a 3-star (that is,
V_T = {v₀} ∪ {uᵢ, vᵢ, wᵢ : 1 ≤ i ≤ n}, E_T = {{v₀, uᵢ}, {uᵢ, vᵢ}, {vᵢ, wᵢ} : 1 ≤ i ≤ n})"
(credited there to Garey and Johnson, unpublished).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IsomorphicSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeThreeStar

open MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree

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

end MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeThreeStar
