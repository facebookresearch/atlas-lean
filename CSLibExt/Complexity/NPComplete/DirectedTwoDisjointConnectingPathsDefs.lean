/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED DISJOINT CONNECTING PATHS with `k = 2`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT CONNECTING PATHS,
p. 217 (the problem; its comment records that the directed version is NP-complete in general);
S. Fortune, J. Hopcroft, and J. Wyllie, "The directed subgraph homeomorphism problem",
Theoretical Computer Science 10 (1980), 111-121, doi:10.1016/0304-3975(80)90009-2 (the
directed problem is NP-complete already for two pairs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), arc list, `s₁`, `t₁`, `s₂`,
`t₂`. -/
abbrev DirectedTwoDisjointConnectingPathsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: the arcs are distinct, loopless and between vertices, and
`s₁, t₁, s₂, t₂` are pairwise distinct vertices. -/
def WellFormed (i : DirectedTwoDisjointConnectingPathsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    (∀ v ∈ [i.2.2.1, i.2.2.2.1, i.2.2.2.2.1, i.2.2.2.2.2], v < i.1) ∧
    [i.2.2.1, i.2.2.2.1, i.2.2.2.2.1, i.2.2.2.2.2].Nodup

/-- `p` is a directed path from `s` to `t` along the arcs `A`: distinct vertices, first `s`,
last `t`, an arc from each vertex to the next. -/
def IsDirectedPath (A : List (ℕ × ℕ)) (s t : ℕ) (p : List ℕ) : Prop :=
  p.head? = some s ∧ p.getLast? = some t ∧ p.Nodup ∧ p.IsChain fun u v => (u, v) ∈ A

/-- There are vertex-disjoint directed paths from `s₁` to `t₁` and from `s₂` to `t₂`. -/
def DirectedTwoDisjointConnectingPathsFeasible
    (i : DirectedTwoDisjointConnectingPathsInstance) : Prop :=
  ∃ p q : List ℕ, IsDirectedPath i.2.1 i.2.2.1 i.2.2.2.1 p ∧
    IsDirectedPath i.2.1 i.2.2.2.2.1 i.2.2.2.2.2 q ∧ p.Disjoint q

open Classical in
/-- DIRECTED DISJOINT CONNECTING PATHS with `k = 2`, as a decision problem over bitstrings. -/
noncomputable def directedTwoDisjointConnectingPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedTwoDisjointConnectingPathsInstance) x with
  | some i => decide (WellFormed i ∧ DirectedTwoDisjointConnectingPathsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPaths
