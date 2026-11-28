/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NNI DISTANCE: definitions

Source:
B. DasGupta, X. He, T. Jiang, M. Li, J. Tromp and L. Zhang, "On computing the nearest neighbor
interchange distance", in *Discrete Mathematical Problems with Medical Applications*, DIMACS
Series in Discrete Mathematics and Theoretical Computer Science 55 (2000), 125-143,
doi:10.1090/dimacs/055/09 (Section 1: nni operations and the nni distance; Theorem 1: "Let `T1`
and `T2` be two trees with unique leaf labels and `k` be an integer. It is NP-complete to decide if
`Dnni(T1, T2) ≤ k`"; conference version in the Proceedings of the Eighth Annual ACM-SIAM Symposium
on Discrete Algorithms (SODA 1997), 427-436).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TBRDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NNIDistance

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open MetaMathlibExt.Complexity.NPComplete.TBRDistance (TreeData IsPhyloTree toTree)

/-- The graph obtained from `G` by the nni operation on the edge `uv` that exchanges the subtree
at `b` (a neighbor of `u` other than `v`) with the subtree at `c` (a neighbor of `v` other than
`u`): the edges `ub` and `vc` are replaced by `uc` and `vb`. -/
def nniSwap {V : Type*} (G : SimpleGraph V) (u v b c : V) : SimpleGraph V :=
  G.deleteEdges {s(u, b), s(v, c)} ⊔ SimpleGraph.fromEdgeSet {s(u, c), s(v, b)}

variable {X : Type}

/-- `T'` is obtained from `T` by one nni operation: for an internal edge `uv` of `T` (neither
end is a leaf), a neighbor `b ≠ v` of `u` and a neighbor `c ≠ u` of `v`, some isomorphism from
`nniSwap T.G u v b c` to `T'` maps the leaf of each taxon in `T` to its leaf in `T'`. -/
def IsNNIStep (T T' : UnrootedBinaryTree X) : Prop :=
  ∃ u v b c : T.V, T.G.Adj u v ∧ T.G.degree u ≠ 1 ∧ T.G.degree v ≠ 1 ∧ T.G.Adj u b ∧ b ≠ v ∧
    T.G.Adj v c ∧ c ≠ u ∧
      ∃ φ : nniSwap T.G u v b c ≃g T'.G, ∀ x, φ (T.label x) = T'.label x

/-- The nni distance from `T₁` to `T₂` is at most `K`: for some `k ≤ K`, a sequence of trees
`S₀, …, S_k` with `T₁ ≅ S₀` and `S_k ≅ T₂` (label-preserving isomorphisms) has each `S_{j+1}`
obtained from `S_j` by one nni operation. -/
def NNIDistanceAtMost (T₁ T₂ : UnrootedBinaryTree X) (K : ℕ) : Prop :=
  ∃ (k : ℕ) (S : Fin (k + 1) → UnrootedBinaryTree X), k ≤ K ∧ T₁.Iso (S 0) ∧
    (∀ j : Fin k, IsNNIStep (S j.castSucc) (S j.succ)) ∧ (S (Fin.last k)).Iso T₂

/-- An instance: the number of taxa `m`, the trees `T₁` and `T₂`, and the bound `K`. -/
abbrev NNIDistanceInstance := ℕ × TreeData × TreeData × ℕ

/-- Well-formedness of an instance: both trees are unrooted binary phylogenetic trees on the taxa
`Fin m`. -/
def WellFormed (i : NNIDistanceInstance) : Prop :=
  IsPhyloTree i.1 i.2.1 ∧ IsPhyloTree i.1 i.2.2.1

/-- The nni distance between `T₁` and `T₂` is at most `K`. -/
def NNIDistanceFeasible (i : NNIDistanceInstance) : Prop :=
  ∃ (h₁ : IsPhyloTree i.1 i.2.1) (h₂ : IsPhyloTree i.1 i.2.2.1),
    NNIDistanceAtMost (toTree h₁) (toTree h₂) i.2.2.2

open Classical in
/-- NNI DISTANCE as a decision problem over bitstrings. -/
noncomputable def nniDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NNIDistanceInstance) x with
  | some i => decide (WellFormed i ∧ NNIDistanceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NNIDistance
