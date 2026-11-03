/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The Branch Length Score of a conserved motif instance

Kheradpour, Stark, Roy and Kellis (2007) score the conservation of a motif instance in an
alignment of many genomes by its **Branch Length Score** (BLS): the total branch length of the
subtree of the species phylogeny connecting the species `S` in which the instance is present,
as a fraction of the total branch length of the tree.

The public BLS is defined over the repository's canonical
`UnrootedBinaryTree X` (`MathlibExt/Biology/Phylogenetics/UnrootedTreeCount`), with an
edge-weight function `w : Sym2 T.V → ℝ` on the undirected edges, the same weighted-edge
convention as `dist_eq_sum_darts` in `NeighborJoining`. An edge of a tree is in the smallest
subtree connecting the leaves `S` iff `S` has leaves on both sides of the edge. We take this
characterization as the definition: `bls S T w` sums, over the darts of `T` (each undirected
edge once in each direction, hence the factor `1 / 2`), the edge length times the indicator
that `S` meets both sides of the edge, where the side of a dart is `edgeSide`
(`CSLibExt/Bioinformatics/Phylogenetics/Splits`). Duplicate species labels are impossible
here: the tree's `label` is a bijection between the taxa and the leaves.

The rooted binary tree `Tree L` below is a *private* implementation of the same edge-sum
specification: the two-pass post-order algorithm `rootedBlsAlg` is proved to compute the
rooted BLS (`rootedBlsAlg_eq_rootedBls`). It is kept for that algorithm and its proof; the
public BLS is the edge sum over `UnrootedBinaryTree` above, not a conversion of this
representation.

## Main results

* `bls_nonneg`, `bls_le_totalLength`: with nonnegative edge lengths the BLS is between `0`
  and the total branch length.
* `bls_mono`: with nonnegative edge lengths the BLS is monotone in `S`.
* `bls_empty`, `bls_singleton`: the BLS of zero or one species is `0`.
* `bls_leaves`: the BLS of all species is the total branch length.
* `bls_union_le`: for overlapping `S`, `S'` the BLS is subadditive.
* `blsFrac_nonneg`, `blsFrac_le_one`: the normalized score lies in `[0, 1]`.

## References

* P. Kheradpour, A. Stark, S. Roy, M. Kellis, *Reliable prediction of regulator targets using
  12 Drosophila genomes*, Genome Res. 17 (2007), 1919–1931.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, chapter 3 (edges and
  splits of a tree).
-/

@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.BranchLengthScore

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

variable {X : Type} [Fintype X] [DecidableEq X]
variable {L : Type*} [DecidableEq L]

/-- Whether the leaf set `S` meets both sides of an edge with leaf set `B` below it, inside a
tree with leaf set `U`: `S ∩ B` and `S ∩ (U \ B)` are nonempty. -/
def Separates (U S B : Finset L) : Prop := (S ∩ B).Nonempty ∧ (S ∩ (U \ B)).Nonempty

/-- `Separates` is decidable. -/
instance (U S B : Finset L) : Decidable (Separates U S B) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem separates_mono {U S S' B : Finset L} (h : S ⊆ S') :
    Separates U S B → Separates U S' B := fun ⟨h1, h2⟩ =>
  ⟨h1.mono (Finset.inter_subset_inter_right h), h2.mono (Finset.inter_subset_inter_right h)⟩

private theorem ite_le_ite {p q : Prop} [Decidable p] [Decidable q] {a : ℝ} (ha : 0 ≤ a)
    (h : p → q) : (if p then a else 0) ≤ if q then a else 0 := by
  by_cases hp : p
  · simp [hp, h hp]
  · simp only [hp, ite_false]; split_ifs <;> linarith

private theorem separates_union {U S S' B : Finset L} (hSS : (S ∩ S').Nonempty)
    (h : Separates U (S ∪ S') B) (hS : S ⊆ U) :
    Separates U S B ∨ Separates U S' B := by
  obtain ⟨x, hx⟩ := hSS
  rw [Finset.mem_inter] at hx
  obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := h
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hy hz
  by_cases hxB : x ∈ B
  · rcases hz.1 with hzS | hzS
    · exact Or.inl ⟨⟨x, Finset.mem_inter.2 ⟨hx.1, hxB⟩⟩, ⟨z, by simp [hzS, hz.2]⟩⟩
    · exact Or.inr ⟨⟨x, Finset.mem_inter.2 ⟨hx.2, hxB⟩⟩, ⟨z, by simp [hzS, hz.2]⟩⟩
  · have hxU : x ∈ U \ B := Finset.mem_sdiff.2 ⟨hS hx.1, hxB⟩
    rcases hy.1 with hyS | hyS
    · exact Or.inl ⟨⟨y, by simp [hyS, hy.2]⟩, ⟨x, Finset.mem_inter.2 ⟨hx.1, hxU⟩⟩⟩
    · exact Or.inr ⟨⟨y, by simp [hyS, hy.2]⟩, ⟨x, Finset.mem_inter.2 ⟨hx.2, hxU⟩⟩⟩

private theorem ite_or_le {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] {a : ℝ}
    (ha : 0 ≤ a) (h : p → q ∨ r) :
    (if p then a else 0) ≤ (if q then a else 0) + if r then a else 0 := by
  by_cases hp : p
  · rcases h hp with hq | hr
    · simp only [hp, hq, ite_true]; split_ifs <;> linarith
    · simp only [hp, hr, ite_true]; split_ifs <;> linarith
  · simp only [hp, ite_false]; split_ifs <;> linarith

omit [Fintype X] in
private theorem separates_singleton {U : Finset X} (x : X) (B : Finset X) :
    ¬ Separates U {x} B := by
  rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_sdiff] at hy hz
  exact hz.2.2 (hz.1 ▸ hy.1 ▸ hy.2)

private theorem separates_univ_of_nonempty {B : Finset X} (hB : B.Nonempty)
    (hBc : Bᶜ.Nonempty) : Separates Finset.univ Finset.univ B := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hB
    exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  · obtain ⟨x, hx⟩ := hBc
    exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_univ x,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.mem_compl.mp hx⟩⟩⟩

/-! ### The public BLS over `UnrootedBinaryTree` -/

/-- Edge lengths are nonnegative: every dart's undirected edge has nonnegative length. -/
def NonnegWeights (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) : Prop :=
  ∀ t : T.G.Dart, 0 ≤ w t.edge

/-- The total branch length: half the sum of the edge lengths over the darts, since each
undirected edge is traversed once in each direction. -/
noncomputable def totalLength (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) : ℝ :=
  (1 / 2) * ∑ t : T.G.Dart, w t.edge

/-- **The Branch Length Score** (unnormalized): the total branch length of the smallest
subtree of `T` connecting the leaves `S`, as half the sum over the darts of the edge length
times the indicator that `S` meets both sides (`edgeSide`) of the dart's edge. -/
noncomputable def bls (S : Finset X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) : ℝ :=
  (1 / 2) * ∑ t : T.G.Dart, w t.edge *
    if Separates Finset.univ S (edgeSide T t.fst t.snd) then 1 else 0

/-- The normalized Branch Length Score, `bls S T w / totalLength T w`, as reported by
Kheradpour et al. (a fraction of the total branch length). -/
noncomputable def blsFrac (S : Finset X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) : ℝ :=
  bls S T w / totalLength T w

private theorem edgeSide_mem_edgeSplits (T : UnrootedBinaryTree X) {p v : T.V}
    (hpv : T.G.Adj p v) : edgeSide T p v ∈ edgeSplits T :=
  Finset.mem_image.mpr ⟨(p, v), Finset.mem_filter.mpr ⟨by simp, hpv⟩, rfl⟩

/-- Both sides of an edge are nonempty: a side is a split, hence a cluster or the complement
of one. -/
private theorem edgeSide_nonempty (T : UnrootedBinaryTree X) (a : X) {p v : T.V}
    (hpv : T.G.Adj p v) :
    (edgeSide T p v).Nonempty ∧ (edgeSide T p v)ᶜ.Nonempty := by
  have hsplit : ∀ B ∈ splitSet T a, B.Nonempty ∧ Bᶜ.Nonempty := by
    intro B hB
    simp only [splitSet, Finset.mem_union, Finset.mem_image] at hB
    rcases hB with hB | ⟨C, hC, rfl⟩
    · exact ⟨((isBinaryHierarchy_clusterSet T a).2.1 B hB).1,
        ⟨a, Finset.mem_compl.mpr (notMem_of_mem_clusterSet T a hB)⟩⟩
    · refine ⟨⟨a, Finset.mem_compl.mpr (notMem_of_mem_clusterSet T a hC)⟩, ?_⟩
      rw [compl_compl]
      exact ((isBinaryHierarchy_clusterSet T a).2.1 C hC).1
  have hA : edgeSide T p v ∈ splitSet T a := by
    rw [splitSet_eq_edgeSplits]; exact edgeSide_mem_edgeSplits T hpv
  have hAc : (edgeSide T p v)ᶜ ∈ splitSet T a := by
    rw [splitSet_eq_edgeSplits, compl_edgeSide T hpv]
    exact edgeSide_mem_edgeSplits T hpv.symm
  exact ⟨(hsplit _ hA).1, (hsplit _ hAc).1⟩

/-- The BLS is nonnegative for nonnegative edge lengths. -/
theorem bls_nonneg (S : Finset X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ)
    (hw : NonnegWeights T w) : 0 ≤ bls S T w := by
  rw [bls]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => ?_)
  exact mul_nonneg (hw t) (by split_ifs <;> norm_num)

/-- The BLS is at most the total branch length. -/
theorem bls_le_totalLength (S : Finset X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ)
    (hw : NonnegWeights T w) : bls S T w ≤ totalLength T w := by
  rw [bls, totalLength]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) (by norm_num)
  by_cases h : Separates Finset.univ S (edgeSide T t.fst t.snd)
  · rw [ite_eq_left h]; simp
  · rw [ite_eq_right h]; simpa using hw t

/-- **Monotonicity**: with nonnegative edge lengths, more conserving species never lower the
BLS. -/
theorem bls_mono {S S' : Finset X} (h : S ⊆ S') (T : UnrootedBinaryTree X)
    (w : Sym2 T.V → ℝ) (hw : NonnegWeights T w) : bls S T w ≤ bls S' T w := by
  rw [bls, bls]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) (by norm_num)
  exact mul_le_mul_of_nonneg_left
    (ite_le_ite zero_le_one fun hs => separates_mono h hs) (hw t)

/-- The BLS of the empty set is `0`. -/
theorem bls_empty (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) : bls ∅ T w = 0 := by
  have hnot : ∀ t : T.G.Dart, ¬ Separates Finset.univ ∅ (edgeSide T t.fst t.snd) := by
    intro t h
    obtain ⟨x, hx⟩ := h.1
    exact Finset.notMem_empty x (Finset.mem_inter.mp hx).1
  have hterm : ∀ t : T.G.Dart, w t.edge *
      (if Separates Finset.univ ∅ (edgeSide T t.fst t.snd) then (1 : ℝ) else 0) = 0 := by
    intro t
    rw [ite_eq_right (hnot t)]
    simp
  rw [bls, Finset.sum_eq_zero (fun t _ => hterm t), mul_zero]

/-- **A single species has BLS `0`** (a motif present in one genome is not conserved). -/
theorem bls_singleton (x : X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) :
    bls {x} T w = 0 := by
  have hterm : ∀ t : T.G.Dart, w t.edge *
      (if Separates Finset.univ {x} (edgeSide T t.fst t.snd) then (1 : ℝ) else 0) = 0 := by
    intro t
    rw [ite_eq_right (separates_singleton x _)]
    simp
  rw [bls, Finset.sum_eq_zero (fun t _ => hterm t), mul_zero]

/-- **All species give the whole tree**: the BLS of the set of all leaves is the total branch
length. -/
theorem bls_leaves (a : X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ) :
    bls Finset.univ T w = totalLength T w := by
  rw [bls, totalLength]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hsep : Separates Finset.univ Finset.univ (edgeSide T t.fst t.snd) :=
    separates_univ_of_nonempty (edgeSide_nonempty T a t.adj).1 (edgeSide_nonempty T a t.adj).2
  rw [ite_eq_left hsep]; simp

/-- **Subadditivity**: for sets of species `S`, `S'` that share a species, the subtree
connecting `S ∪ S'` is at most as long as the two subtrees together. -/
theorem bls_union_le {S S' : Finset X} (hSS : (S ∩ S').Nonempty) (T : UnrootedBinaryTree X)
    (w : Sym2 T.V → ℝ) (hw : NonnegWeights T w) :
    bls (S ∪ S') T w ≤ bls S T w + bls S' T w := by
  simp only [bls]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) (by norm_num)
  have h := ite_or_le (a := (1 : ℝ)) zero_le_one fun hs =>
    separates_union (B := edgeSide T t.fst t.snd) hSS hs (Finset.subset_univ S)
  calc w t.edge * (if Separates Finset.univ (S ∪ S') (edgeSide T t.fst t.snd) then (1 : ℝ)
          else 0)
      ≤ w t.edge * ((if Separates Finset.univ S (edgeSide T t.fst t.snd) then (1 : ℝ)
          else 0) + (if Separates Finset.univ S' (edgeSide T t.fst t.snd) then (1 : ℝ)
          else 0)) := mul_le_mul_of_nonneg_left h (hw t)
    _ = w t.edge * (if Separates Finset.univ S (edgeSide T t.fst t.snd) then (1 : ℝ)
          else 0) + w t.edge * (if Separates Finset.univ S' (edgeSide T t.fst t.snd)
          then (1 : ℝ) else 0) := by rw [mul_add]

/-- The normalized BLS is nonnegative. -/
theorem blsFrac_nonneg (S : Finset X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ)
    (hw : NonnegWeights T w) : 0 ≤ blsFrac S T w := by
  rw [blsFrac]
  refine div_nonneg (bls_nonneg S T w hw) ?_
  rw [totalLength]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => hw t)

/-- The normalized BLS is at most `1` when the tree has positive total length. -/
theorem blsFrac_le_one (S : Finset X) (T : UnrootedBinaryTree X) (w : Sym2 T.V → ℝ)
    (hw : NonnegWeights T w) (hpos : 0 < totalLength T w) : blsFrac S T w ≤ 1 := by
  rw [blsFrac]
  exact (div_le_one hpos).2 (bls_le_totalLength S T w hw)

/-! ### Dart sums and pendant edges -/

omit [Fintype X] [DecidableEq X] in
/-- Every vertex other than the leaf `a` has a neighbor one step closer to `a`. -/
private theorem exists_parent (T : UnrootedBinaryTree X) (a : X) {v : T.V}
    (hv : v ≠ T.label a) :
    ∃ p, T.G.Adj p v ∧ T.G.dist (T.label a) v = T.G.dist (T.label a) p + 1 := by
  obtain ⟨q, hq⟩ := T.isTree.connected.exists_walk_length_eq_dist v (T.label a)
  cases q with
  | nil => exact absurd rfl hv
  | @cons _ c _ h q' =>
    refine ⟨c, h.symm, ?_⟩
    have h1 := SimpleGraph.dist_le q'
    have h3 := T.isTree.connected.dist_triangle (u := v) (v := c) (w := T.label a)
    have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    simp only [SimpleGraph.Walk.length_cons] at hq
    have e1 : T.G.dist (T.label a : T.V) v = T.G.dist v (T.label a) := SimpleGraph.dist_comm
    have e2 : T.G.dist (T.label a : T.V) c = T.G.dist c (T.label a) := SimpleGraph.dist_comm
    omega

private theorem adj_unique_of_degree_one {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {v u w : V} (hv : G.degree v = 1) (hu : G.Adj v u)
    (hw : G.Adj v w) : u = w := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hv
  obtain ⟨z, hz⟩ := hv
  have hu' : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hu
  have hw' : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).mpr hw
  rw [hz, Finset.mem_singleton] at hu' hw'
  rw [hu', hw']

omit [DecidableEq X] in
/-- **The side of a pendant edge is the singleton of its leaf**: the taxa whose leaf is
closer to the leaf vertex than to its neighbor are exactly that leaf's taxon. -/
theorem edgeSide_of_leaf (T : UnrootedBinaryTree X) {x : X} {p : T.V}
    (hp : T.G.Adj p (T.label x)) : edgeSide T p (T.label x) = {x} := by
  ext y
  simp only [edgeSide, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hlt
    by_contra hyx
    have hne : (T.label x : T.V) ≠ T.label y :=
      fun h => hyx (T.label.injective (Subtype.ext h)).symm
    obtain ⟨p₀, hp₀, hd₀⟩ := exists_parent T y hne
    have hdeg : T.G.degree (T.label x) = 1 := (T.label x).2
    have hpeq : p = p₀ := adj_unique_of_degree_one hdeg hp.symm hp₀.symm
    rw [← hpeq] at hd₀
    omega
  · rintro rfl
    rw [SimpleGraph.dist_self, SimpleGraph.dist_eq_one_iff_adj.mpr hp.symm]
    norm_num

omit [Fintype X] [DecidableEq X] in
/-- A sum over darts of a function of the undirected edge is twice the sum over the edges:
the two darts of each edge contribute equally. -/
theorem dart_sum_edge (T : UnrootedBinaryTree X) (f : Sym2 T.V → ℝ) :
    ∑ t : T.G.Dart, f t.edge = ∑ e ∈ T.G.edgeFinset, 2 * f e := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (g := SimpleGraph.Dart.edge) (t := T.G.edgeFinset)
    (fun t _ => SimpleGraph.mem_edgeFinset.mpr t.edge_mem)]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_const, nsmul_eq_mul,
    T.G.dart_edge_fiber_card e (SimpleGraph.mem_edgeFinset.mp he)]
  norm_num

/-! ### Private rooted implementation: the two-pass post-order algorithm -/

/-- A rooted binary tree with leaf labels `L` and real branch lengths: `node a l b r` has the
edge of length `a` to `l` and the edge of length `b` to `r`. Private: the public BLS is the
edge sum over `UnrootedBinaryTree` above. -/
private inductive Tree (L : Type*) where
  /-- A leaf (a species). -/
  | leaf : L → Tree L
  /-- An internal node with branch lengths `a` and `b` to its subtrees `l` and `r`. -/
  | node : ℝ → Tree L → ℝ → Tree L → Tree L

namespace Tree

/-- The set of leaf labels. -/
private def leaves : Tree L → Finset L
  | leaf x => {x}
  | node _ l _ r => leaves l ∪ leaves r

/-- Distinct leaf labels: the two subtrees of every node have disjoint leaf sets. -/
private def WellLabeled : Tree L → Prop
  | leaf _ => True
  | node _ l _ r => WellLabeled l ∧ WellLabeled r ∧ Disjoint (leaves l) (leaves r)

/-- Every branch length is nonnegative. -/
private def NonnegLengths : Tree L → Prop
  | leaf _ => True
  | node a l b r => 0 ≤ a ∧ 0 ≤ b ∧ NonnegLengths l ∧ NonnegLengths r

/-- The total branch length. -/
private def totalLength : Tree L → ℝ
  | leaf _ => 0
  | node a l b r => a + b + totalLength l + totalLength r

/-- Every tree has a leaf. -/
private theorem leaves_nonempty : ∀ t : Tree L, t.leaves.Nonempty
  | leaf x => Finset.singleton_nonempty x
  | node _ l _ _ => (leaves_nonempty l).mono Finset.subset_union_left

end Tree

open _root_.Cslib.Bioinformatics.Phylogenetics.BranchLengthScore.Tree

/-- The total length of the edges of `t` whose two sides (inside a tree with leaf set `U`) both
meet `S`. -/
private noncomputable def blsWithin (U S : Finset L) : Tree L → ℝ
  | leaf _ => 0
  | node a l b r =>
    (if Separates U S l.leaves then a else 0) + (if Separates U S r.leaves then b else 0) +
      blsWithin U S l + blsWithin U S r

/-- The rooted Branch Length Score (unnormalized): the total branch length of the smallest
subtree of `t` connecting the leaves `S`. -/
private noncomputable def rootedBls (S : Finset L) (t : Tree L) : ℝ := blsWithin t.leaves S t

/-- The normalized rooted Branch Length Score. -/
private noncomputable def rootedBlsFrac (S : Finset L) (t : Tree L) : ℝ :=
  rootedBls S t / t.totalLength

/-- One post-order pass with the total number `k` of marked leaves known: returns the number of
leaves of `S` in the subtree and the subtree's partial score. -/
private noncomputable def blsGo (S : Finset L) (k : ℕ) : Tree L → ℕ × ℝ
  | leaf x => (if x ∈ S then 1 else 0, 0)
  | node a l b r =>
    let pl := blsGo S k l
    let pr := blsGo S k r
    (pl.1 + pr.1, (if 0 < pl.1 ∧ pl.1 < k then a else 0) +
      (if 0 < pr.1 ∧ pr.1 < k then b else 0) + pl.2 + pr.2)

/-- The number of leaves of `S` in `t`, by one pass. -/
private def markedCount (S : Finset L) : Tree L → ℕ
  | leaf x => if x ∈ S then 1 else 0
  | node _ l _ r => markedCount S l + markedCount S r

/-- **The linear-time BLS algorithm**: count the marked leaves, then one post-order pass. -/
private noncomputable def rootedBlsAlg (S : Finset L) (t : Tree L) : ℝ :=
  (blsGo S (markedCount S t) t).2

/-- The first component of `blsGo` is the marked-leaf count. -/
private theorem blsGo_fst (S : Finset L) (k : ℕ) : ∀ t : Tree L, (blsGo S k t).1 = markedCount S t
  | leaf _ => rfl
  | node _ l _ r => by simp [blsGo, markedCount, blsGo_fst S k l, blsGo_fst S k r]

/-- With distinct labels, `markedCount S t` is the number of leaves of `t` in `S`. -/
private theorem markedCount_eq_card (S : Finset L) :
    ∀ t : Tree L, t.WellLabeled → markedCount S t = (S ∩ t.leaves).card
  | leaf x, _ => by
      by_cases hx : x ∈ S <;> simp [markedCount, leaves, hx, Finset.inter_singleton_of_mem,
        Finset.inter_singleton_of_notMem]
  | node _ l _ r, ⟨hl, hr, hd⟩ => by
      rw [markedCount, markedCount_eq_card S l hl, markedCount_eq_card S r hr, leaves,
        Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
          (Finset.disjoint_of_subset_left Finset.inter_subset_right
            (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]

private theorem separates_iff_card {U S B : Finset L} (hB : B ⊆ U) :
    Separates U S B ↔ 0 < (S ∩ B).card ∧ (S ∩ B).card < (S ∩ U).card := by
  unfold Separates
  rw [Finset.card_pos]
  refine and_congr Iff.rfl ?_
  have hsub : S ∩ B ⊆ S ∩ U := Finset.inter_subset_inter_left hB
  have hdiff : S ∩ (U \ B) = (S ∩ U) \ (S ∩ B) := by
    ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [hdiff, Finset.sdiff_nonempty]
  constructor
  · intro h; exact lt_of_le_of_ne (Finset.card_le_card hsub) fun he =>
      h (Finset.eq_of_subset_of_card_le hsub he.ge).symm.subset
  · intro h hsub'; exact absurd (Finset.card_le_card hsub') (not_le.2 h)

private theorem blsGo_snd (S U : Finset L) :
    ∀ t : Tree L, t.WellLabeled → t.leaves ⊆ U →
      (blsGo S (S ∩ U).card t).2 = blsWithin U S t
  | leaf _, _, _ => rfl
  | node a l b r, ⟨hl, hr, hd⟩, hU => by
      have hlU : l.leaves ⊆ U := fun x hx => hU (Finset.mem_union_left _ hx)
      have hrU : r.leaves ⊆ U := fun x hx => hU (Finset.mem_union_right _ hx)
      simp only [blsGo, blsWithin, blsGo_fst, markedCount_eq_card S l hl,
        markedCount_eq_card S r hr, blsGo_snd S U l hl hlU, blsGo_snd S U r hr hrU,
        separates_iff_card hlU, separates_iff_card hrU]

/-- **The post-order algorithm computes the rooted Branch Length Score** on trees with
distinct leaf labels. -/
private theorem rootedBlsAlg_eq_rootedBls (S : Finset L) {t : Tree L} (ht : t.WellLabeled) :
    rootedBlsAlg S t = rootedBls S t := by
  rw [rootedBlsAlg, markedCount_eq_card S t ht, rootedBls,
    blsGo_snd S t.leaves t ht subset_rfl]

private theorem blsWithin_mono (U : Finset L) {S S' : Finset L} (h : S ⊆ S') :
    ∀ t : Tree L, t.NonnegLengths → blsWithin U S t ≤ blsWithin U S' t
  | leaf _, _ => le_rfl
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin]
      have := ite_le_ite ha (separates_mono (U := U) (B := l.leaves) h)
      have := ite_le_ite hb (separates_mono (U := U) (B := r.leaves) h)
      have := blsWithin_mono U h l hl
      have := blsWithin_mono U h r hr
      linarith

/-- **Monotonicity** for the rooted BLS: with nonnegative branch lengths, more conserving
species never lower the BLS. -/
private theorem rootedBls_mono {S S' : Finset L} (h : S ⊆ S') {t : Tree L}
    (ht : t.NonnegLengths) : rootedBls S t ≤ rootedBls S' t :=
  blsWithin_mono _ h t ht

private theorem blsWithin_of_not (U S : Finset L) (hS : ∀ B, ¬ Separates U S B) :
    ∀ t : Tree L, blsWithin U S t = 0
  | leaf _ => rfl
  | node _ l _ r => by
      simp [blsWithin, hS, blsWithin_of_not U S hS l, blsWithin_of_not U S hS r]

/-- The rooted BLS of the empty set is `0`. -/
private theorem rootedBls_empty (t : Tree L) : rootedBls ∅ t = 0 :=
  blsWithin_of_not _ _ (fun B h => by simp [Separates] at h) t

/-- **A single species has rooted BLS `0`**. -/
private theorem rootedBls_singleton (x : L) (t : Tree L) : rootedBls {x} t = 0 := by
  refine blsWithin_of_not _ _ (fun B ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ => ?_) t
  simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_sdiff] at hy hz
  exact hz.2.2 (hz.1 ▸ hy.1 ▸ hy.2)

private theorem blsWithin_leaves (U : Finset L) :
    ∀ t : Tree L, t.WellLabeled → t.leaves ⊆ U → (∀ B, B ⊆ t.leaves → B ≠ t.leaves →
      B.Nonempty → Separates U U B) → blsWithin U U t = t.totalLength
  | leaf _, _, _, _ => rfl
  | node a l b r, ⟨hl, hr, hd⟩, hU, hsep => by
      have hlU : l.leaves ⊆ (node a l b r).leaves := Finset.subset_union_left
      have hrU : r.leaves ⊆ (node a l b r).leaves := Finset.subset_union_right
      have hlne : l.leaves ≠ (node a l b r).leaves := fun he => by
        obtain ⟨y, hy⟩ := leaves_nonempty r
        exact Finset.disjoint_left.1 hd ((he ▸ hrU) hy) hy
      have hrne : r.leaves ≠ (node a l b r).leaves := fun he => by
        obtain ⟨y, hy⟩ := leaves_nonempty l
        exact Finset.disjoint_left.1 hd hy ((he ▸ hlU) hy)
      have hl' : ∀ B, B ⊆ l.leaves → B ≠ l.leaves → B.Nonempty → Separates U U B :=
        fun B hB _ hne => hsep B (hB.trans hlU) (fun he => hlne (Finset.Subset.antisymm
          (hlU) (he ▸ hB))) hne
      have hr' : ∀ B, B ⊆ r.leaves → B ≠ r.leaves → B.Nonempty → Separates U U B :=
        fun B hB _ hne => hsep B (hB.trans hrU) (fun he => hrne (Finset.Subset.antisymm
          (hrU) (he ▸ hB))) hne
      simp only [blsWithin, Tree.totalLength,
        hsep _ hlU hlne (leaves_nonempty l), hsep _ hrU hrne (leaves_nonempty r), ite_true,
        blsWithin_leaves U l hl (hlU.trans hU) hl', blsWithin_leaves U r hr (hrU.trans hU) hr']

/-- **All species give the whole rooted tree**: with distinct leaf labels, the rooted BLS of
the set of all leaves is the total branch length. -/
private theorem rootedBls_leaves {t : Tree L} (ht : t.WellLabeled) :
    rootedBls t.leaves t = t.totalLength := by
  refine blsWithin_leaves t.leaves t ht subset_rfl fun B hB hne hBne => ⟨?_, ?_⟩
  · rwa [Finset.inter_eq_right.2 hB]
  · rw [Finset.inter_eq_right.2 Finset.sdiff_subset, Finset.sdiff_nonempty]
    exact fun h => hne (Finset.Subset.antisymm hB h)

private theorem blsWithin_union (U : Finset L) {S S' : Finset L} (hSS : (S ∩ S').Nonempty)
    (hS : S ⊆ U) :
    ∀ t : Tree L, t.NonnegLengths → blsWithin U (S ∪ S') t ≤ blsWithin U S t + blsWithin U S' t
  | leaf _, _ => by simp [blsWithin]
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin]
      have := ite_or_le ha fun h => separates_union (B := l.leaves) hSS h hS
      have := ite_or_le hb fun h => separates_union (B := r.leaves) hSS h hS
      have := blsWithin_union U hSS hS l hl
      have := blsWithin_union U hSS hS r hr
      linarith

/-- **Subadditivity** for the rooted BLS: for sets of species `S`, `S'` that share a species,
with `S` among the leaves of the tree, the subtree connecting `S ∪ S'` is at most as long as
the two subtrees together. -/
private theorem rootedBls_union_le {S S' : Finset L} {t : Tree L} (hSS : (S ∩ S').Nonempty)
    (hS : S ⊆ t.leaves) (ht : t.NonnegLengths) :
    rootedBls (S ∪ S') t ≤ rootedBls S t + rootedBls S' t :=
  blsWithin_union _ hSS hS t ht

private theorem blsWithin_nonneg (U S : Finset L) :
    ∀ t : Tree L, t.NonnegLengths → 0 ≤ blsWithin U S t
  | leaf _, _ => le_rfl
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin]
      have := blsWithin_nonneg U S l hl
      have := blsWithin_nonneg U S r hr
      split_ifs <;> linarith

private theorem blsWithin_le_totalLength (U S : Finset L) :
    ∀ t : Tree L, t.NonnegLengths → blsWithin U S t ≤ t.totalLength
  | leaf _, _ => le_rfl
  | node _ l _ r, ⟨ha, hb, hl, hr⟩ => by
      simp only [blsWithin, Tree.totalLength]
      have := blsWithin_le_totalLength U S l hl
      have := blsWithin_le_totalLength U S r hr
      split_ifs <;> linarith

/-- The rooted BLS is nonnegative for nonnegative branch lengths. -/
private theorem rootedBls_nonneg (S : Finset L) {t : Tree L} (ht : t.NonnegLengths) :
    0 ≤ rootedBls S t :=
  blsWithin_nonneg _ _ t ht

/-- The rooted BLS is at most the total branch length. -/
private theorem rootedBls_le_totalLength (S : Finset L) {t : Tree L} (ht : t.NonnegLengths) :
    rootedBls S t ≤ t.totalLength :=
  blsWithin_le_totalLength _ _ t ht

/-- The normalized rooted BLS is nonnegative. -/
private theorem rootedBlsFrac_nonneg (S : Finset L) {t : Tree L} (ht : t.NonnegLengths) :
    0 ≤ rootedBlsFrac S t :=
  div_nonneg (rootedBls_nonneg S ht) ((rootedBls_nonneg S ht).trans
    (rootedBls_le_totalLength S ht))

/-- The normalized rooted BLS is at most `1` when the tree has positive total length. -/
private theorem rootedBlsFrac_le_one (S : Finset L) {t : Tree L} (ht : t.NonnegLengths)
    (hpos : 0 < t.totalLength) : rootedBlsFrac S t ≤ 1 :=
  (div_le_one hpos).2 (rootedBls_le_totalLength S ht)

end Cslib.Bioinformatics.Phylogenetics.BranchLengthScore
