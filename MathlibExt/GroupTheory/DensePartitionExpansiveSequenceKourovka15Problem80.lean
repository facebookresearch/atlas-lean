/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Kourovka Problem 15.80

The countable box product of the additive real group admits a countable dense partition
and has no expansive sequence.
-/

namespace MathlibExt.GroupTheory.DensePartitionExpansiveSequenceKourovka15Problem80Wanted

@[expose] public section

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.80 (I. V. Protasov). UnsolvedMath record
UM-00701168 (`KOU-15.80`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a topological group (`IsTopologicalGroup`, not necessarily Hausdorff). "Every open subset"
means every nonempty open subset, since the empty set meets nothing. "Countably many" is read as a
partition indexed by `ℕ` into pairwise disjoint dense sets, the most restrictive reading of the
hypothesis, so the refutation is the strongest one; such a partition has infinitely many nonempty
cells.
-/

/-- **Expansive sequence.** In a topological space $G$, a sequence $(F_n)_{n \in \mathbb{N}}$ of
finite subsets of $G$ is expansive if the sets $F_n$ are pairwise disjoint and for every nonempty
open set $U \subseteq G$ there is $m \in \mathbb{N}$ such that $F_n$ meets $U$ for all $n > m$. -/
def IsExpansiveSequence {G : Type*} [TopologicalSpace G] (F : ℕ → Finset G) : Prop :=
  Pairwise (fun i j => Disjoint (F i) (F j)) ∧
    ∀ U : Set G, IsOpen U → U.Nonempty → ∃ m : ℕ, ∀ n, m < n → ∃ x ∈ F n, x ∈ U

/-- **Kourovka Problem 15.80: dense partitions and expansive sequences.** Every topological group
$G$ admitting a sequence $(P_i)_{i \in \mathbb{N}}$ of pairwise disjoint dense subsets with union
$G$ has an expansive sequence. -/
def countableDensePartitionHasExpansiveSequence : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∃ P : ℕ → Set G, Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = Set.univ ∧
      ∀ i, Dense (P i)) → ∃ F : ℕ → Finset G, IsExpansiveSequence F

end

open Set TopologicalSpace

/-- Real sequences, written multiplicatively to use the statement's group convention. -/
private abbrev BoxReal := Multiplicative (ℕ → ℝ)

private def box (U : ℕ → Set ℝ) : Set BoxReal :=
  {x | ∀ i, x.toAdd i ∈ U i}

private def openBoxes : Set (Set BoxReal) :=
  {B | ∃ U : ℕ → Set ℝ, (∀ i, IsOpen (U i)) ∧ B = box U}

local instance instBoxRealTopology : TopologicalSpace BoxReal := generateFrom openBoxes

private theorem isTopologicalBasis_openBoxes : IsTopologicalBasis openBoxes where
  exists_subset_inter := by
    rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩ x ⟨hxU, hxV⟩
    refine ⟨box (fun i ↦ U i ∩ V i), ⟨_, fun i ↦ (hU i).inter (hV i), rfl⟩,
      fun i ↦ ⟨hxU i, hxV i⟩, ?_⟩
    intro y hy
    exact ⟨fun i ↦ (hy i).1, fun i ↦ (hy i).2⟩
  sUnion_eq := by
    refine sUnion_eq_univ_iff.2 fun x ↦ ?_
    exact ⟨box (fun _ ↦ univ), ⟨_, fun _ ↦ isOpen_univ, rfl⟩, fun _ ↦ mem_univ _⟩
  eq_generateFrom := rfl

local instance instBoxRealGroupTopology : IsTopologicalGroup BoxReal where
  continuous_mul := isTopologicalBasis_openBoxes.continuous_iff.2 <| by
    rintro _ ⟨U, hU, rfl⟩
    refine isOpen_prod_iff.2 fun x y hxy ↦ ?_
    have coord (i : ℕ) : ∃ V W : Set ℝ, IsOpen V ∧ IsOpen W ∧
        x.toAdd i ∈ V ∧ y.toAdd i ∈ W ∧ V ×ˢ W ⊆ (fun p : ℝ × ℝ ↦ p.1 + p.2) ⁻¹' U i :=
      isOpen_prod_iff.1 ((hU i).preimage (continuous_fst.add continuous_snd)) _ _ (hxy i)
    choose V W hV hW hx hy hVW using coord
    exact ⟨box V, box W, isTopologicalBasis_openBoxes.isOpen ⟨V, hV, rfl⟩,
      isTopologicalBasis_openBoxes.isOpen ⟨W, hW, rfl⟩, hx, hy,
      fun p hp i ↦ hVW i (show (p.1.toAdd i, p.2.toAdd i) ∈ V i ×ˢ W i from
        ⟨hp.1 i, hp.2 i⟩)⟩
  continuous_inv := isTopologicalBasis_openBoxes.continuous_iff.2 <| by
    rintro _ ⟨U, hU, rfl⟩
    exact isTopologicalBasis_openBoxes.isOpen
      ⟨fun i ↦ (fun x : ℝ ↦ -x) ⁻¹' U i, fun i ↦ (hU i).preimage continuous_neg, rfl⟩

private theorem not_dense_of_countable {s : Set BoxReal} (hs : s.Countable) : ¬ Dense s := by
  obtain ⟨f, hf⟩ := countable_iff_exists_subset_range.mp hs
  let U (i : ℕ) : Set ℝ := { (f i).toAdd i }ᶜ
  intro hd
  obtain ⟨x, hxs, hxU⟩ := hd.exists_mem_open
    (isTopologicalBasis_openBoxes.isOpen ⟨U, fun _ ↦ isOpen_compl_singleton, rfl⟩)
    ⟨Multiplicative.ofAdd (fun i ↦ (f i).toAdd i + 1), fun i ↦ by simp [U]⟩
  obtain ⟨i, rfl⟩ := hf hxs
  exact hxU i (mem_singleton _)

private noncomputable def rationalCoset (n : ℕ) : Set ℝ :=
  range (fun q : ℚ ↦ ↑q + (n : ℝ) * √2)

private theorem dense_rationalCoset (n : ℕ) : Dense (rationalCoset n) := by
  have surj : Function.Surjective (fun x : ℝ ↦ x + (n : ℝ) * √2) := fun y ↦
    ⟨y - (n : ℝ) * √2, sub_add_cancel _ _⟩
  exact surj.denseRange.comp Rat.denseRange_cast (continuous_id.add continuous_const)

private theorem pairwise_disjoint_rationalCoset :
    Pairwise (fun i j ↦ Disjoint (rationalCoset i) (rationalCoset j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨p, rfl⟩ ⟨q, hq⟩
  have hne : (i : ℚ) - (j : ℚ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  apply (irrational_sqrt_two.ratCast_mul hne).ne_rat (q - p)
  push_cast
  rw [sub_mul]
  linarith

-- Put all points outside the positive-index cosets into the zeroth cell.
private noncomputable def realPartition : ℕ → Set ℝ
  | 0 => (⋃ i, rationalCoset (i + 1))ᶜ
  | i + 1 => rationalCoset (i + 1)

private theorem pairwise_disjoint_realPartition :
    Pairwise (fun i j ↦ Disjoint (realPartition i) (realPartition j)) := by
  have disjoint_zero (i : ℕ) : Disjoint (realPartition 0) (realPartition (i + 1)) := by
    rw [Set.disjoint_left]
    exact fun x hx hxi ↦ hx (mem_iUnion.2 ⟨i, hxi⟩)
  intro i j hij
  match i, j with
  | 0, 0 => exact (hij rfl).elim
  | 0, j + 1 => exact disjoint_zero j
  | i + 1, 0 => exact (disjoint_zero i).symm
  | i + 1, j + 1 => exact pairwise_disjoint_rationalCoset hij

private theorem iUnion_realPartition : ⋃ i, realPartition i = univ := by
  classical
  apply iUnion_eq_univ_iff.2
  intro x
  by_cases hx : x ∈ ⋃ i, rationalCoset (i + 1)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact ⟨i + 1, hi⟩
  · exact ⟨0, hx⟩

private theorem dense_realPartition (n : ℕ) : Dense (realPartition n) := by
  cases n with
  | zero =>
    refine (dense_rationalCoset 0).mono fun x hx hUnion ↦ ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 hUnion
    exact Set.disjoint_left.mp (pairwise_disjoint_rationalCoset (Nat.succ_ne_zero i).symm) hx hi
  | succ i => exact dense_rationalCoset (i + 1)

private theorem dense_preimage_firstCoord {s : Set ℝ} (hs : Dense s) :
    Dense ((fun x : BoxReal ↦ x.toAdd 0) ⁻¹' s) := by
  apply dense_iff_inter_open.2
  intro U hU ⟨x, hx⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    isTopologicalBasis_openBoxes.exists_subset_of_mem_open hx hU
  obtain ⟨r, hrs, hrV⟩ := hs.exists_mem_open (hV 0) ⟨x.toAdd 0, hxV 0⟩
  let y := Multiplicative.ofAdd (Function.update x.toAdd 0 r)
  refine ⟨y, hVU ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      simpa [y] using hrV
    · simpa [y, Function.update_of_ne hi] using hxV i
  · simpa [y] using hrs

private theorem exists_densePartition :
    ∃ P : ℕ → Set BoxReal, Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = univ ∧ ∀ i, Dense (P i) := by
  let firstCoord (x : BoxReal) := x.toAdd 0
  refine ⟨fun i ↦ firstCoord ⁻¹' realPartition i,
    fun _ _ hij ↦ (pairwise_disjoint_realPartition hij).preimage firstCoord, ?_,
    fun i ↦ dense_preimage_firstCoord (dense_realPartition i)⟩
  rw [← preimage_iUnion, iUnion_realPartition, preimage_univ]

/--
**Kourovka Problem 15.80 has a negative answer.** It is not true that every topological group $G$
admitting a sequence $(P_i)_{i \in \mathbb{N}}$ of pairwise disjoint dense subsets with union $G$
has an expansive sequence, that is, a sequence $(F_n)_{n \in \mathbb{N}}$ of pairwise disjoint
finite subsets of $G$ such that every nonempty open set $U \subseteq G$ meets $F_n$ for all $n$
larger than some $m$.

S. Corson's counterexample: $\prod_{\mathbb{N}} \mathbb{R}$ with the box topology has no countable
dense subset, hence no expansive sequence (the union of one is countable and dense), but its base
of $2^{\aleph_0}$ open sets of size $2^{\aleph_0}$ lets a transfinite induction partition it into
countably many dense subsets.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.80 (I. V. Protasov); resolution: S.
Corson, letter of 19 May 2025, as recorded in the Kourovka Notebook (21st issue), Problem 15.80, G =
∏_ℕ ℝ with the box topology: not separable, hence without expansive sequences, but partitionable
into countably many dense subsets by transfinite induction; the Kourovka Notebook (21st issue)
marks 15.80 solved (answer: Not necessarily), https://arxiv.org/abs/1401.0300v49.
-/
public theorem countableDensePartitionHasExpansiveSequence_refuted :
    ¬ countableDensePartitionHasExpansiveSequence := by
  intro h
  obtain ⟨F, _, hF⟩ := h BoxReal exists_densePartition
  let s : Set BoxReal := ⋃ n, (F n : Set BoxReal)
  have hs : s.Countable := countable_iUnion fun n ↦ (F n).finite_toSet.countable
  apply not_dense_of_countable hs
  refine dense_iff_inter_open.2 fun U hU hne ↦ ?_
  obtain ⟨m, hm⟩ := hF U hU hne
  obtain ⟨x, hxF, hxU⟩ := hm (m + 1) (Nat.lt_succ_self m)
  exact ⟨x, hxU, mem_iUnion.2 ⟨m + 1, hxF⟩⟩

end MathlibExt.GroupTheory.DensePartitionExpansiveSequenceKourovka15Problem80Wanted
