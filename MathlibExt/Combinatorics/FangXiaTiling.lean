/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/FangXiaTiling.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `fang_xia_tiling_partition_transitive`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these
portions except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the
License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the License for the specific language governing permissions
and limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS placed the definitions, structures
and theorem statement in the present namespace and converted the benchmark theorem to a
Batteries wanted declaration. They moved here with unchanged names, statements and docstrings
when the theorem was proved. The proof is original to this file.
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fang–Xia: tiling of the symmetric group by transpositions

If `T_n = {1} ∪ {all transpositions}` and `(T_n, Y)` is a tiling of the
symmetric group `S_n` (every element of `S_n` has a unique factorisation
`x · y` with `x ∈ T_n`, `y ∈ Y`), then every integer partition `λ` of
`n` whose Young-diagram content sum is nonnegative forces `Y` to be
**λ-transitive** in the Martin–Sagan sense: every pair of ordered set
partitions of shape `λ` is connected by exactly a fixed positive number
of permutations in `Y`. Fang–Xia, *Tiling the symmetric group by
transpositions*, Bull. London Math. Soc. **58**(5) (2026); DOI
`10.1112/blms.70366`; arXiv:2506.00360.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.FangXiaTilingWanted
namespace Combinatorics
namespace FangXiaTilingProblem

open scoped BigOperators

set_option linter.dupNamespace false in
/-- **Tiling of a group by two subsets.** For subsets $X$ and $Y$ of a group $G$, the pair
$(X, Y)$ is a tiling (or factorisation) of $G$ if every $g \in G$ can be written as $g = xy$
with $x \in X$ and $y \in Y$ for exactly one pair $(x, y)$. -/
def IsTiling {G : Type*} [Group G] (X Y : Set G) : Prop :=
  ∀ g : G, ∃! p : X × Y, (p.1 : G) * (p.2 : G) = g

set_option linter.dupNamespace false in
/-- **The identity and the transpositions.** $T_n$ is the set of permutations of
$\{0, \dots, n-1\}$ consisting of the identity and all transpositions $(i\ j)$ with $i \ne j$. -/
def transpositionsWithOne (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {σ | σ = 1 ∨ ∃ i j : Fin n, i ≠ j ∧ σ = Equiv.swap i j}

set_option linter.dupNamespace false in
/-- **Integer partition as a list of row lengths.** A partition of $n$ is encoded as a list
$(\lambda_0, \lambda_1, \dots, \lambda_{k-1})$ of positive integers with
$\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{k-1}$ and $\lambda_0 + \dots + \lambda_{k-1} = n$;
the $\lambda_i$ are its row lengths. -/
structure PartitionShape (n : ℕ) where
  parts : List ℕ
  sorted : parts.Pairwise (· ≥ ·)
  positive : ∀ a ∈ parts, 0 < a
  sum_eq : parts.sum = n

namespace PartitionShape

set_option linter.dupNamespace false in
/-- **Shifted row-length sum.** For a natural number $i$ and a list of natural numbers
$a_0, \dots, a_{k-1}$, this is the integer $\sum_{j=0}^{k-1} a_j\,(a_j - 2(i + j) - 1)$; the
empty list gives $0$.

With $i = 0$ and the row lengths of a partition, this is twice the content sum of the partition. -/
def contentSumAux : ℕ → List ℕ → ℤ
  | _, [] => 0
  | i, a :: as => (a : ℤ) * ((a : ℤ) - 2 * (i : ℤ) - 1) + contentSumAux (i + 1) as

set_option linter.dupNamespace false in
/-- **Twice the content sum of a partition.** For a partition $\lambda$ of $n$ with row lengths
$\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{k-1}$, this is the integer
$\sum_{i=0}^{k-1} \lambda_i\,(\lambda_i - 2i - 1)$.

This is twice the content sum $\sum_{(i,j) \in \lambda} (j - i)$ of the Young diagram of
$\lambda$ (rows $i$ and columns $j$ counted from $0$), so it is nonnegative exactly when the
content sum is. It is the row-length formula from the remark after Theorem 1.4 of Fang–Xia,
whose one-indexed terms are $\lambda_i\,(\lambda_i - 2i + 1)$. -/
def contentSum {n : ℕ} (lam : PartitionShape n) : ℤ :=
  contentSumAux 0 lam.parts

end PartitionShape

set_option linter.dupNamespace false in
/-- **Ordered set partition of shape λ.** Let $\lambda$ be a partition of $n$ with row lengths
$\lambda_0 \ge \dots \ge \lambda_{k-1}$. An ordered set partition of $\{0, \dots, n-1\}$ of shape
$\lambda$ is a sequence $(B_0, \dots, B_{k-1})$ of pairwise disjoint subsets of
$\{0, \dots, n-1\}$ whose union is $\{0, \dots, n-1\}$ and with $|B_i| = \lambda_i$ for every
$i$. -/
structure OrderedSetPartition {n : ℕ} (lam : PartitionShape n) where
  block : Fin lam.parts.length → Finset (Fin n)
  card_block : ∀ i : Fin lam.parts.length, (block i).card = lam.parts.get i
  pairwise_disjoint :
    Pairwise fun i j : Fin lam.parts.length => Disjoint (block i) (block j)
  union_eq_univ : (Finset.univ.biUnion block) = Finset.univ

set_option linter.dupNamespace false in
/-- **Permutation sending one ordered set partition to another.** Let $\lambda$ be a partition
of $n$ and let $P = (P_0, \dots, P_{k-1})$ and $Q = (Q_0, \dots, Q_{k-1})$ be ordered set
partitions of $\{0, \dots, n-1\}$ of shape $\lambda$. A permutation $\sigma$ of
$\{0, \dots, n-1\}$ sends $P$ to $Q$ if $\sigma(P_i) = Q_i$ for every $i$. -/
def SendsPartition {n : ℕ} (σ : Equiv.Perm (Fin n)) {lam : PartitionShape n}
    (P Q : OrderedSetPartition lam) : Prop :=
  ∀ i : Fin lam.parts.length, (P.block i).image σ = Q.block i

set_option linter.dupNamespace false in
/-- **λ-transitive sets of permutations.** Let $\lambda$ be a partition of $n$ with row lengths
$\lambda_0 \ge \dots \ge \lambda_{k-1}$. A set $Y$ of permutations of $\{0, \dots, n-1\}$ is
$\lambda$-transitive, in the sense of Martin and Sagan, if there is a positive integer $r$ such
that for any two ordered set partitions $P = (P_0, \dots, P_{k-1})$ and
$Q = (Q_0, \dots, Q_{k-1})$ of $\{0, \dots, n-1\}$ of shape $\lambda$, exactly $r$ permutations
$\sigma \in Y$ satisfy $\sigma(P_i) = Q_i$ for every $i$. -/
def IsPartitionTransitive {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    (lam : PartitionShape n) : Prop :=
  ∃ r : ℕ, 0 < r ∧
    ∀ P Q : OrderedSetPartition lam,
      {σ : Equiv.Perm (Fin n) | σ ∈ Y ∧ SendsPartition σ P Q}.ncard = r

open Equiv Finset

private abbrev PermN (n : ℕ) := Equiv.Perm (Fin n)

-- On functions constant under swaps inside a row, the sum over swapping an outside
-- point with that row, including the identity, is a positive operator.
private theorem row_energy {n : ℕ} (f : PermN n → ℤ) (A : Finset (Fin n))
    (b : Fin n)
    (hinv : ∀ x ∈ A, ∀ y ∈ A, ∀ g, f (swap x y * g) = f g) :
    0 ≤ ∑ g, f g * (∑ a ∈ insert b A, f (swap b a * g)) := by
  classical
  let S := insert b A
  let F (g : PermN n) := ∑ a ∈ S, f (swap b a * g)
  have stable (c : Fin n) (hc : c ∈ S) (g : PermN n) : F (swap b c * g) = F g := by
    by_cases hcb : c = b
    · simp [hcb, ← Perm.one_def]
    have hcA : c ∈ A := (mem_insert.mp hc).resolve_left hcb
    have hmap (a : Fin n) (ha : a ∈ S) : swap b c a ∈ S := by
      by_cases hab : a = b
      · simpa [hab] using hc
      by_cases hac : a = c
      · simp [hac, S]
      simpa [swap_apply_of_ne_of_ne hab hac] using ha
    apply sum_equiv (swap b c) (fun a ↦ ⟨hmap a, fun h ↦ by simpa using hmap _ h⟩)
    intro a ha
    by_cases hab : a = b
    · simp [hab, ← Perm.one_def]
    by_cases hac : a = c
    · simp [hac, ← Perm.one_def]
    have haA : a ∈ A := (mem_insert.mp ha).resolve_left hab
    rw [swap_apply_of_ne_of_ne hab hac, ← mul_assoc, mul_swap_eq_swap_mul,
      swap_apply_left, swap_apply_of_ne_of_ne hcb (Ne.symm hac), mul_assoc]
    exact hinv a haA c hcA _
  let E := ∑ g, f g * F g
  have hE (a : Fin n) (ha : a ∈ S) : (∑ g, f (swap b a * g) * F g) = E := by
    simpa only [Equiv.coe_mulLeft, stable a ha] using
      Equiv.sum_comp (Equiv.mulLeft (swap b a)) (fun g ↦ f g * F g)
  have hsq : ∑ g, F g * F g = (S.card : ℤ) * E := by
    calc
      _ = ∑ g, ∑ a ∈ S, f (swap b a * g) * F g :=
        sum_congr rfl fun g _ ↦ (sum_mul ..)
      _ = ∑ a ∈ S, ∑ g, f (swap b a * g) * F g := sum_comm
      _ = _ := by rw [sum_congr rfl hE]; simp
  have hpos : 0 < (S.card : ℤ) := by
    exact_mod_cast card_pos.mpr ⟨b, mem_insert_self ..⟩
  have hnonneg : 0 ≤ (S.card : ℤ) * E :=
    hsq ▸ sum_nonneg fun g _ ↦ mul_self_nonneg (F g)
  exact nonneg_of_mul_nonneg_right hnonneg hpos

-- Count ordered pairs above each swap. The identity has n preimages and each
-- proper transposition has two.
open Classical in
private theorem sum_swaps {n : ℕ} (v : PermN n → ℤ) :
    (∑ a, ∑ b, v (swap a b)) =
      (n : ℤ) * v 1 + 2 * ((∑ t : transpositionsWithOne n, v t) - v 1) := by
  classical
  let T := (transpositionsWithOne n).toFinset
  let s (p : Fin n × Fin n) := swap p.1 p.2
  have h1 : 1 ∈ T := Set.mem_toFinset.mpr (Or.inl rfl)
  have hs (p : Fin n × Fin n) (_ : p ∈ univ) : s p ∈ T := by
    apply Set.mem_toFinset.mpr
    by_cases he : p.1 = p.2
    · exact Or.inl (swap_eq_one_iff.mpr he)
    · exact Or.inr ⟨_, _, he, rfl⟩
  have diag : univ.filter (fun p ↦ s p = 1) = (univ : Finset (Fin n)).diag := by
    ext p
    simp [s, mem_diag]
  have fiber (t) (ht : t ∈ T.erase 1) :
      (univ.filter fun p ↦ s p = t).card = 2 := by
    obtain ⟨hne, ht'⟩ := mem_erase.mp ht
    obtain h | ⟨a, b, hab, rfl⟩ := Set.mem_toFinset.mp ht'
    · exact (hne h).elim
    have H : (univ.filter fun p ↦ s p = swap a b) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq, s]
      constructor
      · intro he
        have hm : swap x y a ≠ a := by simpa [he] using hab.symm
        rcases eq_or_eq_of_swap_apply_ne_self hm with rfl | rfl
        · exact Or.inl ⟨rfl, swap_injective_of_left _ he⟩
        · exact Or.inr ⟨swap_injective_of_left _ ((swap_comm ..).trans he), rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rfl
        · exact swap_comm ..
    simp [H, hab]
  have hsum : (∑ t : transpositionsWithOne n, v t) = ∑ t ∈ T, v t :=
    Finset.sum_set_coe _
  rw [hsum, ← sum_erase_add _ _ h1, add_sub_cancel_right, ← Fintype.sum_prod_type',
    ← sum_fiberwise_of_maps_to' hs v, ← sum_erase_add _ _ h1, diag]
  simp only [sum_const, nsmul_eq_mul, Finset.diag, card_map, card_univ, Fintype.card_fin]
  rw [mul_sum]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun t ht ↦ by rw [fiber t ht]; norm_num

-- Sum the row bounds. The two off-diagonal entries for rows i < j each
-- cost at most the length of row j times the squared norm D.
private theorem content_bound (l : List ℕ) (k : ℕ) (D : ℤ)
    (W : Fin l.length → Fin l.length → ℤ)
    (diag : ∀ i, W i i = (l.get i : ℤ) ^ 2 * D)
    (symm : ∀ i j, W i j = W j i)
    (cross : ∀ i j, i < j → -(l.get j : ℤ) * D ≤ W i j) :
    PartitionShape.contentSumAux k l * D + (2 * k + 1 : ℤ) * l.sum * D ≤
      ∑ i, ∑ j, W i j := by
  induction l generalizing k with
  | nil => simp [PartitionShape.contentSumAux]
  | cons a l ih =>
    have ht := ih (k + 1) (fun i j ↦ W i.succ j.succ)
      (fun i ↦ diag i.succ) (fun i j ↦ symm i.succ j.succ)
      (fun i j h ↦ cross i.succ j.succ (Fin.succ_lt_succ_iff.mpr h))
    have hs : (∑ i : Fin l.length, (l.get i : ℤ)) = l.sum := by
      exact_mod_cast (List.sum_ofFn (f := l.get)).symm.trans (congrArg List.sum l.ofFn_get)
    have hc : -(l.sum : ℤ) * D ≤ ∑ j : Fin l.length, W 0 j.succ := by
      rw [← hs, ← sum_neg_distrib, sum_mul]
      exact sum_le_sum fun j _ ↦ cross 0 j.succ (Fin.succ_pos _)
    simp only [List.length_cons] at W ⊢
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp_rw [Fin.sum_univ_succ (fun j ↦ W (Fin.succ _) j), sum_add_distrib,
      show ∀ j : Fin l.length, W j.succ 0 = W 0 j.succ from fun j ↦ symm _ _]
    rw [diag]
    simp only [PartitionShape.contentSumAux, List.sum_cons, Nat.cast_add, Nat.cast_one,
      List.get_cons_zero] at *
    linarith only [ht, hc]

open Classical in
private theorem kernel_trivial {n : ℕ} {lam : PartitionShape n} (P : OrderedSetPartition lam)
    (hlam : 0 ≤ lam.contentSum) (f : PermN n → ℤ)
    (hinv : ∀ i, ∀ x ∈ P.block i, ∀ y ∈ P.block i, ∀ g, f (swap x y * g) = f g)
    (hzero : ∀ g, (∑ t : transpositionsWithOne n, f (g * t)) = 0) :
    ∀ g, f g = 0 := by
  classical
  -- The carrier sum counts each proper swap twice. Regroup its quadratic form
  -- by pairs of rows and compare the result with the content bound.
  let D := ∑ g, f g * f g
  have hD : 0 ≤ D := sum_nonneg fun g _ ↦ mul_self_nonneg _
  let w (a b : Fin n) := ∑ g, f g * f (swap a b * g)
  let W (i j : Fin lam.parts.length) := ∑ a ∈ P.block i, ∑ b ∈ P.block j, w a b
  have hdiag (i) : W i i = (lam.parts.get i : ℤ) ^ 2 * D := by
    have h (a) (ha : a ∈ P.block i) (b) (hb : b ∈ P.block i) : w a b = D := by
      simp [w, D, hinv i a ha b hb]
    simp +contextual [W, h, P.card_block, pow_two, mul_assoc]
  have symm (i j) : W i j = W j i := by
    unfold W
    rw [sum_comm]
    simp only [w, swap_comm]
  have cross (i j) (hij : i < j) : -(lam.parts.get j : ℤ) * D ≤ W i j := by
    have row (b) (hb : b ∈ P.block j) : -D ≤ ∑ a ∈ P.block i, w a b := by
      have hb' : b ∉ P.block i := fun ha ↦ disjoint_left.mp (P.pairwise_disjoint hij.ne) ha hb
      have h := row_energy f (P.block i) b (hinv i)
      simp only [sum_insert hb', swap_self, ← Perm.one_def, one_mul,
        mul_add, sum_add_distrib, mul_sum] at h
      rw [sum_comm (s := univ) (t := P.block i)] at h
      simpa only [w, swap_comm b, neg_le_iff_add_nonneg', D] using h
    unfold W
    rw [sum_comm, ← P.card_block]
    simpa [mul_neg, neg_mul] using sum_le_sum row
  have hbound := content_bound lam.parts 0 D W hdiag symm cross
  have blocks (v : Fin n → ℤ) : (∑ a, v a) = ∑ i, ∑ a ∈ P.block i, v a := by
    calc
      _ = ∑ a ∈ univ.biUnion P.block, v a := by rw [P.union_eq_univ]
      _ = _ := sum_biUnion fun i _ j _ hij ↦ P.pairwise_disjoint hij
  have splitRows : (∑ a, ∑ b, w a b) = ∑ i, ∑ j, W i j := by
    rw [blocks]
    apply sum_congr rfl
    intro i _
    simp_rw [blocks (w _)]
    exact sum_comm
  have point (g : PermN n) : (∑ a, ∑ b, f (swap a b * g)) = (n - 2 : ℤ) * f g := by
    have h := sum_swaps (fun t ↦ f (g * t))
    simp only [mul_one, hzero, mul_swap_eq_swap_mul] at h
    have hmap : (∑ a, ∑ b, f (swap (g a) (g b) * g)) = ∑ a, ∑ b, f (swap a b * g) := by
      calc
        _ = ∑ a : Fin n, ∑ b, f (swap (g a) b * g) :=
          sum_congr rfl fun a _ ↦ Equiv.sum_comp g (fun b ↦ f (swap (g a) b * g))
        _ = _ := Equiv.sum_comp g (fun a ↦ ∑ b, f (swap a b * g))
    rw [hmap] at h
    linarith
  have total : (∑ a, ∑ b, w a b) = (n - 2 : ℤ) * D := by
    calc
      _ = ∑ g, ∑ a, ∑ b, f g * f (swap a b * g) := by
        unfold w
        simp_rw [sum_comm (f := fun b g ↦ f g * f (swap _ b * g))]
        rw [sum_comm]
      _ = _ := by
        rw [show D = ∑ g, f g * f g from rfl, mul_sum]
        apply sum_congr rfl
        intro g _
        simp_rw [← mul_sum, point]
        ring
  rw [← splitRows, total] at hbound
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, lam.sum_eq] at hbound
  have hvan : D = 0 := by
    have h := mul_nonneg hlam hD
    change 0 ≤ PartitionShape.contentSumAux 0 lam.parts * D at h
    linarith
  intro g
  have h := (sum_eq_zero_iff_of_nonneg (fun g _ ↦ mul_self_nonneg (f g))).mp hvan g (mem_univ g)
  exact mul_self_eq_zero.mp h

private theorem sends_left {n : ℕ} {lam : PartitionShape n}
    {A B : OrderedSetPartition lam} {a : PermN n} (ha : SendsPartition a A B)
    (g : PermN n) (P : OrderedSetPartition lam) :
    SendsPartition (a * g) P B ↔ SendsPartition g P A := by
  unfold SendsPartition at ha ⊢
  simp only [Perm.coe_mul, ← image_image, ← ha, image_inj a.injective]

private theorem sends_right {n : ℕ} {lam : PartitionShape n}
    {A B : OrderedSetPartition lam} {a : PermN n} (ha : SendsPartition a A B)
    (g : PermN n) (Q : OrderedSetPartition lam) :
    SendsPartition (g * a) A Q ↔ SendsPartition g B Q := by
  unfold SendsPartition at ha ⊢
  simp only [Perm.coe_mul, ← image_image, ha]

private theorem sends_swap {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (i) (x) (hx : x ∈ P.block i) (y) (hy : y ∈ P.block i) :
    SendsPartition (swap x y) P P := by
  intro j
  apply eq_of_subset_of_card_le _ (by rw [card_image_of_injective _ (swap x y).injective])
  rintro z hz
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hz
  by_cases hij : i = j
  · subst j
    simp only [swap_apply_def]
    split_ifs <;> assumption
  have hd := disjoint_left.mp (P.pairwise_disjoint hij)
  rw [swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hu (hd hx)) (ne_of_mem_of_not_mem hu (hd hy))]
  exact hu

-- An ordered partition identifies its underlying point set with the disjoint sum
-- of its blocks. Bijections between corresponding blocks therefore assemble globally.
private noncomputable def flattenBlocks {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) : (Σ i, ↥(P.block i)) ≃ Fin n :=
  Equiv.ofBijective (fun p ↦ p.2.val) <| by
    constructor
    · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ he
      change x = y at he
      subst y
      have hij : i = j := by
        by_contra h
        exact disjoint_left.mp (P.pairwise_disjoint h) hx hy
      subst j
      rfl
    · intro x
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp (P.union_eq_univ ▸ mem_univ x :
        x ∈ univ.biUnion P.block)
      exact ⟨⟨i, x, hi⟩, rfl⟩

private theorem exists_sends {n : ℕ} {lam : PartitionShape n} (P Q : OrderedSetPartition lam) :
    ∃ g, SendsPartition g P Q := by
  let e (i) : ↥(P.block i) ≃ ↥(Q.block i) := Fintype.equivOfCardEq (by
    simp [P.card_block, Q.card_block])
  let g := (flattenBlocks P).symm.trans ((Equiv.sigmaCongrRight e).trans (flattenBlocks Q))
  refine ⟨g, fun i ↦ eq_of_subset_of_card_le ?_ ?_⟩
  · rintro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have he : (flattenBlocks P).symm x = ⟨i, x, hx⟩ := (flattenBlocks P).symm_apply_eq.mpr rfl
    change ((flattenBlocks Q) ((Equiv.sigmaCongrRight e) ((flattenBlocks P).symm x))) ∈ _
    rw [he]
    exact (e i ⟨x, hx⟩).property
  · simp [card_image_of_injective _ g.injective, P.card_block, Q.card_block]

private noncomputable def sendCount {n : ℕ} {lam : PartitionShape n}
    (Y : Set (PermN n)) (P Q : OrderedSetPartition lam) : ℕ :=
  {σ : PermN n | σ ∈ Y ∧ SendsPartition σ P Q}.ncard

open Classical in
private theorem count_as_sum {n : ℕ} {lam : PartitionShape n}
    (Y : Set (PermN n)) (P Q : OrderedSetPartition lam) :
    (sendCount Y P Q : ℤ) = ∑ y : Y, if SendsPartition y.val P Q then 1 else 0 := by
  classical
  rw [sendCount, Set.ncard_eq_toFinset_card, Set.toFinite_toFinset, sum_boole]
  congr 1
  exact card_bij' (fun x hx ↦ ⟨x, (Set.mem_toFinset.mp hx).1⟩) (fun y _ ↦ y.val)
    (fun x hx ↦ mem_filter.mpr ⟨mem_univ _, (Set.mem_toFinset.mp hx).2⟩)
    (fun y hy ↦ Set.mem_toFinset.mpr ⟨y.property, (mem_filter.mp hy).2⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

open Classical in
private theorem tiling_count {n : ℕ} {Y : Set (PermN n)}
    (ht : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (hc : 0 ≤ lam.contentSum) (P Q : OrderedSetPartition lam) :
    (Fintype.card (transpositionsWithOne n) : ℤ) * sendCount Y P Q =
      ∑ g : PermN n, if SendsPartition g P Q then 1 else 0 := by
  classical
  let v (g : PermN n) : ℤ := if SendsPartition g P Q then 1 else 0
  let N := Fintype.card (transpositionsWithOne n)
  -- Center the sending count by its expected value, clearing the denominator N.
  let f (g : PermN n) := (N : ℤ) * (∑ y : Y, v (g * y)) - ∑ u, v u
  have he (g : PermN n) : (∑ t : transpositionsWithOne n, ∑ y : Y, v (g * (t * y))) =
      ∑ u, v u := by
    let e : (transpositionsWithOne n × Y) ≃ PermN n := Equiv.ofBijective
      (fun p ↦ p.1.val * p.2.val) ((Function.bijective_iff_existsUnique _).mpr ht)
    rw [← Fintype.sum_prod_type']
    exact (Equiv.sum_comp e (fun u ↦ v (g * u))).trans (Equiv.sum_comp (Equiv.mulLeft g) v)
  have hzero (g : PermN n) : (∑ t : transpositionsWithOne n, f (g * t)) = 0 := by
    simp only [f, mul_assoc, sum_sub_distrib, ← mul_sum, he, sum_const, nsmul_eq_mul, N,
      card_univ, sub_self]
  have hinv (i) (x) (hx : x ∈ Q.block i) (y) (hy : y ∈ Q.block i) (g) :
      f (swap x y * g) = f g := by
    simp only [f, v, mul_assoc, sends_left (sends_swap Q i x hx y hy)]
  have h := kernel_trivial Q hc f hinv hzero 1
  rw [count_as_sum]
  simpa [f, v, N, sub_eq_zero] using h

/- **Fang–Xia, Theorem 1.4.** A tiling `(T_n, Y)` of `S_n` forces
λ-transitivity of `Y` for every partition `λ` of `n` whose Young-
diagram content sum is nonnegative. -/
set_option linter.dupNamespace false in
/-- **Fang–Xia: tilings by transpositions and λ-transitivity.** Let $S_n$ be the symmetric group
on $\{0, \dots, n-1\}$, let $T_n \subseteq S_n$ consist of the identity and all transpositions,
and let $Y \subseteq S_n$ be such that $(T_n, Y)$ is a tiling of $S_n$: every $g \in S_n$ can be
written as $g = xy$ with $x \in T_n$ and $y \in Y$ for exactly one pair $(x, y)$. Let $\lambda$
be a partition of $n$ with row lengths $\lambda_0 \ge \dots \ge \lambda_{k-1}$ such that
$\sum_{i=0}^{k-1} \lambda_i\,(\lambda_i - 2i - 1) \ge 0$ (equivalently, the content sum of the
Young diagram of $\lambda$ is nonnegative). Then $Y$ is $\lambda$-transitive: there is a
positive integer $r$ such that for any two ordered set partitions $P = (P_0, \dots, P_{k-1})$
and $Q = (Q_0, \dots, Q_{k-1})$ of $\{0, \dots, n-1\}$ with $|P_i| = |Q_i| = \lambda_i$ for
every $i$, exactly $r$ permutations $\sigma \in Y$ satisfy $\sigma(P_i) = Q_i$ for every $i$.

Source: T. Fang and B. Xia, 'Tiling the symmetric group by transpositions', Bull. London Math. Soc.
58(5) (2026); DOI 10.1112/blms.70366; arXiv:2506.00360. The λ-transitivity notion in the statement
is due to Martin–Sagan. Via leanprover/lean-eval@38361be, problem
`fang_xia_tiling_partition_transitive`. -/
public theorem fang_xia_partition_transitive_of_tiling
    {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (_h : IsTiling (transpositionsWithOne n) Y) :
    ∀ lam : PartitionShape n, 0 ≤ lam.contentSum → IsPartitionTransitive Y lam := by
  classical
  intro lam hc
  rcases isEmpty_or_nonempty (OrderedSetPartition lam) with hempty | ⟨⟨R⟩⟩
  · exact ⟨1, by decide, fun P ↦ (hempty.false P).elim⟩
  let mass (P Q : OrderedSetPartition lam) : ℤ :=
    ∑ g : PermN n, if SendsPartition g P Q then 1 else 0
  have same (P Q : OrderedSetPartition lam) : mass P Q = mass R R := by
    obtain ⟨p, hp⟩ := exists_sends R P
    obtain ⟨q, hq⟩ := exists_sends Q R
    let e := (Equiv.mulLeft q).trans (Equiv.mulRight p)
    have he (g : PermN n) : SendsPartition (e g) R R ↔ SendsPartition g P Q :=
      (sends_right hp (q * g) R).trans (sends_left hq g P)
    simpa only [mass, he] using
      (Equiv.sum_comp e (fun g ↦ if SendsPartition g R R then (1 : ℤ) else 0))
  have pos : 0 < mass R R := by
    have hid : SendsPartition 1 R R := fun i ↦ by simp
    apply sum_pos' (fun _ _ ↦ by split <;> decide)
    exact ⟨1, mem_univ _, by simp [hid]⟩
  have hR := tiling_count _h hc R R
  change _ = mass R R at hR
  have hN : 0 < Fintype.card (transpositionsWithOne n) :=
    Fintype.card_pos_iff.mpr ⟨1, Or.inl rfl⟩
  refine ⟨sendCount Y R R, ?_, fun P Q ↦ ?_⟩
  · by_contra! hn
    rw [Nat.eq_zero_of_le_zero hn, Nat.cast_zero, mul_zero] at hR
    omega
  · have hpq := tiling_count _h hc P Q
    change _ = mass P Q at hpq
    rw [same, ← hR] at hpq
    exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hN.ne' :
      (Fintype.card (transpositionsWithOne n) : ℤ) ≠ 0) hpq

end FangXiaTilingProblem
end Combinatorics
end MathlibExt.Combinatorics.FangXiaTilingWanted
