/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.RookDecomposition
import all MathlibExt.Combinatorics.Enumerative.Partition.RookDecomposition
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Parity of the max-rook partition count for rook number five

Transpose pairs the non-self-conjugate diagrams. Counting the remaining diagrams gives the
parity of the number of partitions with max-rook number five.
-/

namespace MetaMathlibExt

namespace maxRookPartitionCount_five_mod_two

open Finset YoungDiagram
open maxRookPartitionCount_three_genFun (ferrersBoard_eq hasStaircase le_rook_iff_staircase)

private theorem rook_transpose (μ : YoungDiagram) :
    boardMaxRookNumber μ.transpose.cells = boardMaxRookNumber μ.cells := by
  apply eq_of_forall_le_iff
  intro k
  rw [le_rook_iff_staircase, le_rook_iff_staircase]
  simp only [hasStaircase, mem_transpose, Prod.swap_prod_mk]
  exact ⟨fun h i j hij ↦ h j i (by omega), fun h i j hij ↦ h j i (by omega)⟩

private abbrev Diagram (n : ℕ) :=
  {μ : YoungDiagram // μ.card = n ∧ boardMaxRookNumber μ.cells = 5}

private def diagramEquiv (n : ℕ) :
    Diagram n ≃ {p : Nat.Partition n // partitionMaxRookNumber p = 5} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
    (YoungDiagram.equivPartition.subtypeEquiv (fun μ ↦ by
      change boardMaxRookNumber μ.1.cells = 5 ↔
        partitionMaxRookNumber (μ.1.toPartition μ.2) = 5
      rw [partitionMaxRookNumber, ferrersBoard_eq, ofPartition_toPartition]))

private def transposeDiagram (n : ℕ) (μ : Diagram n) : Diagram n :=
  ⟨μ.1.transpose, by simpa [rook_transpose] using μ.2⟩

private abbrev FixedDiagram (n : ℕ) := (transposeDiagram n).fixedPoints

private theorem fixed_iff {n : ℕ} (μ : Diagram n) :
    μ ∈ FixedDiagram n ↔ μ.1.transpose = μ.1 :=
  ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩

private theorem count_modEq_fixed (n : ℕ) :
    maxRookPartitionCount 5 n ≡ Nat.card (FixedDiagram n) [MOD 2] := by
  classical
  let _ : Fintype (Diagram n) := Fintype.ofEquiv _ (diagramEquiv n).symm
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (f := transposeDiagram n) (by
    funext μ
    change transposeDiagram n (transposeDiagram n μ) = μ
    exact Subtype.ext (transpose_transpose _))
  rw [Nat.card_eq_fintype_card]
  convert h using 1
  unfold maxRookPartitionCount
  rw [← Fintype.card_coe, Fintype.card_congr (diagramEquiv n)]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ ↦ by simp))

private theorem rook_eq_five_iff {μ : YoungDiagram} (hsymm : μ.transpose = μ) :
    boardMaxRookNumber μ.cells = 5 ↔
      (5 ≤ μ.rowLen 0 ∧ 4 ≤ μ.rowLen 1 ∧ 3 ≤ μ.rowLen 2) ∧
        ¬(6 ≤ μ.rowLen 0 ∧ 5 ≤ μ.rowLen 1 ∧ 4 ≤ μ.rowLen 2) := by
  have hswap (i j : ℕ) : (j, i) ∈ μ → (i, j) ∈ μ := by
    intro h
    rw [← hsymm, mem_transpose]
    exact h
  have h (k : ℕ) (hk : k = 5 ∨ k = 6) :
      hasStaircase k μ ↔ k ≤ μ.rowLen 0 ∧ k - 1 ≤ μ.rowLen 1 ∧ k - 2 ≤ μ.rowLen 2 := by
    constructor
    · intro h
      have h0 := mem_iff_lt_rowLen.mp (h 0 (k - 1) (by omega))
      have h1 := mem_iff_lt_rowLen.mp (h 1 (k - 2) (by omega))
      have h2 := mem_iff_lt_rowLen.mp (h 2 (k - 3) (by omega))
      omega
    · rintro ⟨h0, h1, h2⟩ i j hij
      have hsmall (a b : ℕ) (hab : a ≤ b) (hsum : a + b + 1 = k) : (a, b) ∈ μ := by
        apply mem_iff_lt_rowLen.mpr
        have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
        rcases ha with rfl | rfl | rfl <;> omega
      exact if hij' : i ≤ j then hsmall i j hij' hij
        else hswap i j (hsmall j i (by omega) (by omega))
  rw [show boardMaxRookNumber μ.cells = 5 ↔
    5 ≤ boardMaxRookNumber μ.cells ∧ ¬6 ≤ boardMaxRookNumber μ.cells by omega]
  rw [le_rook_iff_staircase, le_rook_iff_staircase, h 5 (Or.inl rfl), h 6 (Or.inr rfl)]

-- The entries of the list are the excesses of the first rows over the Durfee square.
private def topRows (l : List ℕ) (hl : l.SortedGE) : YoungDiagram :=
  ofRowLens (l.map (l.length + ·)) (by
    rw [List.sortedGE_iff_getElem_ge_getElem_of_le]
    intro i j hi hj hij
    simpa using Nat.add_le_add_left (hl.getElem_ge_getElem_of_le
      (hi := by simpa using hi) (hj := by simpa using hj) hij) l.length)

private def shape (l : List ℕ) (hl : l.SortedGE) : YoungDiagram :=
  topRows l hl ⊔ (topRows l hl).transpose

private theorem mem_topRows {l : List ℕ} {hl : l.SortedGE} {i j : ℕ} :
    (i, j) ∈ topRows l hl ↔ i < l.length ∧ j < l.length + l.getD i 0 := by
  by_cases hi : i < l.length
  · simp [topRows, mem_ofRowLens, hi]
  · simp [topRows, mem_ofRowLens, hi]

private theorem mem_shape {l : List ℕ} {hl : l.SortedGE} {i j : ℕ} :
    (i, j) ∈ shape l hl ↔
      (i < l.length ∧ j < l.length + l.getD i 0) ∨
        (j < l.length ∧ i < l.length + l.getD j 0) := by
  simp only [shape, mem_sup, mem_transpose, Prod.swap_prod_mk, mem_topRows]

private theorem shape_transpose (l : List ℕ) (hl : l.SortedGE) :
    (shape l hl).transpose = shape l hl := by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_transpose, Prod.swap_prod_mk, mem_shape, or_comm]

private theorem rowLen_shape {l : List ℕ} {hl : l.SortedGE} {i : ℕ} (hi : i < l.length) :
    (shape l hl).rowLen i = l.length + l.getD i 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← mem_iff_lt_rowLen, mem_shape]
  omega

private theorem exists_shape {μ : YoungDiagram} (hsymm : μ.transpose = μ)
    (d : ℕ) (hcore : ∀ i < d, d ≤ μ.rowLen i) (hmiss : (d, d) ∉ μ) :
    ∃ (l : List ℕ) (hl : l.SortedGE), l.length = d ∧ shape l hl = μ := by
  let l := List.ofFn fun i : Fin d ↦ μ.rowLen i - d
  have hlen : l.length = d := List.length_ofFn
  have hl : l.SortedGE := by
    rw [List.sortedGE_iff_getElem_ge_getElem_of_le]
    intro i j hi hj hij
    simpa only [l, List.getElem_ofFn] using
      Nat.sub_le_sub_right (μ.rowLen_anti j i hij) d
  have hrow {i : ℕ} (hi : i < d) : l.length + l.getD i 0 = μ.rowLen i := by
    have he : l.getD i 0 = μ.rowLen i - d := by
      rw [List.getD_eq_getElem _ _ (by rwa [hlen])]
      simp only [l, List.getElem_ofFn]
    rw [he, hlen]
    have := hcore i hi
    omega
  have hswap (i j : ℕ) : (j, i) ∈ μ ↔ (i, j) ∈ μ := by
    conv_rhs => rw [← hsymm, mem_transpose, Prod.swap_prod_mk]
  refine ⟨l, hl, hlen, ?_⟩
  ext ⟨i, j⟩
  simp only [mem_cells, mem_shape, hlen]
  constructor
  · rintro (⟨hi, hj⟩ | ⟨hj, hi⟩)
    · apply mem_iff_lt_rowLen.mpr
      rwa [← hrow hi, hlen]
    · apply (hswap i j).mp
      apply mem_iff_lt_rowLen.mpr
      rwa [← hrow hj, hlen]
  · intro h
    by_cases hi : i < d
    · exact Or.inl ⟨hi, by rw [← hlen, hrow hi]; exact mem_iff_lt_rowLen.mp h⟩
    · have hj : j < d := by
        by_contra! hj
        exact hmiss (μ.up_left_mem (by omega) hj h)
      exact Or.inr ⟨hj, by
        rw [← hlen, hrow hj]
        exact mem_iff_lt_rowLen.mp ((hswap i j).mpr h)⟩

private theorem card_topRows (l : List ℕ) (hl : l.SortedGE) :
    (topRows l hl).card = l.length * l.length + l.sum := by
  rw [← sum_rowLens_eq_card, topRows, rowLens_ofRowLens_eq_self]
  · have hsum (xs : List ℕ) (d : ℕ) : (xs.map (d + ·)).sum = xs.length * d + xs.sum := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
        omega
    exact hsum l l.length
  · simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    have := List.length_pos_of_mem hx
    omega

private theorem card_shape (l : List ℕ) (hl : l.SortedGE) :
    (shape l hl).card = l.length * l.length + 2 * l.sum := by
  have hi : (topRows l hl ⊓ (topRows l hl).transpose).cells =
      range l.length ×ˢ range l.length := by
    ext ⟨i, j⟩
    simp only [mem_cells, mem_inf, mem_transpose, Prod.swap_prod_mk, mem_topRows, mem_product,
      mem_range]
    omega
  have h := card_union_add_card_inter (topRows l hl).cells ((topRows l hl).transpose.cells)
  rw [← cells_sup, ← cells_inf, hi, card_product, card_range] at h
  change (shape l hl).card + l.length * l.length =
    (topRows l hl).card + (topRows l hl).transpose.card at h
  rw [card_transpose, card_topRows] at h
  omega

private theorem shape_congr {l l' : List ℕ} {hl : l.SortedGE} {hl' : l'.SortedGE}
    (h : l = l') : shape l hl = shape l' hl' := by
  subst l'
  rfl

private theorem shape_injective {l l' : List ℕ} {hl : l.SortedGE} {hl' : l'.SortedGE}
    (hlen : l.length = l'.length) (hshape : shape l hl = shape l' hl') : l = l' := by
  apply List.ext_getElem hlen
  intro i hi hi'
  have h := congrArg (fun μ : YoungDiagram ↦ μ.rowLen i) hshape
  simp only [rowLen_shape hi, rowLen_shape hi', hlen,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at h
  omega

private theorem rook_shape_three (a b c : ℕ) (hl : [a, b, c].SortedGE) :
    boardMaxRookNumber (shape [a, b, c] hl).cells = 5 ↔
      2 ≤ a ∧ 1 ≤ b ∧ ¬(3 ≤ a ∧ 2 ≤ b ∧ 1 ≤ c) := by
  rw [rook_eq_five_iff (shape_transpose _ _),
    rowLen_shape (show 0 < [a, b, c].length by simp),
    rowLen_shape (show 1 < [a, b, c].length by simp),
    rowLen_shape (show 2 < [a, b, c].length by simp)]
  simp only [List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
  omega

private theorem rook_shape_four (a b c d : ℕ) (hl : [a, b, c, d].SortedGE) :
    boardMaxRookNumber (shape [a, b, c, d] hl).cells = 5 ↔
      1 ≤ a ∧ ¬(2 ≤ a ∧ 1 ≤ b) := by
  rw [rook_eq_five_iff (shape_transpose _ _),
    rowLen_shape (show 0 < [a, b, c, d].length by simp),
    rowLen_shape (show 1 < [a, b, c, d].length by simp),
    rowLen_shape (show 2 < [a, b, c, d].length by simp)]
  simp only [List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
  omega

private theorem exists_rankFive_shape {μ : YoungDiagram} (hsymm : μ.transpose = μ)
    (hrook : boardMaxRookNumber μ.cells = 5) (hcard : 25 < μ.card) :
    ∃ (l : List ℕ) (hl : l.SortedGE), (l.length = 3 ∨ l.length = 4) ∧ shape l hl = μ := by
  obtain ⟨h₅, h₆⟩ := (rook_eq_five_iff hsymm).mp hrook
  have hmiss : (4, 4) ∉ μ := by
    intro h
    have hr : 5 ≤ μ.rowLen 4 := mem_iff_lt_rowLen.mp h
    have hw : μ.rowLen 0 ≤ 5 := by
      have h1 := μ.rowLen_anti 1 4 (by decide)
      have h2 := μ.rowLen_anti 2 4 (by decide)
      omega
    have hsub : μ.cells ⊆ range 5 ×ˢ range 5 := by
      rintro ⟨i, j⟩ hc
      have hm := (mem_cells _).mp hc
      have hm' : (j, i) ∈ μ := by
        rw [← hsymm, mem_transpose]
        exact hm
      have hj := (mem_iff_lt_rowLen.mp hm).trans_le (μ.rowLen_anti 0 i (Nat.zero_le i))
      have hi := (mem_iff_lt_rowLen.mp hm').trans_le (μ.rowLen_anti 0 j (Nat.zero_le j))
      exact mem_product.mpr ⟨mem_range.mpr (hi.trans_le hw), mem_range.mpr (hj.trans_le hw)⟩
    have hle := card_le_card hsub
    simp only [card_product, card_range] at hle
    exact (not_le_of_gt hcard) hle
  by_cases hcore : (3, 3) ∈ μ
  · obtain ⟨l, hl, hlen, heq⟩ := exists_shape hsymm 4 (fun i hi ↦
      (mem_iff_lt_rowLen.mp hcore).trans_le (μ.rowLen_anti i 3 (by omega))) hmiss
    exact ⟨l, hl, Or.inr hlen, heq⟩
  · obtain ⟨l, hl, hlen, heq⟩ := exists_shape hsymm 3 (fun i hi ↦
      h₅.2.2.trans (μ.rowLen_anti i 2 (by omega))) hcore
    exact ⟨l, hl, Or.inl hlen, heq⟩

private def mkFixed (l : List ℕ) (hl : l.SortedGE) {n : ℕ}
    (hsize : l.length * l.length + 2 * l.sum = n)
    (hrook : boardMaxRookNumber (shape l hl).cells = 5) : FixedDiagram n :=
  ⟨⟨shape l hl, (card_shape l hl).trans hsize, hrook⟩,
    (fixed_iff _).mpr (shape_transpose _ _)⟩

-- For size 9 + 2s, the third excess is either zero, or the last two excesses are both one.
private def oddProfile (s : ℕ) : Fin (s / 2) ⊕ Unit → List ℕ
  | .inl i => [s - (i.val + 1), i.val + 1, 0]
  | .inr _ => [s - 2, 1, 1]

private theorem oddProfile_length (s : ℕ) (x : Fin (s / 2) ⊕ Unit) :
    (oddProfile s x).length = 3 := by
  cases x <;> rfl

private theorem oddProfile_sorted {s : ℕ} (hs : 9 ≤ s) (x : Fin (s / 2) ⊕ Unit) :
    (oddProfile s x).SortedGE := by
  cases x with
  | inl i =>
    have := i.isLt
    simp [oddProfile, List.sortedGE_iff_pairwise]
    omega
  | inr u =>
    simp [oddProfile, List.sortedGE_iff_pairwise]
    omega

private def oddDiagram (s : ℕ) (hs : 9 ≤ s) (x : Fin (s / 2) ⊕ Unit) :
    FixedDiagram (9 + 2 * s) := by
  refine mkFixed (oddProfile s x) (oddProfile_sorted hs x) ?_ ?_
  · cases x with
    | inl i =>
      have := i.isLt
      dsimp [oddProfile]
      omega
    | inr u =>
      dsimp [oddProfile]
      omega
  · cases x with
    | inl i =>
      have := i.isLt
      exact (rook_shape_three _ _ _ _).mpr (by omega)
    | inr u =>
      exact (rook_shape_three _ _ _ _).mpr (by omega)

private theorem oddDiagram_bijective (s : ℕ) (hs : 9 ≤ s) :
    Function.Bijective (oddDiagram s hs) := by
  constructor
  · intro x y heq
    have h := shape_injective ((oddProfile_length s x).trans (oddProfile_length s y).symm)
      (congrArg (fun z : FixedDiagram (9 + 2 * s) ↦ z.1.1) heq)
    cases x <;> cases y <;> simp [oddProfile, Fin.ext_iff] at h ⊢
    tauto
  · intro z
    obtain ⟨l, hl, hlen, heq⟩ := exists_rankFive_shape ((fixed_iff _).mp z.2) z.1.2.2
      (by rw [z.1.2.1]; omega)
    have hsize := (card_shape l hl).symm.trans (congrArg YoungDiagram.card heq |>.trans z.1.2.1)
    have hlen' : l.length = 3 := by
      rcases hlen with h | h
      · exact h
      · rw [h] at hsize
        omega
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen'
    have hrook := (rook_shape_three a b c hl).mp (heq ▸ z.1.2.2)
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hsize
    have hsorted := hl.pairwise
    simp at hsorted
    have hsum : a + b + c = s := by omega
    by_cases hc : c = 0
    · have hi : b - 1 < s / 2 := by omega
      refine ⟨.inl ⟨b - 1, hi⟩, Subtype.ext (Subtype.ext ?_)⟩
      have hp : oddProfile s (.inl ⟨b - 1, hi⟩) = [a, b, c] := by
        simp only [oddProfile, List.cons.injEq, and_true]
        omega
      exact (shape_congr (hl := oddProfile_sorted hs _) (hl' := hl) hp).trans heq
    · have hb : b = 1 := by omega
      have hc' : c = 1 := by omega
      refine ⟨.inr (), Subtype.ext (Subtype.ext ?_)⟩
      have hp : oddProfile s (.inr ()) = [a, b, c] := by
        simp only [oddProfile, List.cons.injEq, and_true]
        omega
      exact (shape_congr (hl := oddProfile_sorted hs _) (hl' := hl) hp).trans heq

private theorem card_odd (s : ℕ) (hs : 9 ≤ s) :
    Nat.card (FixedDiagram (9 + 2 * s)) = s / 2 + 1 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (oddDiagram_bijective s hs)),
    Nat.card_sum, Nat.card_fin, Nat.card_unique]

-- For size 16 + 2s, the only nonzero excess is the first.
private def evenDiagram (s : ℕ) (hs : 5 ≤ s) : FixedDiagram (16 + 2 * s) :=
  mkFixed [s, 0, 0, 0] (by simp [List.sortedGE_iff_pairwise]) (by simp)
    ((rook_shape_four _ _ _ _ _).mpr (by omega))

private theorem card_even (s : ℕ) (hs : 5 ≤ s) :
    Nat.card (FixedDiagram (16 + 2 * s)) = 1 := by
  let _ : Nonempty (FixedDiagram (16 + 2 * s)) := ⟨evenDiagram s hs⟩
  let _ : Subsingleton (FixedDiagram (16 + 2 * s)) := by
    apply subsingleton_of_forall_eq (evenDiagram s hs)
    intro z
    obtain ⟨l, hl, hlen, heq⟩ := exists_rankFive_shape ((fixed_iff _).mp z.2) z.1.2.2
      (by rw [z.1.2.1]; omega)
    have hsize := (card_shape l hl).symm.trans (congrArg YoungDiagram.card heq |>.trans z.1.2.1)
    have hlen' : l.length = 4 := by
      rcases hlen with h | h
      · rw [h] at hsize
        omega
      · exact h
    obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlen'
    have hrook := (rook_shape_four a b c d hl).mp (heq ▸ z.1.2.2)
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hsize
    have hsorted := hl.pairwise
    simp at hsorted
    obtain ⟨rfl, rfl, rfl, rfl⟩ : a = s ∧ b = 0 ∧ c = 0 ∧ d = 0 := by omega
    exact Subtype.ext (Subtype.ext heq.symm)
  exact Nat.card_unique

end maxRookPartitionCount_five_mod_two

/-- **Parity of the number of partitions with max-rook number 5.** Let $R_5(n)$ be the number of
partitions of $n$ with max-rook number $5$. For every natural number $n > 25$, $R_5(n)$ is even if
$n \equiv 5 \pmod 8$ or $n \equiv 7 \pmod 8$, and odd otherwise.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 13
(`jis-2026-26.2.6-thm-13`). -/
public theorem maxRookPartitionCount_five_mod_two (n : ℕ) (hn : 25 < n) :
    maxRookPartitionCount 5 n % 2 = if n % 8 = 5 ∨ n % 8 = 7 then 0 else 1 := by
  have h := maxRookPartitionCount_five_mod_two.count_modEq_fixed n
  change maxRookPartitionCount 5 n % 2 = _ % 2 at h
  rw [h]
  by_cases heven : n % 2 = 0
  · have hn' : n = 16 + 2 * ((n - 16) / 2) := by omega
    have hc := maxRookPartitionCount_five_mod_two.card_even ((n - 16) / 2) (by omega)
    rw [← hn'] at hc
    rw [hc]
    split <;> omega
  · have hn' : n = 9 + 2 * ((n - 9) / 2) := by omega
    have hc := maxRookPartitionCount_five_mod_two.card_odd ((n - 9) / 2) (by omega)
    rw [← hn'] at hc
    rw [hc, Nat.div_div_eq_div_mul]
    split <;> omega

end MetaMathlibExt
