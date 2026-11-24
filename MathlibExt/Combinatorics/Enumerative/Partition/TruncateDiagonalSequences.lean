/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
import all MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
import all MathlibExt.Combinatorics.Enumerative.Partition.ExtremalDiagonalSequences
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Truncating the staircase of a diagonal sequence

Inserting a step into the full staircase preserves the size of the diagonal class
when the first two diagonals after the staircase have the same length.
-/

namespace MetaMathlibExt
namespace card_diagonalClassOf_truncate

open Finset YoungDiagram

-- On diagonal m + t, record the row indices of the occupied cells. Both neighbours
-- of a cell on the preceding diagonal must be occupied whenever they exist.
private structure Layers (m : ℕ) (d : List ℕ) where
  row : ℕ → Finset ℕ
  bound : ∀ {t i}, i ∈ row t → i ≤ m + t
  size : ∀ t, (row t).card = d.getD t 0
  prev : ∀ {t i j}, i ∈ row (t + 1) → j ≤ m + t → j ≤ i → i ≤ j + 1 → j ∈ row t

private theorem layers_ext {m d} {x y : Layers m d} (h : ∀ t, x.row t = y.row t) : x = y := by
  cases x
  cases y
  congr
  exact funext h

private def slice (μ : YoungDiagram) (t : ℕ) : Finset ℕ :=
  (range (t + 1)).filter fun i => (i, t - i) ∈ μ

private theorem mem_slice {μ : YoungDiagram} {t i : ℕ} :
    i ∈ slice μ t ↔ i ≤ t ∧ (i, t - i) ∈ μ := by
  simp [slice]

private theorem card_slice {n : ℕ} (p : Nat.Partition n) (t : ℕ) :
    (slice (ofPartition p) t).card = diagonalSequence p.parts (t + 1) := by
  rw [diagonalSequence_succ_eq_card, Finset.Nat.antidiagonal_eq_map, filter_map, card_map]
  rfl

private def partitionLayers {n d} (p : Nat.Partition n)
    (hp : p ∈ diagonalClassOf n (diagonalOfList d)) : Layers 0 d where
  row := slice (ofPartition p)
  bound hi := by simpa using (mem_slice.mp hi).1
  size t := by
    classical
    exact (card_slice p t).trans (congrFun (mem_filter.mp hp).2 (t + 1))
  prev := by
    intro t i j hi hj hji hij
    obtain ⟨_, hc⟩ := mem_slice.mp hi
    exact mem_slice.mpr ⟨by omega, (ofPartition p).up_left_mem hji (by omega) hc⟩

private def cellsOn {d} (x : Layers 0 d) (t : ℕ) : Finset (ℕ × ℕ) :=
  (x.row t).image fun i => (i, t - i)

private theorem mem_cellsOn {d} {x : Layers 0 d} {t i j} :
    (i, j) ∈ cellsOn x t ↔ i + j = t ∧ i ∈ x.row t := by
  simp only [cellsOn, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    have := x.bound ha
    exact ⟨by omega, ha⟩
  · rintro ⟨rfl, hi⟩
    exact ⟨i, hi, rfl, by omega⟩

private def layerCells {d} (x : Layers 0 d) : Finset (ℕ × ℕ) :=
  (range d.length).biUnion (cellsOn x)

private theorem mem_layerCells {d} {x : Layers 0 d} {i j} :
    (i, j) ∈ layerCells x ↔ i ∈ x.row (i + j) := by
  simp only [layerCells, mem_biUnion, mem_range, mem_cellsOn]
  constructor
  · rintro ⟨_, _, rfl, hi⟩
    exact hi
  · intro hi
    refine ⟨_, ?_, rfl, hi⟩
    by_contra! h
    have := card_pos.mpr ⟨_, hi⟩
    rw [x.size, List.getD_eq_default _ _ h] at this
    omega

private def diagram {d} (x : Layers 0 d) : YoungDiagram where
  cells := layerCells x
  isLowerSet := by
    rintro ⟨u, v⟩ ⟨i, j⟩ ⟨hi, hj⟩
    change (u, v) ∈ layerCells x → (i, j) ∈ layerCells x
    rw [mem_layerCells, mem_layerCells]
    change i ≤ u at hi
    change j ≤ v at hj
    induction u, hi using Nat.le_induction with
    | base =>
      induction v, hj using Nat.le_induction with
      | base => exact id
      | succ v _ ih =>
        exact fun h => ih (x.prev (t := i + v) h (by omega) le_rfl (by omega))
    | succ u _ ih =>
      intro h
      apply ih
      apply x.prev (t := u + v) (i := u + 1) _ (by omega) (by omega) (by omega)
      simpa only [Nat.succ_add] using h

private theorem sum_getD (d : List ℕ) : ∑ t ∈ range d.length, d.getD t 0 = d.sum := by
  induction d with
  | nil => simp
  | cons x d ih => simp only [List.length_cons, sum_range_succ', List.getD_cons_succ, ih,
      List.getD_cons_zero, List.sum_cons, Nat.add_comm]

private theorem card_diagram {d} (x : Layers 0 d) : (diagram x).card = d.sum := by
  change ((range d.length).biUnion (cellsOn x)).card = _
  rw [card_biUnion, ← sum_getD]
  · apply sum_congr rfl
    intro t _
    exact (card_image_of_injective _ fun _ _ h => congrArg Prod.fst h).trans (x.size t)
  · intro t _ u _ htu
    apply disjoint_left.mpr
    rintro ⟨i, j⟩ ht hu
    exact htu ((mem_cellsOn.mp ht).1.symm.trans (mem_cellsOn.mp hu).1)

private theorem slice_diagram {d} (x : Layers 0 d) (t : ℕ) :
    slice (diagram x) t = x.row t := by
  ext i
  rw [mem_slice]
  change (i ≤ t ∧ (i, t - i) ∈ layerCells x) ↔ _
  rw [mem_layerCells]
  constructor
  · rintro ⟨hi, h⟩
    rwa [Nat.add_sub_of_le hi] at h
  · intro h
    have hi := x.bound h
    exact ⟨by omega, by rwa [show i + (t - i) = t by omega]⟩

private def classLayers {n d} (hn : d.sum = n) :
    ↥(diagonalClassOf n (diagonalOfList d)) ≃ Layers 0 d where
  toFun p := partitionLayers p.1 p.2
  invFun x := by
    classical
    let p := (diagram x).toPartition ((card_diagram x).trans hn)
    refine ⟨p, mem_filter.mpr ⟨mem_univ _, funext fun t => ?_⟩⟩
    cases t with
    | zero => simp [diagonalSequence, diagonalOfList]
    | succ t =>
      rw [← card_slice, show ofPartition p = diagram x from ofPartition_toPartition _,
        slice_diagram]
      exact x.size t
  left_inv p := by
    apply Subtype.ext
    apply (equivPartition (n := n)).symm.injective
    apply Subtype.ext
    change ofPartition ((diagram (partitionLayers p.1 p.2)).toPartition
      ((card_diagram _).trans hn)) = ofPartition p.1
    rw [ofPartition_toPartition]
    apply YoungDiagram.ext
    ext ⟨i, j⟩
    change (i, j) ∈ layerCells (partitionLayers p.1 p.2) ↔ _
    rw [mem_layerCells]
    change i ∈ slice (ofPartition p.1) (i + j) ↔ _
    simp [mem_slice]
  right_inv x := by
    apply layers_ext
    intro t
    simpa [partitionLayers] using slice_diagram x t

-- A full diagonal imposes no constraint on the first layer after it.
private def dropFull (m : ℕ) (d : List ℕ) : Layers m ((m + 1) :: d) ≃ Layers (m + 1) d where
  toFun x := {
    row := fun t => x.row (t + 1)
    bound := fun h => by have := x.bound h; omega
    size := fun t => x.size (t + 1)
    prev := fun h hj => x.prev h (by omega) }
  invFun x := {
    row := fun t => Nat.casesOn t (range (m + 1)) x.row
    bound := by
      intro t i hi
      cases t with
      | zero => simpa [Nat.lt_succ_iff] using mem_range.mp hi
      | succ t => have := x.bound hi; omega
    size := by
      intro t
      cases t with
      | zero => exact card_range _
      | succ t => exact x.size t
    prev := by
      intro t i j hi hj hji hij
      cases t with
      | zero => exact mem_range.mpr (by omega)
      | succ t => exact x.prev hi (by omega) hji hij }
  left_inv x := by
    apply layers_ext
    intro t
    cases t with
    | zero =>
      symm
      apply eq_of_subset_of_card_le (fun i hi => mem_range.mpr (by have := x.bound hi; omega))
      rw [card_range, x.size]
      rfl
    | succ t => rfl
  right_inv _ := rfl

private def dropStaircase (m : ℕ) (d : List ℕ) : Layers 0 (List.range' 1 m ++ d) ≃ Layers m d := by
  induction m generalizing d with
  | zero => exact Equiv.refl _
  | succ m ih =>
    simp only [List.range'_concat, one_mul, Nat.one_add, List.append_assoc,
      List.singleton_append]
    exact (ih ((m + 1) :: d)).trans (dropFull m d)

private theorem exists_missing {m d} (x : Layers m d) : ∃ i, i ∉ x.row 0 :=
  ⟨m + 1, fun h => by have := x.bound h; omega⟩

private def gap {m d} (x : Layers m d) := Nat.find (exists_missing x)

private theorem gap_missing {m d} (x : Layers m d) : gap x ∉ x.row 0 :=
  Nat.find_spec (exists_missing x)

private theorem before_gap {m d} {x : Layers m d} {i} (hi : i < gap x) : i ∈ x.row 0 :=
  not_not.mp (Nat.find_min (exists_missing x) hi)

private theorem gap_le_size {m d} (x : Layers m d) : gap x ≤ d.getD 0 0 := by
  have h : range (gap x) ⊆ x.row 0 := fun _ hi => before_gap (mem_range.mp hi)
  simpa only [card_range, x.size] using card_le_card h

private theorem gap_eq {m d} {x : Layers m d} {a : ℕ} (ha : a ∉ x.row 0)
    (h : ∀ i < a, i ∈ x.row 0) : gap x = a := by
  apply le_antisymm (Nat.find_min' (exists_missing x) ha)
  exact le_of_not_gt fun hlt => gap_missing x (h _ hlt)

private theorem missing_later {m d} (x : Layers m d) {a} (ha : a ≤ m) (h : a ∉ x.row 0)
    (t : ℕ) : a ∉ x.row t := by
  induction t with
  | zero => exact h
  | succ t ih => exact fun hi => ih (x.prev hi (by omega) le_rfl (by omega))

-- Insert a blank position at a, or delete that position.
private def skip (a i : ℕ) : ℕ := if i < a then i else i + 1

private def unskip (a i : ℕ) : ℕ := if i < a then i else i - 1

private theorem unskip_skip (a i : ℕ) : unskip a (skip a i) = i := by
  unfold unskip skip
  split_ifs <;> omega

private theorem skip_unskip {a i : ℕ} (hi : i ≠ a) : skip a (unskip a i) = i := by
  unfold unskip skip
  split_ifs <;> omega

private theorem skip_inj (a : ℕ) : Function.Injective (skip a) :=
  Function.LeftInverse.injective (unskip_skip a)

-- Project the second diagonal into the first, towards the first missing cell.
-- Equality of their sizes makes this projection onto. To the right of the gap,
-- an occupied row must therefore be followed by another occupied row.
private theorem gap_succ_missing {m k d} (x : Layers (m + 1) (k :: k :: d)) (hk : k ≤ m) :
    gap x + 1 ∉ x.row 0 := by
  let a := gap x
  have ha : a ≤ k := gap_le_size x
  have hgap : a ∉ x.row 0 := gap_missing x
  have hmiss : a ∉ x.row 1 := missing_later x (by omega) hgap 1
  have proj : (x.row 1).image (unskip a) = x.row 0 := by
    apply eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      have hb := x.bound hi
      unfold unskip
      split <;> apply x.prev (t := 0) hi <;> omega
    · have hinj : Set.InjOn (unskip a) (x.row 1) := by
        intro i hi j hj hij
        have := congrArg (skip a) hij
        have hi' : i ≠ a := fun e => hmiss (e ▸ hi)
        have hj' : j ≠ a := fun e => hmiss (e ▸ hj)
        rwa [skip_unskip hi', skip_unskip hj'] at this
      rw [card_image_of_injOn hinj, x.size, x.size]
      rfl
  intro hnext
  have suffix (j : ℕ) (haj : a + 1 ≤ j) (hj : j ≤ m + 1) : j ∈ x.row 0 := by
    induction j, haj using Nat.le_induction with
    | base => exact hnext
    | succ j hj' ih =>
      obtain ⟨i, hi, he⟩ := mem_image.mp (proj ▸ ih (by omega))
      have hij : i = j + 1 := by unfold unskip at he; split at he <;> omega
      subst i
      exact x.prev (t := 0) hi (by omega) le_rfl (by omega)
  have hsub : (range (m + 2)).erase a ⊆ x.row 0 := by
    intro j hj
    obtain ⟨hne, hj⟩ := mem_erase.mp hj
    have hb := mem_range.mp hj
    rcases lt_or_gt_of_ne hne with h | h
    · exact before_gap h
    · exact suffix j h (by omega)
  have hcard := card_le_card hsub
  rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range, x.size] at hcard
  change m + 2 - 1 ≤ k at hcard
  omega

private def widen {m k d} (hk : k ≤ m) (x : Layers m (k :: k :: d)) :
    Layers (m + 1) (k :: k :: d) where
  row t := (x.row t).image (skip (gap x))
  bound := by
    intro t i hi
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
    have := x.bound hu
    unfold skip
    split <;> omega
  size t := (card_image_of_injective _ (skip_inj _)).trans (x.size t)
  prev := by
    intro t i j hi hj hji hij
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
    have ha : gap x ≤ k := gap_le_size x
    have hne : u ≠ gap x := fun e => missing_later x (by omega) (gap_missing x) _ (e ▸ hu)
    have hjne : j ≠ gap x := by
      unfold skip at hji hij
      split at hji <;> simp_all <;> omega
    refine mem_image.mpr ⟨unskip (gap x) j, ?_, skip_unskip hjne⟩
    apply x.prev hu <;> unfold unskip <;> unfold skip at hji hij <;> split_ifs at * <;> omega

private theorem gap_widen {m k d} (hk : k ≤ m) (x : Layers m (k :: k :: d)) :
    gap (widen hk x) = gap x := by
  apply gap_eq
  · intro h
    obtain ⟨i, _, he⟩ := mem_image.mp h
    unfold skip at he
    split at he <;> omega
  · intro i hi
    exact mem_image.mpr ⟨i, before_gap hi, ite_eq_left hi⟩

private def narrow {m k d} (hk : k ≤ m) (x : Layers (m + 1) (k :: k :: d)) :
    Layers m (k :: k :: d) where
  row t := (x.row t).image (unskip (gap x))
  bound := by
    intro t i hi
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
    have := x.bound hu
    have ha : gap x ≤ k := gap_le_size x
    unfold unskip
    split <;> omega
  size t := by
    rw [card_image_of_injOn, x.size]
    intro i hi j hj hij
    have ha : gap x ≤ k := gap_le_size x
    have hmiss := missing_later x (by omega) (gap_missing x) t
    have hi' : i ≠ gap x := fun e => hmiss (e ▸ hi)
    have hj' : j ≠ gap x := fun e => hmiss (e ▸ hj)
    simpa only [skip_unskip hi', skip_unskip hj'] using congrArg (skip (gap x)) hij
  prev := by
    intro t i j hi hj hji hij
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
    have ha : gap x ≤ k := gap_le_size x
    have hne : u ≠ gap x := fun e => missing_later x (by omega) (gap_missing x) _ (e ▸ hu)
    have hne' : u ≠ gap x + 1 := fun e =>
      missing_later x (by omega) (gap_succ_missing x hk) _ (e ▸ hu)
    refine mem_image.mpr ⟨skip (gap x) j, ?_, unskip_skip _ _⟩
    apply x.prev hu <;> unfold skip <;> unfold unskip at hji hij <;> split_ifs at * <;> omega

private theorem gap_narrow {m k d} (hk : k ≤ m) (x : Layers (m + 1) (k :: k :: d)) :
    gap (narrow hk x) = gap x := by
  apply gap_eq
  · intro h
    obtain ⟨i, hi, he⟩ := mem_image.mp h
    have hne : i ≠ gap x := fun e => gap_missing x (e ▸ hi)
    have hne' : i ≠ gap x + 1 := fun e => gap_succ_missing x hk (e ▸ hi)
    unfold unskip at he
    split at he <;> omega
  · intro i hi
    exact mem_image.mpr ⟨i, before_gap hi, ite_eq_left hi⟩

private def insertStep {m k d} (hk : k ≤ m) : Layers m (k :: k :: d) ≃
    Layers (m + 1) (k :: k :: d) where
  toFun := widen hk
  invFun := narrow hk
  left_inv x := by
    apply layers_ext
    intro t
    change ((x.row t).image _).image (unskip (gap (widen hk x))) = _
    rw [gap_widen, image_image]
    simp [Function.comp_def, unskip_skip]
  right_inv x := by
    apply layers_ext
    intro t
    change ((x.row t).image _).image (skip (gap (narrow hk x))) = _
    rw [gap_narrow, image_image]
    refine (image_congr ?_).trans (image_id (s := x.row t))
    intro i hi
    have ha : gap x ≤ k := gap_le_size x
    exact skip_unskip fun e => missing_later x (by omega) (gap_missing x) _ (e ▸ hi)

open diagonalSequence_max_eq_min_and_multiset (blocks blocks_succ)

private theorem normal_sum (m : ℕ) (s : ℕ → ℕ) :
    (diagonalNormalForm m s).sum = m * (m + 1) / 2 + ∑ j ∈ Icc 1 m, j * s j := by
  have stair : (List.range' 1 m).sum * 2 = m * (m + 1) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range'_concat, List.sum_append, Nat.add_mul, ih]
      simp [Nat.add_mul, Nat.mul_add, Nat.mul_two, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have tail : (blocks m s).sum = ∑ j ∈ Icc 1 m, j * s j := by
    clear stair
    induction m with
    | zero => simp [blocks]
    | succ m ih =>
      rw [blocks_succ, List.sum_append, List.sum_replicate_nat, ih, sum_Icc_succ_top (by omega)]
      ac_rfl
  change (List.range' 1 m ++ blocks m s).sum = _
  rw [List.sum_append, tail, ← stair, Nat.mul_div_cancel _ (by decide)]

private theorem class_card (m : ℕ) (s : ℕ → ℕ) :
    (diagonalClassOf (m * (m + 1) / 2 + ∑ j ∈ Icc 1 m, j * s j)
      (diagonalOfList (diagonalNormalForm m s))).card = Nat.card (Layers m (blocks m s)) := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((classLayers (normal_sum m s)).trans (dropStaircase m (blocks m s)))

end card_diagonalClassOf_truncate

open card_diagonalClassOf_truncate diagonalSequence_max_eq_min_and_multiset in
/-- **Truncating the staircase of a diagonal sequence.** For $m \ge 0$ and a sequence
$s = (s_1, s_2, \dots)$ of natural numbers, let $d(m, s)$ be the sequence
$(1, 2, \dots, m, m^{(s_m)}, (m-1)^{(s_{m-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$, and let $n(m, s) = m(m+1)/2 + \sum_{j=1}^{m} j s_j$. Let
$1 \le k < q$ with $s_k \ge 2$ and $s_j = 0$ for all $k < j \le q$. Then the number of partitions
of $n(q, s)$ with diagonal sequence $d(q, s)$ equals the number of partitions of $n(k, s)$ with
diagonal sequence $d(k, s)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (4). -/
public theorem card_diagonalClassOf_truncate (q k : ℕ) (s : ℕ → ℕ) (hk : 1 ≤ k)
    (hkq : k < q) (hsk : 2 ≤ s k) (hs : ∀ j ∈ Finset.Ioc k q, s j = 0) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (k * (k + 1) / 2 + ∑ j ∈ Finset.Icc 1 k, j * s j)
        (diagonalOfList (diagonalNormalForm k s))).card := by
  rw [class_card, class_card]
  have htail (m : ℕ) (hm : k ≤ m) (hmq : m ≤ q) : blocks m s = blocks k s := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [blocks_succ, hs _ (Finset.mem_Ioc.mpr ⟨by omega, hmq⟩)]
      simpa using ih (by omega)
  obtain ⟨r, hr⟩ : ∃ r, blocks k s = k :: k :: r := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' hsk
    rw [blocks_succ, hc, List.replicate_succ, List.replicate_succ]
    exact ⟨_, rfl⟩
  rw [htail q hkq.le le_rfl, hr]
  have steps (m : ℕ) (hm : k ≤ m) :
      Nat.card (Layers m (k :: k :: r)) = Nat.card (Layers k (k :: k :: r)) := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => exact (Nat.card_congr (insertStep (d := r) hm)).symm.trans ih
  exact steps q hkq.le

end MetaMathlibExt
