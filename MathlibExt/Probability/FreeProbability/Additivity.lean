/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FreeProbability.FreeCumulants
public import MathlibExt.Probability.FreeProbability.Freeness

import Mathlib.Data.List.Chain
import Mathlib.Data.List.Forall2
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.NoncommRing

/-!
# Additivity of free cumulants

In a noncommutative probability space `(A, φ)`, free cumulants linearise free additive convolution:
if `a` and `b` are free then `κₙ(a + b) = κₙ(a) + κₙ(b)` for every `n ≥ 1`, so the R-transform is
additive (Anderson, Guionnet and Zeitouni (manuscript numbering), Lemma 5.3.21 and Corollary
5.3.23).

The proof of `freeCumulant_add_of_areFree` uses the formal moment-series identity
`M(X) = K(X M(X))`, where `K` records the free cumulants with constant term one.
This identifies `K` by requiring
the coefficientwise expectation of the inverse of `K - X x` to be one. For a sum of
free elements, a geometric expansion in the two centered inverses verifies this requirement.

## Source

G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §5.3.2:
Lemma 5.3.21 and Corollary 5.3.23.

Roland Speicher, *Lecture Notes on Free Probability Theory*,
[arXiv:1908.08125](https://arxiv.org/abs/1908.08125), Theorem 3.26 for the moment-series identity.
-/

open Finset NoncrossingPartition PowerSeries
open MathlibExt.Probability.FreeProbability

namespace MathlibExt.Probability.FreeProbabilityWanted.freeCumulant_add_of_areFree

private def firstBlock {n : ℕ} (P : NoncrossingPartition n) : Finset (Fin n) :=
  if h : 0 < n then P.val.part ⟨0, h⟩ else ∅

private theorem firstBlock_succ {n : ℕ} (P : NoncrossingPartition (n + 1)) :
    firstBlock P = P.val.part 0 := dite_eq_left (Nat.succ_pos n)

private theorem mem_firstBlock {n : ℕ} (P : NoncrossingPartition n) (x : Fin n) :
    x ∈ firstBlock P ↔ P.val.part x = P.val.part ⟨0, Nat.zero_lt_of_lt x.isLt⟩ := by
  rw [firstBlock, dite_eq_left (Nat.zero_lt_of_lt x.isLt)]
  exact (P.val.part_eq_iff_mem (part_mem_parts _ _)).symm

private theorem firstBlock_mem_parts {n : ℕ} (h : 0 < n) (P : NoncrossingPartition n) :
    firstBlock P ∈ P.val.parts := by
  rw [firstBlock, dite_eq_left h]
  exact part_mem_parts _ _

private theorem rel_iff_mem {n : ℕ} (P : NoncrossingPartition n) {x y : Fin n} :
    P.val.part x = P.val.part y ↔ y ∈ P.val.part x := by
  exact eq_comm.trans (P.val.part_eq_iff_mem (part_mem_parts P.val x))

private theorem partition_ext {n : ℕ} {P Q : NoncrossingPartition n}
    (h : ∀ x y, P.val.part x = P.val.part y ↔ Q.val.part x = Q.val.part y) : P = Q := by
  apply NoncrossingPartition.ext
  have he (x : Fin n) : P.val.part x = Q.val.part x := by
    ext y
    simpa only [rel_iff_mem] using h x y
  ext B
  exact ⟨fun hB => by
    obtain ⟨x, hx⟩ := P.val.nonempty_of_mem_parts hB
    rw [← P.val.part_eq_of_mem hB hx, he]
    exact part_mem_parts _ _,
    fun hB => by
      obtain ⟨x, hx⟩ := Q.val.nonempty_of_mem_parts hB
      rw [← Q.val.part_eq_of_mem hB hx, ← he]
      exact part_mem_parts _ _⟩

private def labelPartition {n : ℕ} {β : Type*} [DecidableEq β] (f : Fin n → β) : SetPartition n :=
  Finpartition.ofSetoid (Setoid.ker f)

private theorem label_rel {n : ℕ} {β : Type*} [DecidableEq β] (f : Fin n → β) (x y : Fin n) :
    (labelPartition f).part x = (labelPartition f).part y ↔ f x = f y := by
  rw [eq_comm, (labelPartition f).part_eq_iff_mem (part_mem_parts _ _)]
  exact Finpartition.mem_part_ofSetoid_iff_rel

private def pull {n m : ℕ} (P : NoncrossingPartition n) (e : Fin m ↪o Fin n) :
    NoncrossingPartition m :=
  ⟨labelPartition fun x => P.val.part (e x), by
    rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
    simp only [label_rel] at hac hbd
    have hn := (not_congr (label_rel _ a b)).mp hne
    exact P.property ⟨e a, e b, e c, e d, e.strictMono hab, e.strictMono hbc,
      e.strictMono hcd, hac, hbd, hn⟩⟩

private theorem pull_rel {n m : ℕ} (P : NoncrossingPartition n) (e : Fin m ↪o Fin n) (x y : Fin m) :
    (pull P e).val.part x = (pull P e).val.part y ↔ P.val.part (e x) = P.val.part (e y) :=
  label_rel _ x y

-- The middle runs from point 1 up to the cut. The tail begins at the second
-- point of the first block, or is empty when the first block is a singleton.
private def middle {n : ℕ} (i : Fin (n + 1)) : Fin i.val ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (fun x => ⟨x.val + 1, by omega⟩)
    (fun _ _ h => Nat.succ_lt_succ h)

private def tail {n : ℕ} (i : Fin (n + 1)) : Fin (n - i.val) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (fun x => ⟨i.val + 1 + x.val, by omega⟩)
    (fun _ _ h => by exact Nat.add_lt_add_left h _)

private theorem val_middle {n : ℕ} (i : Fin (n + 1)) (x : Fin i.val) :
    (middle i x).val = x.val + 1 := rfl

private theorem val_tail {n : ℕ} (i : Fin (n + 1)) (x : Fin (n - i.val)) :
    (tail i x).val = i.val + 1 + x.val := rfl

private theorem slices {n : ℕ} (i x : Fin (n + 1)) :
    x = 0 ∨ (∃ u, x = middle i u) ∨ ∃ v, x = tail i v := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · have hx' : 0 < x.val := by
      exact Nat.pos_of_ne_zero (fun h => hx (Fin.ext h))
    by_cases hxi : x.val ≤ i.val
    · exact Or.inr (Or.inl ⟨⟨x.val - 1, by omega⟩, Fin.ext (by simp [val_middle]; omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨x.val - i.val - 1, by omega⟩, Fin.ext (by simp [val_tail]; omega)⟩)

private theorem zero_lt_middle {n : ℕ} (i : Fin (n + 1)) (x : Fin i.val) :
    0 < (middle i x).val := by simp [val_middle]

private theorem middle_le_cut {n : ℕ} (i : Fin (n + 1)) (x : Fin i.val) :
    (middle i x).val ≤ i.val := by simp [val_middle]

private theorem cut_lt_tail {n : ℕ} (i : Fin (n + 1)) (x : Fin (n - i.val)) :
    i.val < (tail i x).val := by simp [val_tail]; omega

private def labels {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) (x : Fin (n + 1)) :
    Finset (Fin i.val) ⊕ Finset (Fin (n - i.val)) :=
  if h : 0 < x.val ∧ x.val ≤ i.val then
    .inl (L.val.part ⟨x.val - 1, by omega⟩)
  else if h' : i.val < x.val then
    .inr (R.val.part ⟨x.val - i.val - 1, by omega⟩)
  else .inr (firstBlock R)

private theorem labels_zero {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) : labels i L R 0 = .inr (firstBlock R) := by
  simp [labels]

private theorem labels_middle {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) (x : Fin i.val) :
    labels i L R (middle i x) = .inl (L.val.part x) := by
  rw [labels, dite_eq_left ⟨zero_lt_middle i x, middle_le_cut i x⟩]
  congr 2

private theorem labels_tail {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) (x : Fin (n - i.val)) :
    labels i L R (tail i x) = .inr (R.val.part x) := by
  have h := cut_lt_tail i x
  rw [labels, dite_eq_right (by omega), dite_eq_left h]
  congr 2
  exact Fin.ext (by simp [val_tail]; omega)

private theorem labels_noncrossing {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) : IsNoncrossing (labelPartition (labels i L R)) := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
  simp only [label_rel] at hac hbd
  replace hne := (not_congr (label_rel _ a b)).mp hne
  simp only [Fin.lt_def] at hab hbc hcd
  rcases slices i a with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases slices i b with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases slices i c with rfl | ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
    rcases slices i d with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩ <;>
    simp only [labels_zero, labels_middle, labels_tail, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, val_middle, val_tail, Fin.val_zero] at * <;> try omega
  · let z : Fin (n - i.val) := ⟨0, Nat.zero_lt_of_lt b.isLt⟩
    have he : firstBlock R = R.val.part z := dite_eq_left (Nat.zero_lt_of_lt b.isLt)
    rw [he] at hac hne
    have hb : z < b := by
      change 0 < b.val
      exact Nat.pos_of_ne_zero (fun h => hne (congrArg R.val.part (Fin.ext h.symm)))
    exact R.property ⟨z, b, c, d, hb, by omega, by omega, hac, hbd, hne⟩
  · exact L.property ⟨_, _, _, _, by omega, by omega, by omega, hac, hbd, hne⟩
  · exact R.property ⟨_, _, _, _, by omega, by omega, by omega, hac, hbd, hne⟩

private def join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) : NoncrossingPartition (n + 1) :=
  ⟨labelPartition (labels i L R), labels_noncrossing i L R⟩

private theorem join_rel {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) (x y : Fin (n + 1)) :
    (join i L R).val.part x = (join i L R).val.part y ↔ labels i L R x = labels i L R y :=
  label_rel _ _ _

private def isCut {n : ℕ} (P : NoncrossingPartition (n + 1)) (k : ℕ) : Prop :=
  n ≤ k ∨ ∃ x ∈ firstBlock P, x.val = k + 1

private noncomputable def cut {n : ℕ} (P : NoncrossingPartition (n + 1)) : Fin (n + 1) := by
  classical
  have h : ∃ k, isCut P k := ⟨n, Or.inl le_rfl⟩
  exact ⟨Nat.find h, Nat.lt_succ_of_le (Nat.find_min' h (Or.inl le_rfl))⟩

private theorem cut_spec {n : ℕ} (P : NoncrossingPartition (n + 1)) : isCut P (cut P).val := by
  classical
  exact Nat.find_spec _

private theorem cut_le {n : ℕ} (P : NoncrossingPartition (n + 1)) {k : ℕ}
    (h : isCut P k) : (cut P).val ≤ k := by
  classical
  exact Nat.find_min' _ h

private theorem middle_not_root {n : ℕ} (P : NoncrossingPartition (n + 1))
    (x : Fin (cut P).val) : middle (cut P) x ∉ firstBlock P := by
  intro hx
  have h := cut_le P (Or.inr ⟨middle (cut P) x, hx, val_middle _ _⟩)
  omega

private theorem tail_zero_root {n : ℕ} (P : NoncrossingPartition (n + 1))
    (h : 0 < n - (cut P).val) : tail (cut P) ⟨0, h⟩ ∈ firstBlock P := by
  obtain hn | ⟨x, hx, he⟩ := cut_spec P
  · omega
  · have hx' : x = tail (cut P) ⟨0, h⟩ := Fin.ext (by simpa [val_tail] using he)
    rwa [← hx']

private theorem separate {n : ℕ} (P : NoncrossingPartition (n + 1))
    (x : Fin (cut P).val) (y : Fin (n - (cut P).val)) :
    P.val.part (middle (cut P) x) ≠ P.val.part (tail (cut P) y) := by
  intro he
  let z : Fin (n - (cut P).val) := ⟨0, Nat.zero_lt_of_lt y.isLt⟩
  have hz := (mem_firstBlock P _).mp (tail_zero_root P z.isLt)
  have hx := mt (mem_firstBlock P _).mpr (middle_not_root P x)
  by_cases hy : z = y
  · exact hx (he.trans (hy ▸ hz))
  · refine P.property ⟨0, middle (cut P) x, tail (cut P) z, tail (cut P) y,
      zero_lt_middle _ _, ?_, (tail _).strictMono ?_, hz.symm, he, Ne.symm hx⟩
    · change (middle (cut P) x).val < (tail (cut P) z).val
      exact (middle_le_cut _ _).trans_lt (cut_lt_tail _ _)
    · exact Nat.pos_of_ne_zero (fun h => hy (Fin.ext h.symm))

private theorem join_pull {n : ℕ} (P : NoncrossingPartition (n + 1)) :
    join (cut P) (pull P (middle (cut P))) (pull P (tail (cut P))) = P := by
  let i := cut P
  let L := pull P (middle i)
  let R := pull P (tail i)
  change join i L R = P
  have h0 (y : Fin (n - i.val)) :
      firstBlock R = R.val.part y ↔ P.val.part 0 = P.val.part (tail i y) := by
    have hy := Nat.zero_lt_of_lt y.isLt
    rw [firstBlock, dite_eq_left hy, pull_rel]
    have h := (mem_firstBlock P _).1 (tail_zero_root P hy)
    change P.val.part (tail i ⟨0, hy⟩) = P.val.part 0 at h
    rw [h]
  have hm (x : Fin i.val) : P.val.part (middle i x) ≠ P.val.part 0 :=
    mt (mem_firstBlock P _).2 (middle_not_root P x)
  have hm' (x : Fin i.val) : P.val.part 0 ≠ P.val.part (middle i x) := (hm x).symm
  have hs (x : Fin i.val) (y : Fin (n - i.val)) :
      P.val.part (middle i x) ≠ P.val.part (tail i y) := separate P x y
  have hs' (x : Fin i.val) (y : Fin (n - i.val)) :
      P.val.part (tail i y) ≠ P.val.part (middle i x) := (hs x y).symm
  apply partition_ext
  intro x y
  rw [join_rel]
  rcases slices i x with rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases slices i y with rfl | ⟨y, rfl⟩ | ⟨y, rfl⟩ <;>
    simp [labels_zero, labels_middle, labels_tail, pull_rel, L, R, h0, hm, hm', hs, hs']
  simpa only [eq_comm] using h0 x

private theorem cut_join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) : cut (join i L R) = i := by
  apply Fin.ext
  apply le_antisymm
  · apply cut_le
    by_cases h : i.val = n
    · exact Or.inl h.ge
    · have hi : 0 < n - i.val := by omega
      refine Or.inr ⟨tail i ⟨0, hi⟩, (mem_firstBlock _ _).2 ?_, by simp [val_tail]⟩
      change (join i L R).val.part _ = (join i L R).val.part 0
      rw [join_rel, labels_tail, labels_zero, firstBlock, dite_eq_left hi]
  · obtain h | ⟨x, hx, he⟩ := cut_spec (join i L R)
    · omega
    · obtain rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩ := slices i x
      · simp at he
      · have h := (mem_firstBlock _ _).1 hx
        change (join i L R).val.part _ = (join i L R).val.part 0 at h
        simp only [join_rel, labels_middle, labels_zero, reduceCtorEq] at h
      · have hi := cut_lt_tail i x
        omega

private theorem pull_middle_join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) : pull (join i L R) (middle i) = L := by
  apply partition_ext
  intro x y
  rw [pull_rel, join_rel, labels_middle, labels_middle, Sum.inl.injEq]

private theorem pull_tail_join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) : pull (join i L R) (tail i) = R := by
  apply partition_ext
  intro x y
  rw [pull_rel, join_rel, labels_tail, labels_tail, Sum.inr.injEq]

private noncomputable def splitEquiv (n : ℕ) :
    NoncrossingPartition (n + 1) ≃
      Σ i : Fin (n + 1), NoncrossingPartition i.val × NoncrossingPartition (n - i.val) where
  toFun P := ⟨cut P, pull P (middle (cut P)), pull P (tail (cut P))⟩
  invFun p := join p.1 p.2.1 p.2.2
  left_inv := join_pull
  right_inv := by
    rintro ⟨i, L, R⟩
    let P := join i L R
    change (⟨cut P, pull P (middle (cut P)), pull P (tail (cut P))⟩ : Σ i : Fin (n + 1),
      NoncrossingPartition i.val × NoncrossingPartition (n - i.val)) = ⟨i, L, R⟩
    rw [cut_join i L R]
    simp only [P, pull_middle_join, pull_tail_join]

private theorem firstBlock_join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) :
    firstBlock (join i L R) = insert 0 ((firstBlock R).map (tail i).toEmbedding) := by
  ext x
  rw [mem_firstBlock]
  change (join i L R).val.part x = (join i L R).val.part 0 ↔ _
  rw [join_rel, labels_zero]
  rcases slices i x with rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · simp [labels_zero]
  · have hz : middle i x ≠ 0 := fun h => by
      simpa [h] using zero_lt_middle i x
    have ht (y : Fin (n - i.val)) : tail i y ≠ middle i x := fun h => by
      have := cut_lt_tail i y
      rw [h] at this
      exact (not_lt_of_ge (middle_le_cut i x)) this
    simp [labels_middle, hz, ht]
  · have hz : tail i x ≠ 0 := fun h => by
      simpa [h] using cut_lt_tail i x
    have hfirst : firstBlock R = R.val.part ⟨0, Nat.zero_lt_of_lt x.isLt⟩ :=
      dite_eq_left (Nat.zero_lt_of_lt x.isLt)
    simpa [labels_tail, hz, hfirst] using
      (R.val.part_eq_iff_mem (part_mem_parts R.val ⟨0, Nat.zero_lt_of_lt x.isLt⟩) (a := x))

private theorem part_middle_join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) (x : Fin i.val) :
    (join i L R).val.part (middle i x) = (L.val.part x).map (middle i).toEmbedding := by
  ext y
  rw [← rel_iff_mem, join_rel, labels_middle]
  rcases slices i y with rfl | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have h (z : Fin i.val) : middle i z ≠ 0 := fun e => by
      simpa [e] using zero_lt_middle i z
    simp [labels_zero, h]
  · simp [labels_middle, rel_iff_mem]
  · have h (z : Fin i.val) : middle i z ≠ tail i y := fun e => by
      have := middle_le_cut i z
      rw [e] at this
      exact (not_le_of_gt (cut_lt_tail i y)) this
    simp [labels_tail, h]

private theorem part_tail_join {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) (x : Fin (n - i.val))
    (hx : R.val.part x ≠ firstBlock R) :
    (join i L R).val.part (tail i x) = (R.val.part x).map (tail i).toEmbedding := by
  ext y
  rw [← rel_iff_mem, join_rel, labels_tail]
  rcases slices i y with rfl | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have h (z : Fin (n - i.val)) : tail i z ≠ 0 := fun e => by
      simpa [e] using cut_lt_tail i z
    simp [labels_zero, hx, h]
  · have h (z : Fin (n - i.val)) : tail i z ≠ middle i y := fun e => by
      have := cut_lt_tail i z
      rw [e] at this
      exact (not_lt_of_ge (middle_le_cut i y)) this
    simp [labels_middle, h]
  · simp [labels_tail, rel_iff_mem]

private def mapBlocks {α β : Type*} (e : α ↪ β) : Finset α ↪ Finset β :=
  (Finset.mapEmbedding e).toEmbedding

private theorem mapBlocks_apply {α β : Type*} (e : α ↪ β) (s : Finset α) :
    mapBlocks e s = s.map e := rfl

private theorem parts_join_erase {n : ℕ} (i : Fin (n + 1)) (L : NoncrossingPartition i.val)
    (R : NoncrossingPartition (n - i.val)) :
    (join i L R).val.parts.erase (firstBlock (join i L R)) =
      L.val.parts.map (mapBlocks (middle i).toEmbedding) ∪
        (R.val.parts.erase (firstBlock R)).map (mapBlocks (tail i).toEmbedding) := by
  let P := join i L R
  ext B
  simp only [mem_erase, mem_union, mem_map, mapBlocks_apply]
  constructor
  · rintro ⟨hB0, hB⟩
    obtain ⟨x, hx⟩ := P.val.nonempty_of_mem_parts hB
    obtain rfl | ⟨x, rfl⟩ | ⟨x, rfl⟩ := slices i x
    · exact (hB0 ((P.val.part_eq_of_mem hB hx).symm.trans (firstBlock_succ P).symm)).elim
    · exact Or.inl ⟨L.val.part x, part_mem_parts _ _,
        (part_middle_join i L R x).symm.trans (P.val.part_eq_of_mem hB hx)⟩
    · have hne : R.val.part x ≠ firstBlock R := fun he => hB0 (by
        rw [← P.val.part_eq_of_mem hB hx, firstBlock_succ, join_rel, labels_tail, labels_zero, he])
      exact Or.inr ⟨R.val.part x, ⟨hne, part_mem_parts _ _⟩,
        (part_tail_join i L R x hne).symm.trans (P.val.part_eq_of_mem hB hx)⟩
  · rintro (⟨C, hC, rfl⟩ | ⟨C, ⟨hC0, hC⟩, rfl⟩)
    · obtain ⟨x, hx⟩ := L.val.nonempty_of_mem_parts hC
      rw [← L.val.part_eq_of_mem hC hx, ← part_middle_join i L R x]
      refine ⟨?_, part_mem_parts _ _⟩
      intro h
      rw [firstBlock_succ] at h
      have hl := (join_rel i L R _ 0).1 h
      simp [labels_middle, labels_zero] at hl
    · obtain ⟨x, hx⟩ := R.val.nonempty_of_mem_parts hC
      have hne : R.val.part x ≠ firstBlock R := (R.val.part_eq_of_mem hC hx).trans_ne hC0
      rw [← R.val.part_eq_of_mem hC hx, ← part_tail_join i L R x hne]
      refine ⟨?_, part_mem_parts _ _⟩
      simpa [firstBlock_succ, join_rel, labels_tail, labels_zero] using hne

private theorem join_maps_disjoint {n : ℕ} (i : Fin (n + 1))
    (L : NoncrossingPartition i.val) (R : NoncrossingPartition (n - i.val)) :
    Disjoint (L.val.parts.map (mapBlocks (middle i).toEmbedding))
      ((R.val.parts.erase (firstBlock R)).map (mapBlocks (tail i).toEmbedding)) := by
  rw [Finset.disjoint_left]
  intro B hL hR
  obtain ⟨BL, hBL, rfl⟩ := mem_map.mp hL
  obtain ⟨BR, _, he⟩ := mem_map.mp hR
  obtain ⟨x, hx⟩ := L.val.nonempty_of_mem_parts hBL
  have hm : middle i x ∈ BL.map (middle i).toEmbedding := mem_map_of_mem _ hx
  simp only [mapBlocks_apply] at he
  rw [← he] at hm
  obtain ⟨y, _, hy⟩ := mem_map.mp hm
  have h := cut_lt_tail i y
  change tail i y = middle i x at hy
  rw [hy] at h
  exact (not_lt_of_ge (middle_le_cut i x)) h

-- Add t to the size of the first block. Splitting off its first point then
-- increments t in the tail, including the case where that tail is empty.
private noncomputable def weighted (κ : ℕ → ℂ) (t : ℕ) {n : ℕ}
    (P : NoncrossingPartition n) : ℂ :=
  κ ((firstBlock P).card + t) * ∏ B ∈ P.val.parts.erase (firstBlock P), κ B.card

private theorem weighted_zero (κ : ℕ → ℂ) (hκ : κ 0 = 1) {n : ℕ}
    (P : NoncrossingPartition n) : weighted κ 0 P = ∏ B ∈ P.val.parts, κ B.card := by
  cases n with
  | zero => simp [weighted, firstBlock, eq_indiscrete_zero P, hκ]
  | succ n =>
    simp only [weighted, add_zero]
    exact mul_prod_erase P.val.parts (fun B => κ B.card) (firstBlock_mem_parts (Nat.succ_pos n) P)

private theorem weighted_join (κ : ℕ → ℂ) (hκ : κ 0 = 1) (t : ℕ) {n : ℕ}
    (i : Fin (n + 1)) (L : NoncrossingPartition i.val) (R : NoncrossingPartition (n - i.val)) :
    weighted κ t (join i L R) = weighted κ 0 L * weighted κ (t + 1) R := by
  have hz : 0 ∉ (firstBlock R).map (tail i).toEmbedding := by
    rintro hz
    obtain ⟨x, _, hx⟩ := mem_map.mp hz
    change tail i x = 0 at hx
    simpa [hx] using cut_lt_tail i x
  rw [weighted_zero κ hκ, weighted, weighted, parts_join_erase, firstBlock_join,
    card_insert_of_notMem hz, card_map, prod_union (join_maps_disjoint i L R), prod_map, prod_map]
  simp only [mapBlocks_apply, card_map]
  rw [show (firstBlock R).card + 1 + t = (firstBlock R).card + (t + 1) by omega]
  ac_rfl

private noncomputable def weightedSeries (κ : ℕ → ℂ) (t : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => ∑ P : NoncrossingPartition n, weighted κ t P

private theorem weightedSeries_step (κ : ℕ → ℂ) (hκ : κ 0 = 1) (t : ℕ) :
    weightedSeries κ t = X * (weightedSeries κ 0 * weightedSeries κ (t + 1)) + C (κ t) := by
  ext d
  rcases d with _ | n
  · have hem (P : NoncrossingPartition 0) : P.val.parts = ∅ :=
      Finpartition.parts_eq_empty_iff.mpr (by simp)
    simp [weightedSeries, weighted, firstBlock, hem]
  · rw [map_add, coeff_succ_X_mul, coeff_C, ite_eq_right (Nat.succ_ne_zero n), add_zero, coeff_mul]
    simp only [weightedSeries, coeff_mk]
    rw [Fintype.sum_equiv (splitEquiv n) _ (fun p => weighted κ 0 p.2.1 *
      weighted κ (t + 1) p.2.2) (fun P => by
        rcases h : (splitEquiv n) P with ⟨i, L, R⟩
        have hp := (splitEquiv n).symm_apply_apply P
        rw [h] at hp
        change join i L R = P at hp
        rw [← hp, weighted_join κ hκ]), Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    let f (i : ℕ) := (∑ P : NoncrossingPartition i, weighted κ 0 P) *
      ∑ P : NoncrossingPartition (n - i), weighted κ (t + 1) P
    exact Fin.sum_univ_eq_sum_range f (n + 1)

private theorem weightedSeries_subst (κ : ℕ → ℂ) (hκ : κ 0 = 1) :
    weightedSeries κ 0 = (PowerSeries.mk κ).subst (X * weightedSeries κ 0) := by
  let q : ℂ⟦X⟧ := X * weightedSeries κ 0
  have hq : HasSubst q := HasSubst.X'.mul_left
  let S (t : ℕ) : ℂ⟦X⟧ := (PowerSeries.mk fun n => κ (n + t)).subst q
  have hS (t : ℕ) : S t = X * (weightedSeries κ 0 * S (t + 1)) + C (κ t) := by
    have hshift : (PowerSeries.mk fun n => κ (n + t)) =
        X * (PowerSeries.mk fun n => κ (n + (t + 1))) + C (κ t) := by
      ext n
      cases n with
      | zero => simp
      | succ n => simp [coeff_succ_X_mul, Nat.add_right_comm, Nat.add_assoc]
    unfold S
    rw [hshift, subst_add hq, subst_mul hq, subst_X hq, subst_C]
    change (X * weightedSeries κ 0) * _ + _ = _
    rw [mul_assoc]
    rfl
  have he (n : ℕ) : ∀ t, coeff n (weightedSeries κ t) = coeff n (S t) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro t
      cases n with
      | zero =>
        rw [weightedSeries_step κ hκ t, hS t]
        simp
      | succ n =>
        have hcoeff (p : ℕ × ℕ) (hp : p ∈ antidiagonal n) :
            coeff p.2 (weightedSeries κ (t + 1)) = coeff p.2 (S (t + 1)) :=
          ih p.2 (by have := Finset.mem_antidiagonal.mp hp; omega) (t + 1)
        have hm : coeff n (weightedSeries κ 0 * weightedSeries κ (t + 1)) =
            coeff n (weightedSeries κ 0 * S (t + 1)) := by
          rw [coeff_mul, coeff_mul]
          exact Finset.sum_congr rfl fun p hp => by rw [hcoeff p hp]
        rw [weightedSeries_step κ hκ t, hS t, map_add, map_add, coeff_succ_X_mul,
          coeff_succ_X_mul, hm]
  exact PowerSeries.ext fun n => he n 0

private noncomputable def cumulants (m : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 1 else freeCumulant m n

private theorem moments_subst (m : ℕ → ℂ) (hm : m 0 = 1) :
    PowerSeries.mk m = (PowerSeries.mk (cumulants m)).subst (X * PowerSeries.mk m) := by
  have he : weightedSeries (cumulants m) 0 = PowerSeries.mk m := by
    ext n
    have hκ : cumulants m 0 = 1 := by simp [cumulants]
    simp only [weightedSeries, coeff_mk, weighted_zero _ hκ]
    rcases n with _ | n
    · have hem (P : NoncrossingPartition 0) : P.val.parts = ∅ :=
        Finpartition.parts_eq_empty_iff.mpr (by simp)
      simp [hem, hm]
    · rw [moment_eq_sum_noncrossing_prod_freeCumulant m (Nat.succ_pos n)]
      refine Finset.sum_congr rfl fun P _ => Finset.prod_congr rfl fun B hB => ?_
      simp [cumulants, (P.val.nonempty_of_mem_parts hB).card_pos.ne']
  rw [← he, ← weightedSeries_subst (cumulants m) (by simp [cumulants])]

section Resolvents

variable {A : Type*} [Ring A] [Algebra ℂ A]

private noncomputable def expect (φ : A →ₗ[ℂ] ℂ) : A⟦X⟧ →+ ℂ⟦X⟧ where
  toFun f := PowerSeries.mk fun n => φ (coeff n f)
  map_zero' := PowerSeries.ext fun n => by simp
  map_add' f g := PowerSeries.ext fun n => by simp

private theorem coeff_expect (φ : A →ₗ[ℂ] ℂ) (f : A⟦X⟧) (n : ℕ) :
    coeff n (expect φ f) = φ (coeff n f) := by simp [expect]

private theorem expect_one (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) :
    expect φ 1 = 1 := by
  ext n
  cases n <;> simp [coeff_expect, hφ]

private abbrev liftScalar : ℂ⟦X⟧ →+* A⟦X⟧ := PowerSeries.map (algebraMap ℂ A)

private theorem expect_scalar_mul (φ : A →ₗ[ℂ] ℂ) (p : ℂ⟦X⟧) (f : A⟦X⟧) :
    expect φ (liftScalar p * f) = p * expect φ f := by
  ext n
  simp only [coeff_expect, coeff_mul, map_sum, coeff_map, ← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem commute_liftScalar (p : ℂ⟦X⟧) (q : A⟦X⟧) :
    Commute (liftScalar p) q := by
  change liftScalar p * q = q * liftScalar p
  ext n
  simp only [coeff_mul, coeff_map]
  rw [← Nat.sum_antidiagonal_swap]
  exact Finset.sum_congr rfl fun _ _ => Algebra.commutes _ _

omit [Algebra ℂ A] in
private theorem inverse_eq_of_mul (p : A⟦X⟧) (hp : constantCoeff p = 1)
    (q : A⟦X⟧) (h : p * q = 1) : invOfUnit p 1 = q := by
  have h' := invOfUnit_mul p 1 (by simpa using hp)
  calc
    invOfUnit p 1 = invOfUnit p 1 * (p * q) := by rw [h, mul_one]
    _ = q := by rw [← mul_assoc, h', one_mul]

private noncomputable def denominator (x : A) (K : ℂ⟦X⟧) : A⟦X⟧ :=
  liftScalar K - X * C x

private theorem liftScalar_const (p : ℂ⟦X⟧) :
    constantCoeff (liftScalar p : A⟦X⟧) = algebraMap ℂ A (constantCoeff p) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_map]

private theorem denominator_const (x : A) (K : ℂ⟦X⟧) (hK : constantCoeff K = 1) :
    constantCoeff (denominator x K) = 1 := by
  simp [denominator, hK, liftScalar_const]

private theorem inverse_coeff_mem (x : A) (K : ℂ⟦X⟧) (n : ℕ) :
    coeff n (invOfUnit (denominator x K) 1) ∈ Algebra.adjoin ℂ ({x} : Set A) := by
  let B := Algebra.adjoin ℂ ({x} : Set A)
  have hx : x ∈ B := Algebra.subset_adjoin (by simp)
  have hden (d : ℕ) : coeff d (denominator x K) ∈ B := by
    have hK : coeff d (liftScalar K : A⟦X⟧) ∈ B := by
      rw [coeff_map]
      exact B.algebraMap_mem _
    rw [denominator, map_sub]
    refine sub_mem hK ?_
    cases d with
    | zero => simp
    | succ d =>
      rw [coeff_succ_X_mul, coeff_C]
      split
      · exact hx
      · exact zero_mem _
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [coeff_invOfUnit]
    split
    · simp
    · refine mul_mem (by simp : -↑((1 : Aˣ)⁻¹) ∈ B) (B.toSubmodule.sum_mem fun p _ => ?_)
      split
      · exact B.mul_mem (hden p.1) (ih _ (by assumption))
      · exact zero_mem _

private theorem expect_C (φ : A →ₗ[ℂ] ℂ) (x : A) :
    expect φ (C x) = C (φ x) := by
  ext n
  cases n <;> simp [coeff_expect]

-- The discrete topology on coefficients gives the formal power series topology.
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

section
variable [TopologicalSpace A] [DiscreteTopology A]

private theorem expect_hasSum (φ : A →ₗ[ℂ] ℂ) {f : ℕ → A⟦X⟧} {q : A⟦X⟧}
    (h : HasSum f q) : HasSum (fun i => expect φ (f i)) (expect φ q) := by
  rw [hasSum_iff_hasSum_coeff] at h ⊢
  intro n
  simp only [coeff_expect]
  exact (h n).map (φ : A →+ ℂ) (continuous_of_discreteTopology : Continuous (φ : A → ℂ))

end

private noncomputable def moments (φ : A →ₗ[ℂ] ℂ) (x : A) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => φ (x ^ n)

private noncomputable def cumulantSeries (φ : A →ₗ[ℂ] ℂ) (x : A) : ℂ⟦X⟧ :=
  PowerSeries.mk (cumulants fun n => φ (x ^ n))

private theorem cumulantSeries_const (φ : A →ₗ[ℂ] ℂ) (x : A) :
    constantCoeff (cumulantSeries φ x) = 1 := by
  simp [cumulantSeries, cumulants, ← coeff_zero_eq_constantCoeff_apply]

-- The normalized resolvent expands in powers of g = X / K.
private theorem expect_inverse (φ : A →ₗ[ℂ] ℂ) (x : A) (K : ℂ⟦X⟧)
    (hK : constantCoeff K = 1) :
    expect φ (invOfUnit (denominator x K) 1) =
      invOfUnit K 1 * (moments φ x).subst (X * invOfUnit K 1) := by
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := discreteTopology_bot A
  let F := invOfUnit K 1
  let g : ℂ⟦X⟧ := X * F
  let z : A⟦X⟧ := liftScalar g * C x
  have hg : HasSubst g := HasSubst.X'.mul_left
  have hz : constantCoeff z = 0 := by simp [z, g, liftScalar_const]
  have hKinv : K * F = 1 := mul_invOfUnit K 1 (by simpa using hK)
  have hmul : denominator x K * liftScalar F = 1 - z := by
    rw [denominator, sub_mul, ← map_mul, hKinv, map_one]
    congr 1
    rw [mul_assoc, ← (commute_liftScalar F (C x : A⟦X⟧)).eq]
    simp [z, g, map_mul, map_X, mul_assoc]
  let G : A⟦X⟧ := ∑' k : ℕ, z ^ k
  have hinv : invOfUnit (denominator x K) 1 = liftScalar F * G := by
    apply inverse_eq_of_mul _ (denominator_const x K hK)
    rw [← mul_assoc, hmul]
    exact one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hz
  rw [hinv, expect_scalar_mul]
  congr 1
  ext d
  have hG : HasSum (fun j : ℕ => z ^ j) G :=
    (summable_pow_of_constantCoeff_eq_zero hz).hasSum
  have hsum := (hasSum_iff_hasSum_coeff (R := ℂ)).mp (expect_hasSum φ hG) d
  change coeff d (expect φ G) = coeff d ((moments φ x).subst g)
  rw [← hsum.tsum_eq, coeff_subst' hg]
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℕ)
    (coeff_subst_finite' hg (moments φ x) d)]
  congr 1
  funext j
  have hp : z ^ j = liftScalar (g ^ j) * C (x ^ j) := by
    change (liftScalar g * C x) ^ j = _
    rw [(commute_liftScalar g (C x : A⟦X⟧)).mul_pow, map_pow, map_pow]
  rw [hp, expect_scalar_mul, expect_C, coeff_mul_C]
  simp [moments, smul_eq_mul, mul_comm]

-- Composition with the inverse of X * M characterizes the cumulant series.
private theorem expect_inverse_eq_one_iff (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (x : A)
    (K : ℂ⟦X⟧) (hK : constantCoeff K = 1) :
    expect φ (invOfUnit (denominator x K) 1) = 1 ↔ K = cumulantSeries φ x := by
  let M := moments φ x
  let Cκ := cumulantSeries φ x
  let q : ℂ⟦X⟧ := X * M
  let F := invOfUnit K 1
  let g : ℂ⟦X⟧ := X * F
  have hq : HasSubst q := HasSubst.X'.mul_left
  have hg : HasSubst g := HasSubst.X'.mul_left
  have hm : M = Cκ.subst q := moments_subst _ (by simpa using hφ)
  have hKF : K * F = 1 := mul_invOfUnit K 1 (by simpa using hK)
  have hFK : F * K = 1 := invOfUnit_mul K 1 (by simpa using hK)
  rw [expect_inverse φ x K hK]
  change F * M.subst g = 1 ↔ K = Cκ
  constructor
  · intro h
    have hM : M.subst g = K := by
      calc
        M.subst g = K * (F * M.subst g) := by rw [← mul_assoc, hKF, one_mul]
        _ = K := by rw [h, mul_one]
    have hqg : q.subst g = X := by
      calc
        q.subst g = g * M.subst g := by rw [show q = X * M by rfl, subst_mul hg, subst_X hg]
        _ = X := by rw [hM, show g = X * F by rfl, mul_assoc, hFK, mul_one]
    calc
      K = M.subst g := hM.symm
      _ = Cκ := by rw [hm, subst_comp_subst_apply hq hg, hqg, X_subst]
  · intro h
    have hs : g.subst q = X := by
      have he : M * F.subst q = 1 := by
        rw [hm, ← h, ← subst_mul hq, hKF]
        rw [← coe_substAlgHom (R := ℂ) hq, map_one]
      calc
        g.subst q = q * F.subst q := by
          rw [show g = X * F by rfl, subst_mul hq, subst_X hq]
        _ = X := by rw [show q = X * M by rfl, mul_assoc, he, mul_one]
    have hqg : q.subst g = X := by
      refine g.subst_eq_X_of_subst_eq_X (by simp [g]) ?_ hq hs
      change IsUnit (coeff (0 + 1) (X * F))
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
      simp [F]
    have he : M.subst g = K := by
      rw [hm, subst_comp_subst_apply hq hg, hqg, X_subst, h]
    rwa [he]

-- Each coefficient of a series product is a linear combination of products
-- of one coefficient from each factor, in their original order.
private def coefficientProducts (w : List (A⟦X⟧)) : Set A :=
  {x | ∃ v : List A, List.Forall₂ (fun f a => ∃ n, coeff n f = a) w v ∧ v.prod = x}

private theorem coeff_prod_mem (w : List (A⟦X⟧)) (n : ℕ) :
    coeff n w.prod ∈ Submodule.span ℂ (coefficientProducts w) := by
  induction w generalizing n with
  | nil =>
    rw [List.prod_nil, coeff_one]
    split
    · exact Submodule.subset_span ⟨[], List.Forall₂.nil, rfl⟩
    · exact zero_mem _
  | cons f w ih =>
    rw [List.prod_cons, coeff_mul]
    refine (Submodule.span ℂ _).sum_mem fun j _ => ?_
    let L := LinearMap.mulLeft ℂ (coeff j.1 f)
    have hL : (Submodule.span ℂ (coefficientProducts w)).map L ≤
        Submodule.span ℂ (coefficientProducts (f :: w)) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨coeff j.1 f :: v, List.Forall₂.cons ⟨j.1, rfl⟩ hv, rfl⟩
    exact hL (Submodule.mem_map.mpr ⟨_, ih j.2, rfl⟩)

private theorem expect_word (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) {ι : Type*}
    {B : ι → Subalgebra ℂ A} (hf : IsFreelyIndependent φ hφ B) (s : ι → A⟦X⟧)
    (hmem : ∀ i n, coeff n (s i) ∈ B i) (hzero : ∀ i, expect φ (s i) = 0)
    (w : List ι) (hw : w ≠ []) (ha : w.IsChain (· ≠ ·)) :
    expect φ (w.map s).prod = 0 := by
  ext d
  rw [coeff_expect, map_zero, ← LinearMap.mem_ker]
  refine (Submodule.span_le.mpr ?_) (coeff_prod_mem (w.map s) d)
  rintro _ ⟨v, hv, rfl⟩
  obtain _ | ⟨i, w⟩ := w
  · exact (hw rfl).elim
  let l := i :: w
  have hvlen : v.length = w.length + 1 := by simpa [l] using hv.length_eq.symm
  let idx (i : Fin (w.length + 1)) := l.get i
  let val (i : Fin (w.length + 1)) := v.get (Fin.cast hvlen.symm i)
  have hv' (i : Fin (w.length + 1)) : ∃ n, coeff n (s (idx i)) = val i := by
    have he := hv.get (i := i.val) (by simpa only [List.length_map, List.length_cons] using i.isLt)
      (by rw [hvlen]; exact i.isLt)
    simpa only [idx, val, l, List.get_eq_getElem, List.getElem_map, Fin.val_cast] using he
  have hvanish := hf w.length idx val
    (fun j => List.isChain_iff_getElem.mp ha j (by simp))
    (fun j => by obtain ⟨n, hn⟩ := hv' j; rw [← hn]; exact hmem _ _)
    (fun j => by
      obtain ⟨n, hn⟩ := hv' j
      rw [← hn, ← coeff_expect, hzero, map_zero])
  have he : List.ofFn val = v := by
    apply List.ext_getElem
    · simpa using hvlen.symm
    · intro i h₁ h₂
      simp only [List.getElem_ofFn, val, List.get_eq_getElem, Fin.val_cast]
  rwa [he] at hvanish

private def alternatingPairs : ℕ → List (Fin 2) → List (Fin 2)
  | 0, w => w
  | k + 1, w => 0 :: 1 :: alternatingPairs k w

private theorem alternatingPairs_chain (k : ℕ) (w : List (Fin 2))
    (hw : (1 :: w).IsChain (· ≠ ·)) : (1 :: alternatingPairs k w).IsChain (· ≠ ·) := by
  induction k with
  | zero => exact hw
  | succ k ih => simp [alternatingPairs, ih]

omit [Algebra ℂ A] in
private theorem alternatingPairs_prod (s : Fin 2 → A⟦X⟧) (k : ℕ) (w : List (Fin 2)) :
    ((alternatingPairs k w).map s).prod = (s 0 * s 1) ^ k * (w.map s).prod := by
  induction k with
  | zero => simp [alternatingPairs]
  | succ k ih => simp [alternatingPairs, ih, pow_succ', mul_assoc]

section
variable [TopologicalSpace A] [DiscreteTopology A]

private theorem expect_geometric_of_free (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1)
    {B : Fin 2 → Subalgebra ℂ A} (hf : IsFreelyIndependent φ hφ B) (s : Fin 2 → A⟦X⟧)
    (hmem : ∀ i n, coeff n (s i) ∈ B i) (hzero : ∀ i, expect φ (s i) = 0)
    (hz : constantCoeff (s 0 * s 1) = 0) :
    expect φ ((1 + s 1) * (∑' k : ℕ, (s 0 * s 1) ^ k) * (1 + s 0)) = 1 := by
  have hs := (summable_pow_of_constantCoeff_eq_zero hz).hasSum
  have hs' := expect_hasSum φ ((hs.mul_left (1 + s 1)).mul_right (1 + s 0))
  have h₁ (k : ℕ) (w : List (Fin 2)) (hw : (1 :: w).IsChain (· ≠ ·)) :
      expect φ (s 1 * ((s 0 * s 1) ^ k * (w.map s).prod)) = 0 := by
    rw [← alternatingPairs_prod]
    exact expect_word φ hφ hf s hmem hzero _ (by simp) (alternatingPairs_chain k w hw)
  have h₂ (k : ℕ) (w : List (Fin 2)) (hw : (1 :: w).IsChain (· ≠ ·))
      (hn : alternatingPairs k w ≠ []) :
      expect φ ((s 0 * s 1) ^ k * (w.map s).prod) = 0 := by
    rw [← alternatingPairs_prod]
    exact expect_word φ hφ hf s hmem hzero _ hn (alternatingPairs_chain k w hw).tail
  have hterm (k : ℕ) : expect φ ((1 + s 1) * (s 0 * s 1) ^ k * (1 + s 0)) =
      if k = 0 then 1 else 0 := by
    have he₁ := h₁ k [] (by simp)
    have he₂ := h₁ k [0] (by simp)
    have he₃ := h₂ k [0] (by simp) (by cases k <;> simp [alternatingPairs])
    simp only [List.map_nil, List.map_cons, List.prod_nil, List.prod_cons, mul_one] at he₁ he₂ he₃
    simp only [add_mul, mul_add, one_mul, mul_one, map_add, mul_assoc, he₁, he₂, he₃,
      add_zero]
    cases k with
    | zero => simp [expect_one φ hφ]
    | succ k =>
      simpa using h₂ (k + 1) [] (by simp) (by simp [alternatingPairs])
  simp_rw [hterm] at hs'
  rw [← hs'.tsum_eq]
  simp

end

private theorem denominator_add (a b : A) (K L : ℂ⟦X⟧) :
    denominator (a + b) (K + L - 1) = denominator a K + denominator b L - 1 := by
  simp only [denominator, map_add, map_sub, map_one, mul_add]
  abel

private theorem add_cumulantSeries (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a b : A)
    (hfree : AreFree φ hφ ![a, b]) :
    cumulantSeries φ (a + b) = cumulantSeries φ a + cumulantSeries φ b - 1 := by
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := discreteTopology_bot A
  let K := cumulantSeries φ a
  let L := cumulantSeries φ b
  let P := denominator a K
  let Q := denominator b L
  let S := invOfUnit P 1
  let T := invOfUnit Q 1
  let U := S - 1
  let V := T - 1
  have hK : constantCoeff K = 1 := cumulantSeries_const φ a
  have hL : constantCoeff L = 1 := cumulantSeries_const φ b
  have hKL : constantCoeff (K + L - 1) = 1 := by simp [hK, hL]
  have hP : constantCoeff P = 1 := denominator_const a K hK
  have hQ : constantCoeff Q = 1 := denominator_const b L hL
  have hPS : P * S = 1 := mul_invOfUnit _ _ (by simpa using hP)
  have hQT : Q * T = 1 := mul_invOfUnit _ _ (by simpa using hQ)
  have hz : constantCoeff (U * V) = 0 := by simp [U, V, S, T]
  -- The inverse for the sum is T * (1 - U * V)⁻¹ * S.
  have hmid : (P + Q - 1) * T = P * (1 - U * V) := by
    calc
      (P + Q - 1) * T = P * (T + S - S * T) := by
        simp [add_mul, sub_mul, mul_add, mul_sub, ← mul_assoc, hPS, hQT]
      _ = P * (1 - U * V) := by congr 1; dsimp [U, V]; noncomm_ring
  let G : A⟦X⟧ := ∑' k : ℕ, (U * V) ^ k
  have hinv : invOfUnit (denominator (a + b) (K + L - 1)) 1 = T * G * S := by
    apply inverse_eq_of_mul _ (denominator_const _ _ hKL)
    rw [denominator_add, ← mul_assoc, ← mul_assoc, hmid, mul_assoc P,
      one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hz, mul_one, hPS]
  symm
  apply (expect_inverse_eq_one_iff φ hφ (a + b) _ hKL).1
  rw [hinv]
  have hs : expect φ S = 1 := (expect_inverse_eq_one_iff φ hφ a K hK).2 rfl
  have ht : expect φ T = 1 := (expect_inverse_eq_one_iff φ hφ b L hL).2 rfl
  let s : Fin 2 → A⟦X⟧ := ![U, V]
  have hmem (i : Fin 2) (n : ℕ) : coeff n (s i) ∈ Algebra.adjoin ℂ ({![a, b] i} : Set A) := by
    fin_cases i
    · change coeff n (S - 1) ∈ Algebra.adjoin ℂ ({a} : Set A)
      rw [map_sub]
      refine sub_mem (inverse_coeff_mem a K n) ?_
      cases n <;> simp
    · change coeff n (T - 1) ∈ Algebra.adjoin ℂ ({b} : Set A)
      rw [map_sub]
      refine sub_mem (inverse_coeff_mem b L n) ?_
      cases n <;> simp
  have hzero (i : Fin 2) : expect φ (s i) = 0 := by
    fin_cases i
    · change expect φ (S - 1) = 0
      simp [hs, expect_one φ hφ]
    · change expect φ (T - 1) = 0
      simp [ht, expect_one φ hφ]
  have h := expect_geometric_of_free φ hφ hfree s hmem hzero hz
  change expect φ ((1 + V) * G * (1 + U)) = 1 at h
  rwa [show 1 + V = T by dsimp [V]; abel, show 1 + U = S by dsimp [U]; abel] at h

end Resolvents
end MathlibExt.Probability.FreeProbabilityWanted.freeCumulant_add_of_areFree

namespace MathlibExt.Probability.FreeProbabilityWanted

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Free cumulants are additive for free variables** (Anderson, Guionnet and Zeitouni, *An
Introduction to Random Matrices*, Lemma 5.3.21). Let `(A, φ)` be a noncommutative probability space
(`φ` linear with `φ 1 = 1`) and let `a, b ∈ A` be free. Then for every `n ≥ 1` the `n`-th free
cumulant of `a + b` is the sum of those of `a` and `b`:
`κₙ(a + b) = κₙ(a) + κₙ(b)`, where `κₙ(x)` is the free cumulant of the moment sequence
`k ↦ φ (xᵏ)`. Equivalently the R-transform is additive, `R_{a+b} = R_a + R_b`
(Corollary 5.3.23). The source states it for bounded operators; its proof (multilinearity of the
cumulants and the vanishing of mixed cumulants, Theorem 5.3.15) is algebraic. -/
public theorem freeCumulant_add_of_areFree (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a b : A)
    (hfree : AreFree φ hφ ![a, b]) {n : ℕ} (hn : 1 ≤ n) :
    freeCumulant (fun k => φ ((a + b) ^ k)) n =
      freeCumulant (fun k => φ (a ^ k)) n + freeCumulant (fun k => φ (b ^ k)) n := by
  have h := congrArg (PowerSeries.coeff n)
    (freeCumulant_add_of_areFree.add_cumulantSeries φ hφ a b hfree)
  simpa [freeCumulant_add_of_areFree.cumulantSeries, freeCumulant_add_of_areFree.cumulants,
    PowerSeries.coeff_one, show n ≠ 0 by omega] using h

end MathlibExt.Probability.FreeProbabilityWanted
