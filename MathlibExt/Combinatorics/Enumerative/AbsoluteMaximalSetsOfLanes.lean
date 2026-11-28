/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSingles

import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.Combinatorics.NoncrossingPartition.Pairing
import MathlibExt.NumberTheory.DivisorCountParity

/-!
# Absolute maximal sets of lanes

The maximal sets of lanes of the standard road intersection of size `n`, with all lanes allowed,
are in bijection with the noncrossing partitions of `Fin n` and are counted by `catalan n`.
The correspondence joins each entry to the preceding index of its block in cyclic order.
The count identifies these lane sets with the noncrossing perfect matchings on `2 * n` points.
The absolute and nonabsolute subclasses are counted by the lonely and marriageable singles
partitions, respectively.

## References

* Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and Catalan
  Numbers*, Journal of Integer Sequences **28** (2025), Article 25.1.1, pp. 1–13, Section 2,
  Lemma 16 and Corollaries 17 and 18. The nonabsolute count is Corollary 17.
* Richard P. Stanley, *Catalan Numbers*, Cambridge University Press (2015), p. 28,
  entries 59 and 61, cited by Rouyer and Ninet for the correspondence with noncrossing chords.
* `MathlibExt.Combinatorics.NoncrossingPartition.Pairing`: `IsNCMatching` and `card_ncMatching`
  supply the matching model and its Catalan count.
-/

namespace MetaMathlibExt
namespace card_absolute_maximalSetsOfLanes

open Finset NoncrossingPartition

variable {n : ℕ}

private abbrev Lane (n : ℕ) := Fin n × Fin n

-- The open clockwise gap from exit j to entry i, after collapsing each entry-exit pair.
private def gap (i j x : Fin n) : Prop :=
  if j < i then j < x ∧ x < i else j < x ∨ x < i

private theorem gap_left (i j : Fin n) : ¬ gap i j i := by
  unfold gap
  split <;> omega

private theorem gap_right (i j : Fin n) : ¬ gap i j j := by
  unfold gap
  split <;> omega

private theorem gap_loop (i x : Fin n) : gap i i x ↔ x ≠ i := by
  simp only [gap, lt_irrefl, ite_false]
  omega

-- The midpoint of an entry-exit pair is on the same side of a lane as either endpoint,
-- except at that lane's own entry or exit. This gives the crossing test in terms of gaps.
private theorem meet_iff {i j k l : Fin n} (hi : i ≠ k) (hj : j ≠ l) :
    lanesMeet (i, j) (k, l) ↔ ¬ (gap i j k ↔ gap i j l) := by
  simp only [lanesMeet, hi, hj, false_or, gap]
  split <;> omega

private theorem mem_block_iff (P : SetPartition n) (x i : Fin n) :
    x ∈ P.part i ↔ P.part x = P.part i :=
  P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)

-- In each block, join every entry to the exit immediately preceding it in cyclic order.
private noncomputable def lanes (P : SetPartition n) : Finset (Lane n) := by
  classical
  exact univ.filter fun (i, j) => j ∈ P.part i ∧ ∀ x ∈ P.part i, ¬ gap i j x

private theorem mem_lanes {P : SetPartition n} {i j : Fin n} :
    (i, j) ∈ lanes P ↔ j ∈ P.part i ∧ ∀ x ∈ P.part i, ¬ gap i j x := by
  classical
  simp [lanes]

private def rank (i x : Fin n) : ℕ := if x < i then n + x.val else x.val

private theorem gap_iff_rank (i j x : Fin n) : gap i j x ↔ rank i j < rank i x := by
  simp only [gap, rank]
  split_ifs <;> omega

private theorem exists_lane (P : SetPartition n) (i : Fin n) : ∃ j, (i, j) ∈ lanes P := by
  obtain ⟨j, hj, hmax⟩ := (P.part i).exists_max_image (rank i) ⟨i, mem_part_self P i⟩
  exact ⟨j, mem_lanes.mpr ⟨hj, fun x hx => by rw [gap_iff_rank]; exact (hmax x hx).not_gt⟩⟩

private theorem unique_exit {P : SetPartition n} {i j k : Fin n}
    (hj : (i, j) ∈ lanes P) (hk : (i, k) ∈ lanes P) : j = k := by
  obtain ⟨hj, hgj⟩ := mem_lanes.mp hj
  obtain ⟨hk, hgk⟩ := mem_lanes.mp hk
  have h₁ := hgj k hk
  have h₂ := hgk j hj
  simp only [gap] at h₁ h₂
  split_ifs at h₁ h₂ <;> omega

private theorem unique_entry {P : SetPartition n} {i k j : Fin n}
    (hi : (i, j) ∈ lanes P) (hk : (k, j) ∈ lanes P) : i = k := by
  obtain ⟨hi, hgi⟩ := mem_lanes.mp hi
  obtain ⟨hk, hgk⟩ := mem_lanes.mp hk
  have heq := ((mem_block_iff P j i).mp hi).symm.trans ((mem_block_iff P j k).mp hk)
  have h₁ := hgi k (heq ▸ mem_part_self P k)
  have h₂ := hgk i (heq ▸ mem_part_self P i)
  simp only [gap] at h₁ h₂
  split_ifs at h₁ h₂ <;> omega

-- A different block cannot straddle a gap between two points of the same block.
private theorem gap_constant {P : SetPartition n} (hnc : IsNoncrossing P) {i j k l : Fin n}
    (hij : P.part i = P.part j) (hkl : P.part k = P.part l) (hik : P.part i ≠ P.part k)
    (hk : gap i j k) : gap i j l := by
  by_contra hl
  have hil : i ≠ l := fun h => hik ((congrArg P.part h).trans hkl.symm)
  have hjl : j ≠ l := fun h => hik (hij.trans ((congrArg P.part h).trans hkl.symm))
  apply hnc
  by_cases hji : j < i
  · simp only [gap, ite_eq_left hji] at hk hl
    by_cases h : j < l
    · exact ⟨j, k, i, l, hk.1, hk.2, by omega, hij.symm, hkl, by grind⟩
    · exact ⟨l, j, k, i, by omega, hk.1, hk.2, hkl.symm, hij.symm, by grind⟩
  · simp only [gap, ite_eq_right hji] at hk hl
    rcases hk with hk | hk
    · exact ⟨i, l, j, k, by omega, by omega, hk, hij, hkl.symm, by grind⟩
    · exact ⟨k, i, l, j, hk, by omega, by omega, hkl, hij, by grind⟩

private theorem independent {P : SetPartition n} (hnc : IsNoncrossing P) :
    ∀ a ∈ lanes P, ∀ b ∈ lanes P, a ≠ b → ¬ lanesMeet a b := by
  rintro ⟨i, j⟩ ha ⟨k, l⟩ hb hne
  have hi : i ≠ k := by rintro rfl; exact hne (by rw [unique_exit ha hb])
  have hj : j ≠ l := by rintro rfl; exact hne (by rw [unique_entry ha hb])
  rw [meet_iff hi hj, not_not]
  obtain ⟨hji, hg⟩ := mem_lanes.mp ha
  have hlk := (mem_block_iff P l k).mp (mem_lanes.mp hb).1
  have hij := ((mem_block_iff P j i).mp hji).symm
  by_cases h : P.part i = P.part k
  · have hk := hg k (h ▸ mem_part_self P k)
    have hl := hg l ((mem_block_iff ..).mpr (hlk.trans h.symm))
    simp [hk, hl]
  · exact ⟨gap_constant hnc hij hlk.symm h, gap_constant hnc hij hlk (by grind)⟩

private theorem maximal {P : SetPartition n} (hnc : IsNoncrossing P) :
    IsMaximalSetOfLanes univ (lanes P) := by
  refine ⟨subset_univ _, independent hnc, ?_⟩
  rintro ⟨i, j⟩ - -
  obtain ⟨k, hk⟩ := exists_lane P i
  exact ⟨(i, k), hk, Or.inl rfl⟩

-- Two indices are in one block when every lane places them on the same side.
private def sameSide (S : Finset (Lane n)) : Setoid (Fin n) where
  r x y := ∀ a ∈ S, gap a.1 a.2 x ↔ gap a.1 a.2 y
  iseqv := ⟨fun _ _ _ => Iff.rfl, fun h a ha => (h a ha).symm,
    fun h h' a ha => (h a ha).trans (h' a ha)⟩

private noncomputable def regions (S : Finset (Lane n)) : SetPartition n := by
  classical
  exact Finpartition.ofSetoid (sameSide S)

private theorem mem_regions {S : Finset (Lane n)} {x y : Fin n} :
    x ∈ (regions S).part y ↔ ∀ a ∈ S, gap a.1 a.2 y ↔ gap a.1 a.2 x := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

private theorem nc_regions (S : Finset (Lane n)) : IsNoncrossing (regions S) := by
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
  have sides {x y : Fin n} := (mem_block_iff (regions S) x y).symm.trans mem_regions
  apply hne
  apply sides.mpr
  intro ⟨i, j⟩ h
  have h₁ := sides.mp hac (i, j) h
  have h₂ := sides.mp hbd (i, j) h
  simp only [gap] at h₁ h₂ ⊢
  split_ifs at h₁ h₂ ⊢ <;> omega

private theorem lanes_regions {S : Finset (Lane n)} (hS : IsMaximalSetOfLanes univ S) :
    lanes (regions S) = S := by
  have hsub : S ⊆ lanes (regions S) := by
    rintro ⟨i, j⟩ hij
    apply mem_lanes.mpr
    constructor
    · apply mem_regions.mpr
      rintro ⟨k, l⟩ hkl
      by_cases h : (k, l) = (i, j)
      · cases h
        simp [gap_left, gap_right]
      have hd := hS.2.1 _ hkl _ hij h
      have hk : k ≠ i := fun e => hd (Or.inl e)
      have hl : l ≠ j := fun e => hd (Or.inr (Or.inl e))
      exact not_not.mp (fun hn => hd ((meet_iff hk hl).mpr hn))
    · intro x hx
      exact fun hg => gap_left i j ((mem_regions.mp hx (i, j) hij).mpr hg)
  apply Subset.antisymm _ hsub
  intro a ha
  by_contra hn
  obtain ⟨b, hb, hm⟩ := hS.2.2 a (mem_univ _) hn
  exact independent (nc_regions S) a ha b (hsub hb) (fun h => hn (h ▸ hb)) hm

-- Following predecessors from any point of a block down to its least element recovers the
-- block. In particular the lane set determines the original partition even if it crosses.
private theorem constant_on_block {P : SetPartition n} {α : Type*} {f : Fin n → α}
    (hf : ∀ i j, (i, j) ∈ lanes P → f i = f j) {x y : Fin n}
    (hxy : P.part x = P.part y) : f x = f y := by
  let B := P.part x
  have hB : B.Nonempty := ⟨x, mem_part_self P x⟩
  let m := B.min' hB
  have hm : m ∈ B := B.min'_mem hB
  have descend (v : Fin n) (hv : v ∈ B) : f v = f m := by
    induction v using WellFoundedLT.induction with
    | ind v ih =>
      by_cases hvm : v = m
      · rw [hvm]
      have hmv : m < v := lt_of_le_of_ne (B.min'_le v hv) (Ne.symm hvm)
      have hvB : P.part v = B := (mem_block_iff P v x).mp hv
      obtain ⟨j, hj⟩ := exists_lane P v
      obtain ⟨hjv, hg⟩ := mem_lanes.mp hj
      have h := hg m (hvB ▸ hm)
      have hjlt : j < v := by unfold gap at h; split at h <;> omega
      exact (hf v j hj).trans (ih j hjlt (hvB ▸ hjv))
  exact (descend x (mem_part_self P x)).trans
    (descend y ((mem_block_iff P y x).mpr hxy.symm)).symm

private theorem lanes_injective : Function.Injective (lanes (n := n)) := by
  have refineBlock {P Q : SetPartition n} (he : lanes P = lanes Q) {x y : Fin n}
      (hxy : P.part x = P.part y) : Q.part x = Q.part y := by
    apply constant_on_block (P := P) (f := Q.part) _ hxy
    intro i j h
    exact ((mem_block_iff Q j i).mp (mem_lanes.mp (he ▸ h)).1).symm
  intro P Q h
  have hpart (x : Fin n) : P.part x = Q.part x := by
    ext y
    rw [mem_block_iff, mem_block_iff]
    exact ⟨refineBlock h, refineBlock h.symm⟩
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB hx, hpart]
    exact part_mem_parts _ _
  · intro hB
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB hx, ← hpart]
    exact part_mem_parts _ _

private theorem maximal_iff (P : SetPartition n) :
    IsMaximalSetOfLanes univ (lanes P) ↔ IsNoncrossing P := by
  refine ⟨fun h => ?_, maximal⟩
  exact lanes_injective (lanes_regions h) ▸ nc_regions (lanes P)

private theorem loop_iff (P : SetPartition n) (i : Fin n) :
    (i, i) ∈ lanes P ↔ P.part i = {i} := by
  rw [mem_lanes]
  simp only [mem_part_self, true_and, gap_loop, not_not]
  exact ⟨fun h => Subset.antisymm (fun x hx => mem_singleton.mpr (h x hx))
    (singleton_subset_iff.mpr (mem_part_self P i)), fun h x hx => mem_singleton.mp (h ▸ hx)⟩

-- Tag the two selected blocks alike and give all remaining blocks their original labels.
private noncomputable def merge (P : SetPartition n) (i j : Fin n) : SetPartition n := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker fun x =>
    if x ∈ P.part i ∨ x ∈ P.part j then none else some (P.part x))

private theorem mem_merge (P : SetPartition n) (i j x y : Fin n) :
    x ∈ (merge P i j).part y ↔ mergedSameBlock P i j x y := by
  classical
  unfold merge
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  simp only [Setoid.ker_def, mergedSameBlock, mem_block_iff]
  split_ifs <;> simp_all <;> grind

private theorem nc_merge (P : SetPartition n) (i j : Fin n) :
    IsNoncrossing (merge P i j) ↔ ¬ mergedHasCrossing P i j := by
  simp only [IsNoncrossing, HasCrossing, mergedHasCrossing, ne_eq, ← mem_block_iff, mem_merge]

private theorem lane_at_pair {P : SetPartition n} {i j : Fin n} (hp : P.part i = {i, j}) :
    (i, j) ∈ lanes P := by
  simp [mem_lanes, hp, gap_left, gap_right]

private theorem target_iff {P : SetPartition n} {i j : Fin n} (h : (i, j) ∈ lanes P) (k : Fin n) :
    (i, k) ∈ lanes P ↔ k = j :=
  ⟨fun hk => unique_exit hk h, fun e => e ▸ h⟩

private def exchange (S : Finset (Lane n)) (i j : Fin n) : Finset (Lane n) :=
  insert (i, j) (insert (j, i) ((S.erase (i, i)).erase (j, j)))

private theorem lanes_merge {P : SetPartition n} {i j : Fin n} (hij : i ≠ j)
    (hi : P.part i = {i}) (hj : P.part j = {j}) :
    lanes (merge P i j) = exchange (lanes P) i j := by
  let Q := merge P i j
  have memQ (x k : Fin n) : x ∈ Q.part k ↔
      x ∈ P.part k ∨ ((x = i ∨ x = j) ∧ (k = i ∨ k = j)) := by
    simp only [Q, mem_merge, mergedSameBlock, ← mem_block_iff, hi, hj, mem_singleton]
  have hQi : Q.part i = {i, j} := by ext x; simp [memQ, hi]
  have hQj : Q.part j = {j, i} := by ext x; simp [memQ, hj]; tauto
  have hi' := target_iff ((loop_iff P i).mpr hi)
  have hj' := target_iff ((loop_iff P j).mpr hj)
  have hi'' := target_iff (lane_at_pair hQi)
  have hj'' := target_iff (lane_at_pair hQj)
  change lanes Q = _
  ext ⟨k, l⟩
  simp only [exchange, mem_insert, mem_erase, Prod.mk.injEq]
  by_cases hki : k = i
  · subst k
    simp [hi', hi'', hij]
  by_cases hkj : k = j
  · subst k
    simp [hj', hj'', hki]
  have heq : Q.part k = P.part k := by ext x; simp [memQ, hki, hkj]
  simp [mem_lanes, heq, hki, hkj]

private theorem absolute_iff {P : SetPartition n} (hnc : IsNoncrossing P) :
    IsAbsoluteMaximalSetOfLanes (lanes P) ↔ ¬ IsMarriageableSingles P := by
  rw [IsAbsoluteMaximalSetOfLanes, and_iff_right (maximal hnc)]
  apply not_congr
  unfold IsMarriageableSingles
  apply exists_congr
  intro i
  apply exists_congr
  intro j
  simp only [loop_iff]
  refine and_congr_right fun hij => and_congr_right fun hi => and_congr_right fun hj => ?_
  change IsMaximalSetOfLanes univ (exchange (lanes P) i j) ↔ _
  rw [← lanes_merge hij hi hj, maximal_iff, nc_merge]

-- Restrict the partition–lane bijection to corresponding predicates on the two sides.
private theorem card_lanes_filter {Q : SetPartition n → Prop} {R : Finset (Lane n) → Prop}
    [DecidablePred Q] [DecidablePred R] (hmax : ∀ S, R S → IsMaximalSetOfLanes univ S)
    (hfilter : ∀ P, IsNoncrossing P → (R (lanes P) ↔ Q P)) :
    (univ.filter R).card = (univ.filter fun P : _root_.NoncrossingPartition n => Q P.val).card := by
  symm
  apply Finset.card_bij (fun P _ => lanes P.val)
  · intro P hP
    exact mem_filter.mpr ⟨mem_univ _, (hfilter P.val P.2).mpr (mem_filter.mp hP).2⟩
  · intro P _ P' _ h
    exact Subtype.ext (lanes_injective h)
  · intro S hS
    have h := (mem_filter.mp hS).2
    have he := lanes_regions (hmax S h)
    refine ⟨⟨regions S, nc_regions S⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, he⟩
    exact (hfilter _ (nc_regions S)).mp (by rwa [he])

-- A lane joins its even entry position and its odd exit position, in either order.
private def Joins (S : Finset (Lane n)) (a b : ℕ) : Prop :=
  ∃ i j : Fin n, (i, j) ∈ S ∧
    ((a = 2 * i.val ∧ b = 2 * j.val + 1) ∨ (a = 2 * j.val + 1 ∧ b = 2 * i.val))

private theorem joins_symm {S : Finset (Lane n)} {a b : ℕ} (h : Joins S a b) : Joins S b a := by
  obtain ⟨i, j, hij, h | h⟩ := h
  · exact ⟨i, j, hij, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨i, j, hij, Or.inl ⟨h.2, h.1⟩⟩

private theorem joins_unique {P : SetPartition n} {a b c : ℕ}
    (hb : Joins (lanes P) a b) (hc : Joins (lanes P) a c) : b = c := by
  obtain ⟨i, j, hij, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := hb <;>
    obtain ⟨k, l, hkl, ⟨ha', hc⟩ | ⟨ha', hc⟩⟩ := hc
  · have hik : i = k := Fin.ext (by omega)
    subst k
    rw [hb, hc, unique_exit hij hkl]
  · omega
  · omega
  · have hjl : j = l := Fin.ext (by omega)
    subst l
    rw [hb, hc, unique_entry hij hkl]

-- Following the lane incident to each point gives a noncrossing perfect matching.
private noncomputable def partitionMatching (P : _root_.NoncrossingPartition n) :
    {f : NCMatching (2 * n) // ∀ a < 2 * n, Joins (lanes P.val) a (f.val a)} := by
  let exit (i : Fin n) := Classical.choose (exists_lane P.val i)
  have hExit (i : Fin n) : (i, exit i) ∈ lanes P.val := Classical.choose_spec (exists_lane P.val i)
  have hSurj : Function.Surjective exit :=
    Finite.surjective_of_injective fun i k h => unique_entry (hExit i) (h ▸ hExit k)
  have hasMate (a : ℕ) (ha : a < 2 * n) : ∃ b, Joins (lanes P.val) a b := by
    let v : Fin n := ⟨a / 2, by omega⟩
    by_cases h : a % 2 = 0
    · exact ⟨_, v, exit v, hExit v, Or.inl ⟨by dsimp [v]; omega, rfl⟩⟩
    · obtain ⟨i, hi⟩ := hSurj v
      exact ⟨_, i, v, hi ▸ hExit i, Or.inr ⟨by dsimp [v]; omega, rfl⟩⟩
  let f (a : ℕ) : ℕ := if ha : a < 2 * n then Classical.choose (hasMate a ha) else a
  have hJoin (a : ℕ) (ha : a < 2 * n) : Joins (lanes P.val) a (f a) := by
    simpa only [f, dite_eq_left ha] using Classical.choose_spec (hasMate a ha)
  have hLt (a : ℕ) (ha : a < 2 * n) : f a < 2 * n := by
    obtain ⟨i, j, _, ⟨_, h⟩ | ⟨_, h⟩⟩ := hJoin a ha <;> omega
  refine ⟨⟨f, hLt, ?_, ?_, ?_, ?_⟩, hJoin⟩
  · intro a ha
    obtain ⟨i, j, _, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := hJoin a ha <;> omega
  · intro a ha
    exact joins_unique (hJoin (f a) (hLt a ha)) (joins_symm (hJoin a ha))
  · intro a b hab hbfa
    have ha : a < 2 * n := by
      by_contra! h
      simp only [f, dite_eq_right (Nat.not_lt.mpr h)] at hbfa
      omega
    have hb := hbfa.trans (hLt a ha)
    obtain ⟨i, j, hij, ⟨ha', hfa⟩ | ⟨ha', hfa⟩⟩ := hJoin a ha <;>
      obtain ⟨k, l, hkl, ⟨hb', hfb⟩ | ⟨hb', hfb⟩⟩ := hJoin b hb
    all_goals
      have hne : (i, j) ≠ (k, l) := by
        simp only [ne_eq, Prod.mk.injEq]
        rintro ⟨rfl, rfl⟩
        omega
      have h := independent P.2 _ hij _ hkl hne
      simp only [lanesMeet, not_or] at h
      have h := h.2.2
      omega
  · intro a ha
    exact dite_eq_right (Nat.not_lt.mpr ha)

-- The points strictly inside an arc are paired with one another, so there are evenly many.
private theorem matching_parity {N : ℕ} {f : ℕ → ℕ} (hf : IsNCMatching N f) {a : ℕ}
    (ha : a < N) : f a % 2 ≠ a % 2 := by
  have parity_of_lt (i : ℕ) (hi : i < N) (hif : i < f i) : f i % 2 ≠ i % 2 := by
    have hin (j : ℕ) (hj : j ∈ Ioo i (f i)) : j < N := (mem_Ioo.mp hj).2.trans (hf.lt i hi)
    have he := Finset.even_card_of_involution (s := Ioo i (f i)) (f := f)
      (fun j hj => mem_Ioo.mpr (hf.nested i j (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2))
      (fun j hj => hf.invol j (hin j hj)) (fun j hj => hf.ne j (hin j hj))
    rw [Nat.card_Ioo] at he
    obtain ⟨k, hk⟩ := he
    omega
  rcases lt_or_gt_of_ne (hf.ne a ha) with h | h
  · have hp := parity_of_lt (f a) (hf.lt a ha) (by rwa [hf.invol a ha])
    rw [hf.invol a ha] at hp
    exact hp.symm
  · exact parity_of_lt a ha h

private def matchingLanes (f : NCMatching (2 * n)) : Finset (Lane n) :=
  univ.filter fun (i, j) => f.val (2 * i.val) = 2 * j.val + 1

private theorem joins_matchingLanes_iff (f : NCMatching (2 * n)) {a b : ℕ} (ha : a < 2 * n) :
    Joins (matchingLanes f) a b ↔ f.val a = b := by
  constructor
  · rintro ⟨i, j, hij, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (mem_filter.mp hij).2
    · rw [← (mem_filter.mp hij).2]
      exact f.2.invol _ (by omega)
  · intro hab
    have even_join {x y : ℕ} (hx : x < 2 * n) (hy : y < 2 * n) (he : x % 2 = 0)
        (ho : y % 2 = 1) (hxy : f.val x = y) : Joins (matchingLanes f) x y := by
      let i : Fin n := ⟨x / 2, by omega⟩
      let j : Fin n := ⟨y / 2, by omega⟩
      have hi : x = 2 * i.val := by dsimp [i]; omega
      have hj : y = 2 * j.val + 1 := by dsimp [j]; omega
      refine ⟨i, j, mem_filter.mpr ⟨mem_univ _, ?_⟩, Or.inl ⟨hi, hj⟩⟩
      change f.val (2 * i.val) = 2 * j.val + 1
      rwa [← hi, ← hj]
    have hb := hab ▸ f.2.lt a ha
    have hp := matching_parity f.2 ha
    rw [hab] at hp
    by_cases h : a % 2 = 0
    · exact even_join ha hb h (by omega) hab
    · exact joins_symm (even_join hb ha (by omega) (by omega) (hab ▸ f.2.invol a ha))

private theorem matchingLanes_maximal (f : NCMatching (2 * n)) :
    IsMaximalSetOfLanes univ (matchingLanes f) := by
  refine ⟨subset_univ _, ?_, ?_⟩
  · rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl hne
    have hij' : f.val (2 * i.val) = 2 * j.val + 1 := (mem_filter.mp hij).2
    have hkl' : f.val (2 * k.val) = 2 * l.val + 1 := (mem_filter.mp hkl).2
    have hji : f.val (2 * j.val + 1) = 2 * i.val := hij' ▸ f.2.invol _ (by omega)
    have hlk : f.val (2 * l.val + 1) = 2 * k.val := hkl' ▸ f.2.invol _ (by omega)
    rintro (h | h | h)
    · change i = k at h
      subst k
      have hjl : j = l := Fin.ext (by omega)
      exact hne (Prod.ext rfl hjl)
    · change j = l at h
      subst l
      have hik : i = k := Fin.ext (by omega)
      exact hne (Prod.ext hik rfl)
    · let lo := min (2 * i.val) (2 * j.val + 1)
      let hi := max (2 * i.val) (2 * j.val + 1)
      have hmate : f.val lo = hi := by
        dsimp [lo, hi]
        rcases le_total (2 * i.val) (2 * j.val + 1) with hle | hle
        · simpa only [min_eq_left hle, max_eq_right hle] using hij'
        · simpa only [min_eq_right hle, max_eq_left hle] using hji
      have hinside (x : ℕ) (hx : lo < x ∧ x < hi) : lo < f.val x ∧ f.val x < hi := by
        rw [← hmate] at hx ⊢
        exact f.2.nested lo x hx.1 hx.2
      change (lo < 2 * k.val ∧ 2 * k.val < hi) ↔ ¬ (lo < 2 * l.val + 1 ∧ 2 * l.val + 1 < hi) at h
      have hsame : (lo < 2 * k.val ∧ 2 * k.val < hi) ↔
          (lo < 2 * l.val + 1 ∧ 2 * l.val + 1 < hi) :=
        ⟨fun hx => by simpa only [hkl'] using hinside (2 * k.val) hx,
          fun hx => by simpa only [hlk] using hinside (2 * l.val + 1) hx⟩
      tauto
  · rintro ⟨i, j⟩ - -
    obtain ⟨k, l, hkl, ⟨h, _⟩ | ⟨h, _⟩⟩ :=
      (joins_matchingLanes_iff f (a := 2 * i.val) (by omega)).mpr rfl
    · exact ⟨(k, l), hkl, Or.inl (show i = k from Fin.ext (by omega))⟩
    · omega

private noncomputable def matchingEquivLanes (n : ℕ) :
    NCMatching (2 * n) ≃ {S : Finset (Lane n) // IsMaximalSetOfLanes univ S} := by
  refine Equiv.ofBijective (fun f => ⟨matchingLanes f, matchingLanes_maximal f⟩) ⟨?_, ?_⟩
  · intro f g h
    have hLanes : matchingLanes f = matchingLanes g := congrArg Subtype.val h
    apply Subtype.ext
    funext a
    by_cases ha : a < 2 * n
    · have hJoin := (joins_matchingLanes_iff f (b := f.val a) ha).mpr rfl
      rw [hLanes] at hJoin
      exact ((joins_matchingLanes_iff g ha).mp hJoin).symm
    · rw [f.2.fix a (Nat.not_lt.mp ha), g.2.fix a (Nat.not_lt.mp ha)]
  · intro S
    let P : _root_.NoncrossingPartition n := ⟨regions S.val, nc_regions S.val⟩
    let f := partitionMatching P
    refine ⟨f.val, Subtype.ext ?_⟩
    have hS : lanes P.val = S.val := lanes_regions S.2
    rw [← hS]
    ext ⟨i, j⟩
    have ha : 2 * i.val < 2 * n := by omega
    refine ⟨?_, ?_⟩
    · intro hij
      have h : f.val.val (2 * i.val) = 2 * j.val + 1 := (mem_filter.mp hij).2
      obtain ⟨k, l, hkl, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := f.2 (2 * i.val) ha
      · have hik : i = k := Fin.ext (by omega)
        have hjl : j = l := Fin.ext (by omega)
        simpa only [hik, hjl] using hkl
      · omega
    · intro hij
      exact mem_filter.mpr ⟨mem_univ _,
        joins_unique (f.2 (2 * i.val) ha) ⟨i, j, hij, Or.inl ⟨rfl, rfl⟩⟩⟩

end card_absolute_maximalSetsOfLanes

open card_absolute_maximalSetsOfLanes in
open Finset NoncrossingPartition in
/-- **Maximal sets of lanes and noncrossing partitions.** For every $n \ge 0$, the maximal sets of
lanes of the standard road intersection of size $n$, in which every lane is allowed, are in
bijection with the noncrossing partitions of $\{0, \dots, n-1\}$, and their number is the Catalan
number $C_n$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Lemma 16
(`jis-2025-25.1.1-lem-16`). -/
public theorem maximalSetsOfLanes_equiv_noncrossingPartition (n : ℕ) :
    Nonempty ({S : Finset (Fin n × Fin n) // IsMaximalSetOfLanes Finset.univ S} ≃
      _root_.NoncrossingPartition n) ∧
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) =>
      IsMaximalSetOfLanes Finset.univ S).card = catalan n := by
  constructor
  · refine ⟨{ toFun := fun S => ⟨regions S.val, nc_regions S.val⟩
              invFun := fun P => ⟨lanes P.val, maximal P.2⟩
              left_inv := fun S => Subtype.ext (lanes_regions S.2)
              right_inv := fun P => Subtype.ext (lanes_injective (lanes_regions (maximal P.2))) }⟩
  · rw [← Fintype.card_subtype, Fintype.card_eq_nat_card,
      ← Nat.card_congr (matchingEquivLanes n), card_ncMatching]
    simp

open card_absolute_maximalSetsOfLanes in
/-- **Absolute maximal sets of lanes are counted by lonely singles partitions.** For every
$n \ge 0$, the number of absolute maximal sets of lanes of the standard road intersection of
size $n$ equals $L_n$, the number of noncrossing partitions of $\{0, \dots, n-1\}$ that are not
marriageable singles partitions.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 18
(`jis-2025-25.1.1-cor-18`). -/
public theorem card_absolute_maximalSetsOfLanes (n : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) => IsAbsoluteMaximalSetOfLanes S).card =
      lonelySinglesCount n := by
  unfold lonelySinglesCount
  apply card_lanes_filter (Q := fun P => ¬ IsMarriageableSingles P)
  · exact fun _ h => h.1
  · exact fun _ hnc => absolute_iff hnc

open card_absolute_maximalSetsOfLanes in
/-- **Nonabsolute maximal sets of lanes are counted by marriageable singles partitions.** For
every $n \ge 0$, the number of maximal sets of lanes of the standard road intersection of size $n$
that are not absolute equals $M_n$, the number of noncrossing partitions of $\{0, \dots, n-1\}$
that are marriageable singles partitions.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 17
(`jis-2025-25.1.1-cor-17`). -/
public theorem card_nonabsolute_maximalSetsOfLanes (n : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) =>
      IsMaximalSetOfLanes Finset.univ S ∧ ¬ IsAbsoluteMaximalSetOfLanes S).card =
      marriageableSinglesCount n := by
  unfold marriageableSinglesCount
  apply card_lanes_filter
  · exact fun _ h => h.1
  · intro P hnc
    rw [and_iff_right (maximal hnc), absolute_iff hnc, not_not]

end MetaMathlibExt
