/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Sort
import MathlibExt.Combinatorics.Enumerative.BellStirlingSum

/-!
# Colored partitions with different sizes and colors

The cardinality formula sums over distinct-size partitions and counts valid colorings
by assigning colors in increasing order of part size. For bounded sizes, adding the largest
size gives a Stirling recurrence for the counts by number of parts.
-/

namespace MetaMathlibExt

open Finset

namespace card_coloredPartitions_fullyDifferent

/-- Form the possible colored-part sets for a list of sizes and a set of already used colors. -/
private def colorings : List ℕ → Finset ℕ → Finset (Finset (ℕ × ℕ))
  | [], _ => {∅}
  | m :: ms, used =>
    (Icc 1 m \ used).biUnion fun j => (colorings ms (insert j used)).image (insert (m, j))

private lemma size_mem {ms : List ℕ} {T : Finset (ℕ × ℕ)}
    (hsizes : T.image Prod.fst = ms.toFinset) {p : ℕ × ℕ} (hp : p ∈ T) : p.1 ∈ ms := by
  simpa [hsizes] using mem_image_of_mem Prod.fst hp

/-- For distinct sizes, a coloring uses each size once and each allowed color at most once. -/
private lemma mem_colorings {ms : List ℕ} (hms : ms.Nodup)
    {used : Finset ℕ} {T : Finset (ℕ × ℕ)} :
    T ∈ colorings ms used ↔
      T.image Prod.fst = ms.toFinset ∧
      Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) ∧ Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) ∧
      ∀ p ∈ T, 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.2 ∉ used := by
  induction ms generalizing T used with
  | nil =>
    simp only [colorings, mem_singleton, List.toFinset_nil, image_eq_empty]
    exact ⟨by rintro rfl; simp, And.left⟩
  | cons m ms ih =>
    obtain ⟨hm, hms⟩ := List.nodup_cons.mp hms
    simp only [colorings, mem_biUnion, mem_sdiff, mem_Icc, mem_image, List.toFinset_cons]
    constructor
    · rintro ⟨j, ⟨hj, hjused⟩, U, hU, rfl⟩
      obtain ⟨hsizes, hinjSize, hinjColor, hbounds⟩ := (ih hms).mp hU
      have hsize (p : ℕ × ℕ) (hp : p ∈ U) : m ≠ p.1 :=
        fun h => hm (h.symm ▸ size_mem hsizes hp)
      have hcolor (p : ℕ × ℕ) (hp : p ∈ U) : j ≠ p.2 :=
        fun h => (hbounds p hp).2.2 (h ▸ mem_insert_self j used)
      refine ⟨by rw [image_insert, hsizes], ?_, ?_, ?_⟩
      · rw [coe_insert, Set.injOn_insert (fun hp => hsize (m, j) hp rfl)]
        exact ⟨hinjSize, fun ⟨p, hp, h⟩ => hsize p hp h.symm⟩
      · rw [coe_insert, Set.injOn_insert (fun hp => hcolor (m, j) hp rfl)]
        exact ⟨hinjColor, fun ⟨p, hp, h⟩ => hcolor p hp h.symm⟩
      · intro p hp
        rcases mem_insert.mp hp with rfl | hp
        · exact ⟨hj.1, hj.2, hjused⟩
        · obtain ⟨h₁, h₂, h₃⟩ := hbounds p hp
          exact ⟨h₁, h₂, fun h => h₃ (mem_insert_of_mem h)⟩
    · rintro ⟨hsizes, hinjSize, hinjColor, hbounds⟩
      have hmem : m ∈ T.image Prod.fst := hsizes ▸ mem_insert_self m ms.toFinset
      obtain ⟨⟨q, j⟩, hp, (heq : q = m)⟩ := Finset.mem_image.mp hmem
      subst q
      obtain ⟨hj₁, hj₂, hjused⟩ := hbounds (m, j) hp
      refine ⟨j, ⟨⟨hj₁, hj₂⟩, hjused⟩, T.erase (m, j), (ih hms).mpr ?_,
        insert_erase hp⟩
      refine ⟨?_, hinjSize.mono (erase_subset _ _), hinjColor.mono (erase_subset _ _), ?_⟩
      · ext k
        rw [Finset.mem_image]
        constructor
        · rintro ⟨p, h, rfl⟩
          obtain ⟨hne, hT⟩ := mem_erase.mp h
          have hk : p.1 ∈ insert m ms.toFinset := hsizes ▸ mem_image_of_mem Prod.fst hT
          exact (mem_insert.mp hk).resolve_left fun h => hne (hinjSize hT hp h)
        · intro hk
          have hkT : k ∈ T.image Prod.fst := hsizes ▸ mem_insert_of_mem hk
          obtain ⟨p, hT, rfl⟩ := Finset.mem_image.mp hkT
          exact ⟨p, mem_erase.mpr ⟨fun h => hm (by simpa [h] using hk), hT⟩, rfl⟩
      · intro p h
        obtain ⟨hne, hT⟩ := mem_erase.mp h
        obtain ⟨h₁, h₂, h₃⟩ := hbounds p hT
        exact ⟨h₁, h₂, fun hj => (mem_insert.mp hj).elim
          (fun h => hne (hinjColor hT hp h)) h₃⟩

/-- Each earlier color is in the range of every remaining part size. -/
private lemma card_colorings {ms : List ℕ} (hms : ms.Pairwise (· < ·))
    {used : Finset ℕ} (hused : ∀ m ∈ ms, used ⊆ Icc 1 m) :
    (colorings ms used).card = (ms.mapIdx fun i m => m - (used.card + i)).prod := by
  induction ms generalizing used with
  | nil => simp [colorings]
  | cons m ms ih =>
    obtain ⟨hlt, hms⟩ := List.pairwise_cons.mp hms
    have hn : ms.Nodup := hms.imp (fun h => ne_of_lt h)
    have hm : m ∉ ms := fun h => (lt_irrefl m) (hlt m h)
    have hnotMem (j : ℕ) {U : Finset (ℕ × ℕ)} (hU : U ∈ colorings ms (insert j used)) :
        ∀ p ∈ U, p.1 ≠ m := fun p hp h =>
      hm (h ▸ size_mem ((mem_colorings hn).mp hU).1 hp)
    rw [colorings, card_biUnion]
    · rw [List.mapIdx_cons, List.prod_cons]
      simp only [Nat.add_zero]
      calc
        _ = ∑ _j ∈ Icc 1 m \ used,
            (ms.mapIdx fun i q => q - (used.card + (i + 1))).prod := by
          refine sum_congr rfl fun j hj => ?_
          obtain ⟨hj, hjused⟩ := mem_sdiff.mp hj
          have hi : ∀ q ∈ ms, insert j used ⊆ Icc 1 q := by
            intro q hq
            refine insert_subset ?_ (hused q (List.mem_cons_of_mem m hq))
            obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
            exact mem_Icc.mpr ⟨hj₁, hj₂.trans (hlt q hq).le⟩
          rw [card_image_of_injOn, ih hms hi, card_insert_of_notMem hjused]
          · simp only [Nat.add_right_comm used.card 1, Nat.add_assoc]
          · intro A hA B hB heq
            have ha := hnotMem j hA (m, j)
            have hb := hnotMem j hB (m, j)
            rw [← erase_insert (fun h => ha h rfl), heq, erase_insert (fun h => hb h rfl)]
        _ = _ := by
          rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset (hused m (by simp)), Nat.card_Icc]
          simp
    · intro j _ k _ hjk
      simp only [Function.onFun, Finset.disjoint_left]
      intro T hj hk
      obtain ⟨A, hA, rfl⟩ := mem_image.mp hj
      obtain ⟨B, hB, heq⟩ := mem_image.mp hk
      have hmem : (m, j) ∈ insert (m, k) B := heq.symm ▸ mem_insert_self (m, j) A
      rcases mem_insert.mp hmem with h | h
      · exact hjk (congrArg Prod.snd h)
      · exact hnotMem k hB _ h rfl

private lemma sorted_parts {n : ℕ} {μ : Nat.Partition n} (hμ : μ ∈ Nat.Partition.distincts n) :
    (μ.parts.sort (· ≤ ·)).Pairwise (· < ·) := by
  have hn : (μ.parts.sort (· ≤ ·)).Nodup := by
    have h : μ.parts.Nodup := (mem_filter.mp hμ).2
    simpa only [← Multiset.coe_nodup, Multiset.sort_eq] using h
  exact ((μ.parts.pairwise_sort (· ≤ ·)).sortedLE.sortedLT_of_nodup hn).pairwise

private lemma toFinset_sort (s : Multiset ℕ) :
    (s.sort (· ≤ ·)).toFinset = s.toFinset := by
  ext m
  simp

end card_coloredPartitions_fullyDifferent

open card_coloredPartitions_fullyDifferent

/-- **Formula for colored partitions into fully different parts.** A colored part is a pair
$(m, j)$ of integers with $1 \le j \le m$, read as the part $m$ in color $j$. For $n \ge 0$, let
$\mathrm{pf}_c(n)$ be the number of finite sets of colored parts whose sizes $m$ sum to $n$ and
in which no two colored parts have the same size and no two have the same color. Then
$\mathrm{pf}_c(n)$ is the sum, over all partitions of $n$ into distinct parts
$p_1 > p_2 > \cdots > p_k$, of the product $p_k (p_{k-1} - 1) \cdots (p_1 - (k - 1))$.

The identity is stated for all $n \ge 0$; at $n = 0$ both sides equal $1$, while the paper states
it for $n \ge 1$.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 2 (`integers-2026-A20-thm-2`). -/
public theorem card_coloredPartitions_fullyDifferent (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => ∑ x ∈ T, x.1 = n ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card)).card =
      ∑ μ ∈ Nat.Partition.distincts n,
        ((μ.parts.sort (· ≤ ·)).mapIdx fun i q => q - i).prod := by
  let board := (Icc 1 n ×ˢ Icc 1 n).filter fun x : ℕ × ℕ => x.2 ≤ x.1
  let colors (μ : Nat.Partition n) := colorings (μ.parts.sort (· ≤ ·)) ∅
  have hcolors {μ : Nat.Partition n} (hμ : μ ∈ Nat.Partition.distincts n) {T} :
      T ∈ colors μ ↔
        T.image Prod.fst = μ.parts.toFinset ∧
        Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) ∧ Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) ∧
        ∀ p ∈ T, 1 ≤ p.2 ∧ p.2 ≤ p.1 := by
    simp only [colors, mem_colorings ((sorted_parts hμ).imp fun h => ne_of_lt h),
      toFinset_sort, notMem_empty, not_false_eq_true, and_true]
  have hdisjoint :
      (↑(Nat.Partition.distincts n) : Set (Nat.Partition n)).PairwiseDisjoint colors := by
    intro μ hμ ν hν hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro T hTμ hTν
    apply hne
    exact Nat.Partition.ext (Multiset.Nodup.toFinset_inj
      (mem_filter.mp hμ).2 (mem_filter.mp hν).2
      (((hcolors hμ).mp hTμ).1.symm.trans ((hcolors hν).mp hTν).1))
  have hsum {T : Finset (ℕ × ℕ)} (hT : Set.InjOn Prod.fst (T : Set (ℕ × ℕ))) :
      (T.image Prod.fst).val.sum = ∑ x ∈ T, x.1 := by
    calc
      _ = ∑ m ∈ T.image Prod.fst, id m := by
        simp only [Finset.sum_eq_multiset_sum, Multiset.map_id]
      _ = _ := sum_image (f := id) hT
  have heq : (board.powerset.filter fun T =>
      ∑ x ∈ T, x.1 = n ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card) = (Nat.Partition.distincts n).biUnion colors := by
    ext T
    simp only [mem_filter, mem_powerset, card_image_iff, mem_biUnion]
    constructor
    · rintro ⟨hboard, htotal, hSize, hColor⟩
      let μ : Nat.Partition n :=
        ⟨(T.image Prod.fst).val, fun {m} hm => by
          obtain ⟨p, hp, rfl⟩ := mem_image.mp (mem_val.mp hm)
          exact (mem_Icc.mp (mem_product.mp (mem_filter.mp (hboard hp)).1).1).1,
          (hsum hSize).trans htotal⟩
      have hμ : μ ∈ Nat.Partition.distincts n :=
        mem_filter.mpr ⟨mem_univ _, (T.image Prod.fst).nodup⟩
      refine ⟨μ, hμ, (hcolors hμ).mpr ⟨(Finset.val_toFinset _).symm, hSize, hColor, ?_⟩⟩
      intro p hp
      obtain ⟨hp, hj⟩ := mem_filter.mp (hboard hp)
      exact ⟨(mem_Icc.mp (mem_product.mp hp).2).1, hj⟩
    · rintro ⟨μ, hμ, hT⟩
      obtain ⟨hsizes, hSize, hColor, hbounds⟩ := (hcolors hμ).mp hT
      refine ⟨?_, ?_, hSize, hColor⟩
      · intro p hp
        obtain ⟨hj, hjm⟩ := hbounds p hp
        have hm : p.1 ∈ μ.parts := by
          simpa [hsizes] using mem_image_of_mem Prod.fst hp
        have hmn := μ.le_of_mem_parts hm
        exact mem_filter.mpr
          ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hj.trans hjm, hmn⟩,
            mem_Icc.mpr ⟨hj, hjm.trans hmn⟩⟩, hjm⟩
      · rw [← hsum hSize, hsizes,
          Multiset.toFinset_eq (mem_filter.mp hμ).2 |>.symm]
        exact μ.parts_sum
  change (board.powerset.filter _).card = _
  rw [heq, card_biUnion hdisjoint]
  refine sum_congr rfl fun μ hμ => ?_
  simpa [colors] using card_colorings (sorted_parts hμ) (used := ∅) (by simp)

namespace card_coloredPartitions_fullyDifferent_le

/-- All placements on the triangular board, including the empty placement. -/
private def placements (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (((Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ => p.2 ≤ p.1)).powerset.filter
    fun T => (T.image Prod.fst).card = T.card ∧ (T.image Prod.snd).card = T.card)

private lemma mem_placements {n : ℕ} {T : Finset (ℕ × ℕ)} :
    T ∈ placements n ↔
      (∀ p ∈ T, 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ n) ∧
        Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) ∧ Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) := by
  simp only [placements, mem_filter, mem_powerset, card_image_iff]
  refine and_congr_left' ?_
  change (∀ ⦃p : ℕ × ℕ⦄, p ∈ T → _) ↔ _
  simp only [mem_filter, mem_product, mem_Icc]
  constructor
  · intro h p hp
    exact ⟨(h hp).1.2.1, (h hp).2, (h hp).1.1.2⟩
  · intro h p hp
    obtain ⟨h₁, h₂, h₃⟩ := h p hp
    exact ⟨⟨⟨h₁.trans h₂, h₃⟩, ⟨h₁, h₂.trans h₃⟩⟩, h₂⟩

private lemma empty_mem_placements (n : ℕ) : ∅ ∈ placements n := by
  simp [placements]

private lemma card_le_of_mem_placements {n : ℕ} {T : Finset (ℕ × ℕ)}
    (hT : T ∈ placements n) : T.card ≤ n := by
  obtain ⟨hb, hi, _⟩ := mem_placements.mp hT
  have hsub : T.image Prod.fst ⊆ Icc 1 n := by
    rintro m hm
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
    obtain ⟨h₁, h₂, h₃⟩ := hb p hp
    exact mem_Icc.mpr ⟨h₁.trans h₂, h₃⟩
  simpa [card_image_of_injOn hi, Nat.card_Icc] using card_le_card hsub

private def placementsWithCard (n k : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (placements n).filter fun T => T.card = k

private lemma placementsWithCard_zero (n : ℕ) : placementsWithCard n 0 = {∅} := by
  ext T
  simp only [placementsWithCard, mem_filter, card_eq_zero, mem_singleton]
  exact ⟨And.right, fun h => h.symm ▸ ⟨empty_mem_placements n, rfl⟩⟩

private lemma placementsWithCard_eq_empty {n k : ℕ} (hk : n < k) :
    placementsWithCard n k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨hT, hcard⟩ := mem_filter.mp hT
  have hle := card_le_of_mem_placements hT
  exact (not_lt_of_ge (hcard ▸ hle)) hk

private def availableColors (n : ℕ) (T : Finset (ℕ × ℕ)) : Finset ℕ :=
  Icc 1 (n + 1) \ T.image Prod.snd

private def extend (n : ℕ) (T : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (availableColors n T).image fun j => insert (n + 1, j) T

private lemma notMem_last {n : ℕ} {T : Finset (ℕ × ℕ)}
    (hT : T ∈ placements n) (j : ℕ) : (n + 1, j) ∉ T :=
  fun h => (Nat.not_succ_le_self n) ((mem_placements.mp hT).1 _ h).2.2

private lemma insert_last_inj {n j l : ℕ} {T U : Finset (ℕ × ℕ)}
    (hT : T ∈ placements n) (hU : U ∈ placements n)
    (h : insert (n + 1, j) T = insert (n + 1, l) U) : j = l ∧ T = U := by
  have hmem : (n + 1, j) ∈ insert (n + 1, l) U := h ▸ mem_insert_self _ _
  have hjl : j = l := congrArg Prod.snd
    ((mem_insert.mp hmem).resolve_right (notMem_last hU j))
  subst l
  -- Recover the smaller placement by erasing the common last-row pair.
  have he := congrArg (fun V : Finset (ℕ × ℕ) => V.erase (n + 1, j)) h
  rw [erase_insert (notMem_last hT j), erase_insert (notMem_last hU j)] at he
  exact ⟨rfl, he⟩

private lemma insert_mem_placements {n j : ℕ} {T : Finset (ℕ × ℕ)}
    (hT : T ∈ placements n) (hj : j ∈ availableColors n T) :
    insert (n + 1, j) T ∈ placements (n + 1) := by
  obtain ⟨hb, hSize, hColor⟩ := mem_placements.mp hT
  obtain ⟨hj, hjNot⟩ := mem_sdiff.mp hj
  refine mem_placements.mpr ⟨?_, ?_, ?_⟩
  · intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact ⟨(mem_Icc.mp hj).1, (mem_Icc.mp hj).2, le_rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := hb p hp
      exact ⟨h₁, h₂, h₃.trans (Nat.le_succ _)⟩
  · rw [coe_insert, Set.injOn_insert (notMem_last hT j)]
    refine ⟨hSize, ?_⟩
    rintro ⟨p, hp, he⟩
    have hle := (hb p hp).2.2
    change p.1 = n + 1 at he
    rw [he] at hle
    exact Nat.not_succ_le_self n hle
  · rw [coe_insert, Set.injOn_insert (notMem_last hT j)]
    exact ⟨hColor, fun ⟨p, hp, he⟩ => hjNot (mem_image.mpr ⟨p, hp, he⟩)⟩

/-- Separate placements according to whether they use the new, largest size. -/
private lemma placementsWithCard_succ (n k : ℕ) :
    placementsWithCard (n + 1) (k + 1) =
      placementsWithCard n (k + 1) ∪ (placementsWithCard n k).biUnion (extend n) := by
  ext T
  simp only [placementsWithCard, mem_filter, mem_union, mem_biUnion, extend, mem_image]
  constructor
  · rintro ⟨hT, hcard⟩
    obtain ⟨hb, hSize, hColor⟩ := mem_placements.mp hT
    by_cases hlast : ∃ j, (n + 1, j) ∈ T
    · obtain ⟨j, hj⟩ := hlast
      refine Or.inr ⟨T.erase (n + 1, j), ⟨mem_placements.mpr ⟨?_,
        hSize.mono (erase_subset _ _), hColor.mono (erase_subset _ _)⟩,
        Nat.add_right_cancel ((card_erase_add_one hj).trans hcard)⟩,
        j, mem_sdiff.mpr ⟨mem_Icc.mpr ⟨(hb _ hj).1, (hb _ hj).2.1⟩, ?_⟩, insert_erase hj⟩
      · intro p hp
        obtain ⟨hne, hp⟩ := mem_erase.mp hp
        obtain ⟨h₁, h₂, h₃⟩ := hb p hp
        have hne' : p.1 ≠ n + 1 := fun he => hne (hSize hp hj he)
        exact ⟨h₁, h₂, by omega⟩
      · intro hc
        obtain ⟨p, hp, he⟩ := mem_image.mp hc
        obtain ⟨hne, hp⟩ := mem_erase.mp hp
        exact hne (hColor hp hj he)
    · refine Or.inl ⟨mem_placements.mpr ⟨?_, hSize, hColor⟩, hcard⟩
      rintro ⟨m, j⟩ hp
      obtain ⟨h₁, h₂, h₃⟩ := hb _ hp
      have hne : m ≠ n + 1 := fun he => hlast ⟨j, he ▸ hp⟩
      exact ⟨h₁, h₂, by change m ≤ n + 1 at h₃; change m ≤ n; omega⟩
  · rintro (⟨hT, hcard⟩ | ⟨U, ⟨hU, hcard⟩, j, hj, rfl⟩)
    · obtain ⟨hb, hSize, hColor⟩ := mem_placements.mp hT
      exact ⟨mem_placements.mpr ⟨fun p hp =>
        ⟨(hb p hp).1, (hb p hp).2.1, (hb p hp).2.2.trans (Nat.le_succ _)⟩,
        hSize, hColor⟩, hcard⟩
    · exact ⟨insert_mem_placements hU hj, (card_insert_of_notMem (notMem_last hU j)).trans
        (congrArg (· + 1) hcard)⟩

private lemma card_extend {n k : ℕ} {T : Finset (ℕ × ℕ)} (hT : T ∈ placementsWithCard n k) :
    (extend n T).card = n + 1 - k := by
  obtain ⟨hT, hcard⟩ := mem_filter.mp hT
  obtain ⟨hb, _, hColor⟩ := mem_placements.mp hT
  have hsub : T.image Prod.snd ⊆ Icc 1 (n + 1) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    obtain ⟨h₁, h₂, h₃⟩ := hb p hp
    exact mem_Icc.mpr ⟨h₁, (h₂.trans h₃).trans (Nat.le_succ _)⟩
  rw [extend, card_image_of_injOn, availableColors, card_sdiff_of_subset hsub,
    card_image_of_injOn hColor, hcard, Nat.card_Icc, Nat.add_sub_cancel]
  exact fun _ _ _ _ h => (insert_last_inj hT hT h).1

private lemma card_placementsWithCard_succ (n k : ℕ) :
    (placementsWithCard (n + 1) (k + 1)).card =
      (n + 1 - k) * (placementsWithCard n k).card + (placementsWithCard n (k + 1)).card := by
  rw [placementsWithCard_succ, card_union_of_disjoint, card_biUnion]
  · rw [sum_const_nat fun _ hT => card_extend hT]
    ac_rfl
  · intro T hT U hU hne
    simp only [Function.onFun, disjoint_left, extend, mem_image]
    rintro _ ⟨j, _, rfl⟩ ⟨l, _, he⟩
    exact hne (insert_last_inj (mem_filter.mp hT).1 (mem_filter.mp hU).1 he.symm).2
  · simp only [disjoint_left, mem_biUnion, extend, mem_image]
    rintro T hT ⟨U, _, j, _, rfl⟩
    exact notMem_last (mem_filter.mp hT).1 j (mem_insert_self _ _)

/-- A placement of `k` pairs on the board of size `n` contributes to Stirling column `n+1-k`.
The last row is either unused or uses one of the colors not used by the smaller placement. -/
private lemma card_placementsWithCard (n k : ℕ) :
    (placementsWithCard n k).card = (n + 1).stirlingSecond (n + 1 - k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [placementsWithCard_zero, card_singleton, Nat.sub_zero, Nat.stirlingSecond_self]
    | succ k =>
      rw [placementsWithCard_eq_empty (Nat.succ_pos k), card_empty,
        Nat.sub_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le k)), Nat.stirlingSecond_succ_zero]
  | succ n ih =>
    cases k with
    | zero => rw [placementsWithCard_zero, card_singleton, Nat.sub_zero, Nat.stirlingSecond_self]
    | succ k =>
      by_cases hk : k ≤ n
      · rw [card_placementsWithCard_succ, ih k, ih (k + 1)]
        have h₁ : n + 1 + 1 - (k + 1) = (n - k) + 1 := by omega
        have h₂ : n + 1 - k = (n - k) + 1 := by omega
        have h₃ : n + 1 - (k + 1) = n - k := by omega
        rw [h₁, h₂, h₃, Nat.stirlingSecond_succ_succ (n + 1) (n - k)]
      · rw [placementsWithCard_eq_empty (by omega : n + 1 < k + 1), card_empty,
          Nat.sub_eq_zero_of_le (by omega : n + 1 + 1 ≤ k + 1), Nat.stirlingSecond_succ_zero]

private lemma card_placements (n : ℕ) : (placements n).card = Nat.bell (n + 1) := by
  calc
    (placements n).card = ∑ k ∈ range (n + 1 + 1), (placementsWithCard n k).card := by
      apply card_eq_sum_card_fiberwise
      intro T hT
      exact mem_range.mpr ((card_le_of_mem_placements hT).trans_lt (by omega))
    _ = ∑ k ∈ range (n + 1 + 1), (n + 1).stirlingSecond (n + 1 + 1 - 1 - k) := by
      exact sum_congr rfl fun k _ => card_placementsWithCard n k
    _ = Nat.bell (n + 1) := by
      rw [sum_range_reflect, bell_eq_sum_stirlingSecond]

end card_coloredPartitions_fullyDifferent_le

open card_coloredPartitions_fullyDifferent_le

/-- **Colored partitions into fully different parts with bounded size.** A colored part is a pair
$(m, j)$ of integers with $1 \le j \le m$, read as the part $m$ in color $j$. For every $n \ge 0$,
the number of nonempty finite sets of colored parts $(m, j)$ with $m \le n$ in which no two
colored parts have the same size $m$ and no two have the same color $j$ is $B_{n+1} - 1$, where
$B_k$ denotes the $k$-th Bell number.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 3 (`integers-2026-A20-thm-3`). -/
public theorem card_coloredPartitions_fullyDifferent_le (n : ℕ) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x : ℕ × ℕ => x.2 ≤ x.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.fst).card = T.card ∧
        (T.image Prod.snd).card = T.card)).card = Nat.bell (n + 1) - 1 := by
  have h : (placements n).erase ∅ =
      (((Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ => p.2 ≤ p.1)).powerset.filter
        fun T => T.Nonempty ∧ (T.image Prod.fst).card = T.card ∧
          (T.image Prod.snd).card = T.card) := by
    ext T
    simp only [mem_erase, placements, mem_filter, nonempty_iff_ne_empty]
    exact ⟨fun ⟨he, hp, hi⟩ => ⟨hp, he, hi⟩, fun ⟨hp, he, hi⟩ => ⟨he, hp, hi⟩⟩
  rw [← h, card_erase_of_mem (empty_mem_placements n), card_placements]

end MetaMathlibExt
