/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Sort

/-!
# Colored partitions with different sizes and colors

The cardinality formula sums over distinct-size partitions and counts valid colorings
by assigning colors in increasing order of part size.
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

end MetaMathlibExt
