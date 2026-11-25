/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV

/-!
# Chvátal's theorem for shifted down-sets

In a finite shifted down-set of finite sets of natural numbers, the star at zero is at least
as large as any intersecting subfamily. The proof compresses the subfamily and then inducts
on the size of the ground set.
-/

public section

namespace MathlibExt.Combinatorics.ChvatalShifted

open Finset

/-- A family is shifted at `m` when replacing `m` in a member by a smaller absent element gives
another member. -/
private def ShiftedAt (m : ℕ) (𝓐 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓐, m ∈ A → ∀ i < m, i ∉ A → insert i (A.erase m) ∈ 𝓐

private lemma compress_singleton_eq {i m : ℕ} (him : i ≠ m) (A : Finset ℕ) :
    UV.compress ({i} : Finset ℕ) {m} A = if i ∉ A ∧ m ∈ A then insert i (A.erase m) else A := by
  unfold UV.compress
  simp only [disjoint_singleton_left, singleton_subset_iff]
  split_ifs with h
  · ext x
    simp only [mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    constructor
    · rintro ⟨hx | rfl, hxm⟩
      · exact Or.inr ⟨hxm, hx⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hxm, hx⟩)
      · exact ⟨Or.inr rfl, him⟩
      · exact ⟨Or.inl hx, hxm⟩
  · rfl

/-- The members of the compression of `𝓐` moving `m` to `i`: unmoved members of `𝓐`, whose
compression is already in `𝓐` when it applies, and moved images not in `𝓐`. -/
private lemma mem_compression_singleton {i m : ℕ} (him : i ≠ m) {𝓐 : Finset (Finset ℕ)}
    {B : Finset ℕ} (hB : B ∈ UV.compression {i} {m} 𝓐) :
    B ∈ 𝓐 ∧ (m ∈ B → i ∉ B → insert i (B.erase m) ∈ 𝓐) ∨
      B ∉ 𝓐 ∧ ∃ A ∈ 𝓐, m ∈ A ∧ i ∉ A ∧ B = insert i (A.erase m) := by
  rw [UV.mem_compression] at hB
  rcases hB with ⟨hB, hc⟩ | ⟨hB, A, hA, hc⟩
  · refine Or.inl ⟨hB, fun hm hi => ?_⟩
    rwa [compress_singleton_eq him, ite_eq_left ⟨hi, hm⟩] at hc
  · refine Or.inr ⟨hB, A, hA, ?_⟩
    rw [compress_singleton_eq him] at hc
    split_ifs at hc with h
    · exact ⟨h.2, h.1, hc.symm⟩
    · exact absurd (hc ▸ hA) hB

/-- An unmoved member meets every moved member. -/
private lemma not_disjoint_insert_erase {i m : ℕ} {𝓐 : Finset (Finset ℕ)}
    (hint : (𝓐 : Set (Finset ℕ)).Intersecting) {B A : Finset ℕ} (hB : B ∈ 𝓐)
    (hB' : m ∈ B → i ∉ B → insert i (B.erase m) ∈ 𝓐) (hA : A ∈ 𝓐) (hiA : i ∉ A) :
    ¬ Disjoint B (insert i (A.erase m)) := by
  intro hdis
  have hiB : i ∉ B := fun h => disjoint_left.1 hdis h (mem_insert_self _ _)
  have hmB : m ∈ B := by
    by_contra hmB
    refine hint hB hA (disjoint_left.2 fun x hxB hxA => ?_)
    have hxm : x ≠ m := fun h => hmB (h ▸ hxB)
    exact disjoint_left.1 hdis hxB (mem_insert_of_mem (mem_erase.2 ⟨hxm, hxA⟩))
  refine hint (hB' hmB hiB) hA (disjoint_left.2 fun x hx hxA => ?_)
  rcases mem_insert.1 hx with rfl | hx
  · exact hiA hxA
  · obtain ⟨hxm, hxB⟩ := mem_erase.1 hx
    exact disjoint_left.1 hdis hxB (mem_insert_of_mem (mem_erase.2 ⟨hxm, hxA⟩))

/-- Compression preserves the intersecting property. -/
private lemma intersecting_compression {i m : ℕ} (him : i ≠ m) {𝓐 : Finset (Finset ℕ)}
    (hint : (𝓐 : Set (Finset ℕ)).Intersecting) :
    ((UV.compression {i} {m} 𝓐 : Finset (Finset ℕ)) : Set (Finset ℕ)).Intersecting := by
  intro B hB C hC hBC
  rcases mem_compression_singleton him hB with ⟨hB, hB'⟩ | ⟨-, A, hA, -, hiA, rfl⟩ <;>
    rcases mem_compression_singleton him hC with ⟨hC, hC'⟩ | ⟨-, A', hA', -, hiA', rfl⟩
  · exact hint hB hC hBC
  · exact not_disjoint_insert_erase hint hB hB' hA' hiA' hBC
  · exact not_disjoint_insert_erase hint hC hC' hA hiA hBC.symm
  · exact disjoint_left.1 hBC (mem_insert_self i _) (mem_insert_self i _)

/-- Compression keeps a subfamily of a shifted family inside it. -/
private lemma compression_subset {i m : ℕ} (him : i < m) {𝓕 𝓐 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (h𝓐 : 𝓐 ⊆ 𝓕) : UV.compression {i} {m} 𝓐 ⊆ 𝓕 := by
  intro B hB
  rcases mem_compression_singleton him.ne hB with ⟨hB, -⟩ | ⟨-, A, hA, hmA, hiA, rfl⟩
  · exact h𝓐 hB
  · exact hshift A (h𝓐 hA) m hmA i him hiA

/-- A compression that moves some member decreases the number of members containing `m`. -/
private lemma card_filter_mem_compression_lt {i m : ℕ} (him : i ≠ m) {𝓐 : Finset (Finset ℕ)}
    {A : Finset ℕ} (hA : A ∈ 𝓐) (hmA : m ∈ A) (hiA : i ∉ A)
    (hnot : insert i (A.erase m) ∉ 𝓐) :
    #{B ∈ UV.compression {i} {m} 𝓐 | m ∈ B} < #{B ∈ 𝓐 | m ∈ B} := by
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · refine ⟨A, mem_filter.2 ⟨hA, hmA⟩, fun h => ?_⟩
    rcases mem_compression_singleton him (mem_filter.1 h).1 with ⟨-, hA'⟩ | ⟨hA', -⟩
    · exact hnot (hA' hmA hiA)
    · exact hA' hA
  · intro B hB
    obtain ⟨hB, hmB⟩ := mem_filter.1 hB
    rcases mem_compression_singleton him hB with ⟨hB, -⟩ | ⟨-, A', -, -, -, rfl⟩
    · exact mem_filter.2 ⟨hB, hmB⟩
    · exfalso
      rcases mem_insert.1 hmB with h | h
      · exact him h.symm
      · exact notMem_erase m A' h

/-- Every intersecting subfamily of a shifted family can be replaced by one of the same size that
is shifted at `m`. -/
private lemma exists_shiftedAt {𝓕 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕) (m : ℕ)
    (𝓐 : Finset (Finset ℕ)) (h𝓐 : 𝓐 ⊆ 𝓕) (hint : (𝓐 : Set (Finset ℕ)).Intersecting) :
    ∃ 𝓑 : Finset (Finset ℕ), 𝓑 ⊆ 𝓕 ∧ (𝓑 : Set (Finset ℕ)).Intersecting ∧ #𝓑 = #𝓐 ∧
      ShiftedAt m 𝓑 := by
  suffices H : ∀ k, ∀ 𝓐 : Finset (Finset ℕ), #{B ∈ 𝓐 | m ∈ B} = k → 𝓐 ⊆ 𝓕 →
      (𝓐 : Set (Finset ℕ)).Intersecting →
      ∃ 𝓑 : Finset (Finset ℕ), 𝓑 ⊆ 𝓕 ∧ (𝓑 : Set (Finset ℕ)).Intersecting ∧ #𝓑 = #𝓐 ∧
        ShiftedAt m 𝓑 from H _ 𝓐 rfl h𝓐 hint
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro 𝓐 hk h𝓐 hint
    by_cases hs : ShiftedAt m 𝓐
    · exact ⟨𝓐, h𝓐, hint, rfl, hs⟩
    · simp only [ShiftedAt, not_forall] at hs
      obtain ⟨A, hA, hmA, i, him, hiA, hnot⟩ := hs
      obtain ⟨𝓑, h𝓑, hint𝓑, hcard, hsh⟩ :=
        ih _ (hk ▸ card_filter_mem_compression_lt him.ne hA hmA hiA hnot)
          (UV.compression {i} {m} 𝓐) rfl (compression_subset him hshift h𝓐)
          (intersecting_compression him.ne hint)
      exact ⟨𝓑, h𝓑, hint𝓑, hcard.trans (UV.card_compression _ _ _), hsh⟩

/-- In a family shifted at `m` whose members lie in `{0, ..., m}`, two members containing `m`
that meet only in `m` together cover `{0, ..., m}`. -/
private lemma union_eq_range_of_disjoint {m : ℕ} {𝓑 : Finset (Finset ℕ)}
    (hint : (𝓑 : Set (Finset ℕ)).Intersecting) (hsh : ShiftedAt m 𝓑)
    (hbd : ∀ A ∈ 𝓑, A ⊆ range (m + 1)) {X Y : Finset ℕ}
    (hX : X ∈ 𝓑.memberSubfamily m) (hY : Y ∈ 𝓑.memberSubfamily m) (hXY : Disjoint X Y) :
    X ∪ Y = range m := by
  rw [mem_memberSubfamily] at hX hY
  have hsub : ∀ Z, insert m Z ∈ 𝓑 → m ∉ Z → Z ⊆ range m := fun Z hZ hmZ x hx => by
    have hx' := mem_range.1 (hbd _ hZ (mem_insert_of_mem hx))
    exact mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx') fun h => hmZ (h ▸ hx))
  refine Subset.antisymm (union_subset (hsub X hX.1 hX.2) (hsub Y hY.1 hY.2)) fun i hi => ?_
  by_contra hiXY
  rw [mem_union, not_or] at hiXY
  have hi' : i < m := mem_range.1 hi
  have hmem : insert i ((insert m Y).erase m) ∈ 𝓑 :=
    hsh _ hY.1 (mem_insert_self m Y) i hi' (by simp [hiXY.2, hi'.ne])
  rw [erase_insert hY.2] at hmem
  refine hint hX.1 hmem (disjoint_left.2 fun x hx hx' => ?_)
  rcases mem_insert.1 hx with rfl | hx
  · rcases mem_insert.1 hx' with h | h
    · exact hi'.ne h.symm
    · exact hY.2 h
  · rcases mem_insert.1 hx' with rfl | h
    · exact hiXY.1 hx
    · exact disjoint_left.1 hXY hx h

private lemma isLowerSet_memberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hlow : IsLowerSet (𝓕 : Set (Finset ℕ))) :
    IsLowerSet ((𝓕.memberSubfamily m : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
  intro X Y hYX hX
  rw [mem_coe, mem_memberSubfamily] at hX ⊢
  exact ⟨hlow (insert_subset_insert m hYX) hX.1, fun h => hX.2 (hYX h)⟩

private lemma isLowerSet_nonMemberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hlow : IsLowerSet (𝓕 : Set (Finset ℕ))) :
    IsLowerSet ((𝓕.nonMemberSubfamily m : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
  intro X Y hYX hX
  rw [mem_coe, mem_nonMemberSubfamily] at hX ⊢
  exact ⟨hlow hYX hX.1, fun h => hX.2 (hYX h)⟩

private lemma shift_memberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) :
    ∀ A ∈ 𝓕.memberSubfamily m, ∀ j ∈ A, ∀ i < j, i ∉ A →
      insert i (A.erase j) ∈ 𝓕.memberSubfamily m := by
  intro A hA j hj i hij hiA
  rw [mem_memberSubfamily] at hA ⊢
  have hjm : j ≠ m := fun h => hA.2 (h ▸ hj)
  have hjm' : j < m :=
    lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 (hbd _ hA.1 (mem_insert_of_mem hj)))) hjm
  have him : i ≠ m := (hij.trans hjm').ne
  have h := hshift _ hA.1 j (mem_insert_of_mem hj) i hij (by simp [him, hiA])
  rw [erase_insert_of_ne (Ne.symm hjm), insert_comm] at h
  refine ⟨h, ?_⟩
  simp [him.symm, hA.2]

private lemma shift_nonMemberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) :
    ∀ A ∈ 𝓕.nonMemberSubfamily m, ∀ j ∈ A, ∀ i < j, i ∉ A →
      insert i (A.erase j) ∈ 𝓕.nonMemberSubfamily m := by
  intro A hA j hj i hij hiA
  rw [mem_nonMemberSubfamily] at hA ⊢
  have hjm : j ≠ m := fun h => hA.2 (h ▸ hj)
  have hjm' : j < m := lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 (hbd _ hA.1 hj))) hjm
  have him : i ≠ m := (hij.trans hjm').ne
  refine ⟨hshift _ hA.1 j hj i hij hiA, ?_⟩
  simp [him.symm, hA.2]

private lemma subset_range_memberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) : ∀ A ∈ 𝓕.memberSubfamily m, A ⊆ range m := by
  intro A hA x hx
  rw [mem_memberSubfamily] at hA
  have hx' := mem_range.1 (hbd _ hA.1 (mem_insert_of_mem hx))
  exact mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx') fun h => hA.2 (h ▸ hx))

private lemma subset_range_nonMemberSubfamily {m : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hbd : ∀ A ∈ 𝓕, A ⊆ range (m + 1)) : ∀ A ∈ 𝓕.nonMemberSubfamily m, A ⊆ range m := by
  intro A hA x hx
  rw [mem_nonMemberSubfamily] at hA
  have hx' := mem_range.1 (hbd _ hA.1 hx)
  exact mem_range.2 (lt_of_le_of_ne (Nat.lt_succ_iff.1 hx') fun h => hA.2 (h ▸ hx))

/-- Chvátal's bound for families whose members lie in `{0, ..., n - 1}`, by induction on `n`. -/
private lemma card_le_aux (n : ℕ) :
    ∀ 𝓕 𝓐 : Finset (Finset ℕ), IsLowerSet (𝓕 : Set (Finset ℕ)) →
      (∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕) →
      (∀ A ∈ 𝓕, A ⊆ range n) → 𝓐 ⊆ 𝓕 → (𝓐 : Set (Finset ℕ)).Intersecting →
      #𝓐 ≤ #{A ∈ 𝓕 | 0 ∈ A} := by
  induction n with
  | zero =>
    intro 𝓕 𝓐 _ _ hbd h𝓐 hint
    refine card_le_card fun A hA => ?_
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 (hint.ne_bot hA)
    simpa using hbd A (h𝓐 hA) hx
  | succ m ih =>
    intro 𝓕 𝓐 hlow hshift hbd h𝓐 hint
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine card_le_card fun A hA => mem_filter.2 ⟨h𝓐 hA, ?_⟩
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 (hint.ne_bot hA)
      have hx0 : x = 0 := by simpa using hbd A (h𝓐 hA) hx
      exact hx0 ▸ hx
    obtain ⟨𝓑, h𝓑, hint𝓑, hcard, hsh⟩ := exists_shiftedAt hshift m 𝓐 h𝓐 hint
    have hbd𝓑 : ∀ A ∈ 𝓑, A ⊆ range (m + 1) := fun A hA => hbd A (h𝓑 hA)
    rw [← hcard]
    -- Split `𝓑` according to whether its members contain `m`.
    set 𝓒 := (𝓑.memberSubfamily m).filter
      (fun X => 0 ∉ X ∧ range m \ X ∈ 𝓑.memberSubfamily m)
    set 𝓓 := (𝓑.memberSubfamily m).filter
      (fun X => ¬ (0 ∉ X ∧ range m \ X ∈ 𝓑.memberSubfamily m))
    have h0m : 0 ∈ range m := mem_range.2 hm
    -- Members of `𝓓` pairwise intersect.
    have hint𝓓 : (𝓓 : Set (Finset ℕ)).Intersecting := by
      intro X hX Y hY hXY
      obtain ⟨hX, hpX⟩ := mem_filter.1 hX
      obtain ⟨hY, hpY⟩ := mem_filter.1 hY
      have hU := union_eq_range_of_disjoint hint𝓑 hsh hbd𝓑 hX hY hXY
      rcases mem_union.1 (hU ▸ h0m) with h0X | h0Y
      · refine hpY ⟨fun h0Y => disjoint_left.1 hXY h0X h0Y, ?_⟩
        rwa [← hU, union_sdiff_right, hXY.sdiff_eq_left]
      · refine hpX ⟨fun h0X => disjoint_left.1 hXY h0X h0Y, ?_⟩
        rwa [← hU, union_sdiff_left, hXY.symm.sdiff_eq_left]
    -- Members of `𝓑` without `m`, together with `𝓒`, pairwise intersect.
    have hint𝓒 : ((𝓑.nonMemberSubfamily m ∪ 𝓒 : Finset (Finset ℕ)) :
        Set (Finset ℕ)).Intersecting := by
      intro A hA B hB hAB
      rw [mem_coe, mem_union] at hA hB
      rcases hA with hA | hA <;> rcases hB with hB | hB
      · exact hint𝓑 (mem_nonMemberSubfamily.1 hA).1 (mem_nonMemberSubfamily.1 hB).1 hAB
      · obtain ⟨hA, hmA⟩ := mem_nonMemberSubfamily.1 hA
        exact hint𝓑 hA (mem_memberSubfamily.1 (mem_filter.1 hB).1).1
          (disjoint_insert_right.2 ⟨hmA, hAB⟩)
      · obtain ⟨hB, hmB⟩ := mem_nonMemberSubfamily.1 hB
        exact hint𝓑 (mem_memberSubfamily.1 (mem_filter.1 hA).1).1 hB
          (disjoint_insert_left.2 ⟨hmB, hAB⟩)
      · obtain ⟨hA, h0A, -⟩ := mem_filter.1 hA
        obtain ⟨hB, h0B, -⟩ := mem_filter.1 hB
        have hU := union_eq_range_of_disjoint hint𝓑 hsh hbd𝓑 hA hB hAB
        rcases mem_union.1 (hU ▸ h0m) with h | h
        · exact h0A h
        · exact h0B h
    have hdisj : Disjoint (𝓑.nonMemberSubfamily m) 𝓒 := by
      refine disjoint_left.2 fun X hX hXC => ?_
      obtain ⟨hX, hmX⟩ := mem_nonMemberSubfamily.1 hX
      obtain ⟨-, -, hcomp⟩ := mem_filter.1 hXC
      exact hint𝓑 hX (mem_memberSubfamily.1 hcomp).1
        (disjoint_insert_right.2 ⟨hmX, disjoint_sdiff⟩)
    -- Apply the induction hypothesis to both parts.
    have hD : #𝓓 ≤ #{A ∈ 𝓕.memberSubfamily m | 0 ∈ A} := by
      refine ih _ _ (isLowerSet_memberSubfamily hlow) (shift_memberSubfamily hshift hbd)
        (subset_range_memberSubfamily hbd) (fun X hX => ?_) hint𝓓
      rw [mem_memberSubfamily]
      obtain ⟨hX, -⟩ := mem_filter.1 hX
      rw [mem_memberSubfamily] at hX
      exact ⟨h𝓑 hX.1, hX.2⟩
    have hC : #(𝓑.nonMemberSubfamily m ∪ 𝓒) ≤ #{A ∈ 𝓕.nonMemberSubfamily m | 0 ∈ A} := by
      refine ih _ _ (isLowerSet_nonMemberSubfamily hlow) (shift_nonMemberSubfamily hshift hbd)
        (subset_range_nonMemberSubfamily hbd) (fun X hX => ?_) hint𝓒
      rw [mem_nonMemberSubfamily]
      rcases mem_union.1 hX with hX | hX
      · obtain ⟨hX, hmX⟩ := mem_nonMemberSubfamily.1 hX
        exact ⟨h𝓑 hX, hmX⟩
      · obtain ⟨hX, -⟩ := mem_filter.1 hX
        rw [mem_memberSubfamily] at hX
        exact ⟨hlow (subset_insert m X) (h𝓑 hX.1), hX.2⟩
    rw [card_union_of_disjoint hdisj] at hC
    -- Count the star of `0` in `𝓕` by the same split.
    have hstar : #{A ∈ 𝓕 | 0 ∈ A} =
        #{A ∈ 𝓕.memberSubfamily m | 0 ∈ A} + #{A ∈ 𝓕.nonMemberSubfamily m | 0 ∈ A} := by
      rw [← card_memberSubfamily_add_card_nonMemberSubfamily m {A ∈ 𝓕 | 0 ∈ A}]
      congr 2
      · ext X
        simp only [mem_memberSubfamily, mem_filter, mem_insert]
        constructor
        · rintro ⟨⟨hX, h0 | h0⟩, hmX⟩
          · exact absurd h0 hm.ne
          · exact ⟨⟨hX, hmX⟩, h0⟩
        · rintro ⟨⟨hX, hmX⟩, h0⟩
          exact ⟨⟨hX, Or.inr h0⟩, hmX⟩
      · ext X
        simp only [mem_nonMemberSubfamily, mem_filter]
        tauto
    have hsplit : #(𝓑.memberSubfamily m) = #𝓒 + #𝓓 :=
      (card_filter_add_card_filter_not _).symm
    rw [hstar, ← card_memberSubfamily_add_card_nonMemberSubfamily m 𝓑, hsplit]
    omega

/-- **Chvátal's theorem for shifted down-sets.** Let $\mathcal F$ be a finite family of finite
sets of natural numbers that is closed under taking subsets and under shifting, that is,
replacing an element $j$ of a member by a smaller natural number $i$ not in that member gives
another member. Then every intersecting subfamily of $\mathcal F$ (any two members, equal or not,
meet) has at most as many members as the star $\{A \in \mathcal F : 0 \in A\}$.

The proof compresses the intersecting family at the largest element $m$ of the ground set and
splits it by whether its members contain $m$; induction on the ground set applies to both parts.

Source: B. Alexeev, D. Mixon, and W. Sawin, The independence and clique cover numbers of the
squarefree graph, arXiv:2507.01928 (2025), https://arxiv.org/abs/2507.01928, Section 1.1,
Proposition 3, where the result is attributed to V. Chvátal, Intersecting families of edges in
hypergraphs having the hereditary property, Hypergraph Seminar, Springer (1974), 61-66. There
the ground set is $\{1, \dots, k\}$, the star is that of $1$, and the family is closed under
passing to any set that injects into a member by a map $f$ with $x \le f(x)$, which is
equivalent to closure under subsets and shifts. -/
theorem card_le_card_star_zero_of_isLowerSet_of_shifted {𝓕 𝓐 : Finset (Finset ℕ)}
    (hlow : IsLowerSet (𝓕 : Set (Finset ℕ)))
    (hshift : ∀ A ∈ 𝓕, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ 𝓕)
    (h𝓐 : 𝓐 ⊆ 𝓕) (hint : (𝓐 : Set (Finset ℕ)).Intersecting) :
    #𝓐 ≤ #{A ∈ 𝓕 | 0 ∈ A} := by
  refine card_le_aux (𝓕.sup fun A => A.sup (· + 1)) 𝓕 𝓐 hlow hshift (fun A hA x hx => ?_) h𝓐
    hint
  have h₁ : x + 1 ≤ A.sup (· + 1) := le_sup (f := (· + 1)) hx
  have h₂ : A.sup (· + 1) ≤ 𝓕.sup fun A => A.sup (· + 1) :=
    le_sup (f := fun A : Finset ℕ => A.sup (· + 1)) hA
  exact mem_range.2 (by omega)

end MathlibExt.Combinatorics.ChvatalShifted
