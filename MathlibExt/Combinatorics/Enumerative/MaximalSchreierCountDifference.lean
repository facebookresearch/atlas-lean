/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedSchreierPadovan

/-!
# Maximal $(1, q)$-Schreier sets and differences of Schreier counts

For a positive integer `q`, the number of maximal `(1, q)`-Schreier sets with maximum `n ≥ 1`
is `2 |S^{1/q}_n| - |S^{1/q}_{n+1}|`, where `|S^{1/q}_m|` counts the `(1, q)`-Schreier sets with
maximum `m` (`maximalSchreierCount_eq_two_mul_sub`, Theorem 9 of Chu and Vasseur).

A `(1, q)`-Schreier set with maximum `n + 1` either omits `n`, and then lowering its maximum to
`n` gives a `(1, q)`-Schreier set with maximum `n`, or contains `n`, and then removing `n + 1`
gives a `(1, q)`-Schreier set with maximum `n` that is not maximal.
-/

namespace MetaMathlibExt.maximalSchreierCount_eq_two_mul_sub

open Finset

/-- The `(1, q)`-Schreier sets with maximum `n`, with the cardinality raised by `t` in the
Schreier condition: `t = 0` gives all of them and `t = 1` the non-maximal ones. -/
private def family (q t n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun F => n ∈ F ∧ ∀ x ∈ F, F.card + t ≤ q * x

private theorem mem_family {q t n : ℕ} {F : Finset ℕ} :
    F ∈ family q t n ↔
      n ∈ F ∧ (∀ x ∈ F, 1 ≤ x ∧ x ≤ n) ∧ ∀ x ∈ F, F.card + t ≤ q * x := by
  simp only [family, mem_filter, mem_powerset, subset_iff, mem_Icc]
  tauto

private theorem card_family_zero (q n : ℕ) : (family q 0 n).card = schreierCount 1 q n := by
  unfold schreierCount family
  simp only [Nat.add_zero, Nat.one_mul]

/-- The maximal sets are the Schreier sets whose condition is tight at some element. -/
private theorem maximalSchreierCount_add_card_family_one (q n : ℕ) :
    maximalSchreierCount 1 q n + (family q 1 n).card = (family q 0 n).card := by
  rw [← card_filter_add_card_filter_not (s := family q 0 n)
    (fun F => ∃ x ∈ F, q * x = F.card)]
  congr 1
  · unfold maximalSchreierCount family
    rw [filter_filter]
    simp only [Nat.add_zero, Nat.one_mul, and_assoc]
  · unfold family
    rw [filter_filter]
    congr 1
    apply filter_congr
    intro F _
    constructor
    · rintro ⟨hn, h⟩
      exact ⟨⟨hn, fun x hx => (h x hx).trans' (Nat.le_succ _)⟩,
        fun ⟨x, hx, he⟩ => by have := h x hx; omega⟩
    · rintro ⟨⟨hn, h⟩, hne⟩
      refine ⟨hn, fun x hx => ?_⟩
      have := h x hx
      have : q * x ≠ F.card := fun he => hne ⟨x, hx, he⟩
      omega

/-- Splitting the Schreier sets with maximum `n + 1` by whether they contain `n`. -/
private theorem card_family_succ {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (family q 0 (n + 1)).card = (family q 0 n).card + (family q 1 n).card := by
  let S := family q 0 (n + 1)
  have withPrev : (S.filter fun F => n ∈ F).card = (family q 1 n).card := by
    apply card_nbij' (fun F => F.erase (n + 1)) (insert (n + 1))
    · intro F hF
      dsimp only
      obtain ⟨hF, hnF⟩ := mem_filter.mp hF
      obtain ⟨hmax, hbd, hsch⟩ := mem_family.mp hF
      have hcard := card_erase_of_mem hmax
      have hpos := card_pos.mpr ⟨n, hnF⟩
      refine mem_family.mpr ⟨mem_erase.mpr ⟨by omega, hnF⟩, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨hxn, hx⟩ := mem_erase.mp hx
        have := hbd x hx
        omega
      · have := hsch x (mem_of_mem_erase hx)
        omega
    · intro G hG
      obtain ⟨hnG, hbd, hsch⟩ := mem_family.mp hG
      have hnew : n + 1 ∉ G := fun h => by have := hbd _ h; omega
      have hcard := card_insert_of_notMem hnew
      refine mem_filter.mpr ⟨mem_family.mpr ⟨mem_insert_self .., fun x hx => ?_,
        fun x hx => ?_⟩, mem_insert_of_mem hnG⟩
      · rcases mem_insert.mp hx with rfl | hx
        · omega
        · have := hbd x hx
          omega
      · rw [hcard]
        rcases mem_insert.mp hx with rfl | hx
        · have := hsch n hnG
          have := Nat.mul_le_mul_left q (Nat.le_add_right n 1)
          omega
        · have := hsch x hx
          omega
    · intro F hF
      exact insert_erase (mem_family.mp (mem_filter.mp hF).1).1
    · intro G hG
      apply erase_insert
      intro h
      have := ((mem_family.mp hG).2.1 _ h).2
      omega
  have withoutPrev : (S.filter fun F => n ∉ F).card = (family q 0 n).card := by
    apply card_nbij' (fun F => insert n (F.erase (n + 1)))
      (fun G => insert (n + 1) (G.erase n))
    · intro F hF
      dsimp only
      obtain ⟨hF, hnF⟩ := mem_filter.mp hF
      obtain ⟨hmax, hbd, hsch⟩ := mem_family.mp hF
      have hnot : n ∉ F.erase (n + 1) := fun h => hnF (mem_of_mem_erase h)
      have hcard : (insert n (F.erase (n + 1))).card = F.card := by
        rw [card_insert_of_notMem hnot, card_erase_of_mem hmax,
          Nat.sub_add_cancel (card_pos.mpr ⟨n + 1, hmax⟩)]
      -- The new maximum `n` obeys the condition: `F` is a singleton or has an element below `n`.
      have hcardn : F.card ≤ q * n := by
        by_cases hone : F.card ≤ 1
        · have := Nat.mul_le_mul hq hn
          omega
        · obtain ⟨y, hy, hyne⟩ := exists_mem_ne (s := F) (by omega) (n + 1)
          have := hsch y hy
          have := Nat.mul_le_mul_left q (show y ≤ n by have := hbd y hy; omega)
          omega
      refine mem_family.mpr ⟨mem_insert_self .., fun x hx => ?_, fun x hx => ?_⟩
      · rcases mem_insert.mp hx with rfl | hx
        · omega
        · obtain ⟨hxn, hx⟩ := mem_erase.mp hx
          have := hbd x hx
          omega
      · rw [hcard]
        rcases mem_insert.mp hx with rfl | hx
        · omega
        · exact hsch x (mem_of_mem_erase hx)
    · intro G hG
      dsimp only
      obtain ⟨hnG, hbd, hsch⟩ := mem_family.mp hG
      have hnew : n + 1 ∉ G.erase n := fun h => by have := hbd _ (mem_of_mem_erase h); omega
      have hcard : (insert (n + 1) (G.erase n)).card = G.card := by
        rw [card_insert_of_notMem hnew, card_erase_of_mem hnG,
          Nat.sub_add_cancel (card_pos.mpr ⟨n, hnG⟩)]
      refine mem_filter.mpr ⟨mem_family.mpr ⟨mem_insert_self .., fun x hx => ?_,
        fun x hx => ?_⟩, ?_⟩
      · rcases mem_insert.mp hx with rfl | hx
        · omega
        · have := hbd x (mem_of_mem_erase hx)
          omega
      · rw [hcard]
        rcases mem_insert.mp hx with rfl | hx
        · have := hsch n hnG
          have := Nat.mul_le_mul_left q (Nat.le_add_right n 1)
          omega
        · exact hsch x (mem_of_mem_erase hx)
      · simp
    · intro F hF
      dsimp only
      obtain ⟨hF, hnF⟩ := mem_filter.mp hF
      have hmax := (mem_family.mp hF).1
      ext x
      simp only [mem_insert, mem_erase]
      grind
    · intro G hG
      obtain ⟨hnG, hbd, -⟩ := mem_family.mp hG
      have hnew : n + 1 ∉ G := fun h => by have := hbd _ h; omega
      ext x
      simp only [mem_insert, mem_erase]
      grind
  rw [← withPrev, ← withoutPrev, add_comm (card _), card_filter_add_card_filter_not]

end MetaMathlibExt.maximalSchreierCount_eq_two_mul_sub

namespace MetaMathlibExt

/-- **Maximal $(1, q)$-Schreier sets counted by $(1, q)$-Schreier sets.** Fix a positive integer
$q$. For each $m$, let $|S^{1/q}_m|$ be the number of sets $F \subseteq \{1, \dots, m\}$ with
$m \in F$ and $q \min F \ge |F|$, and let $|M^{1/q}_m|$ be the number of those with
$q \min F = |F|$. Then $|M^{1/q}_n| = 2|S^{1/q}_n| - |S^{1/q}_{n+1}|$ for every positive integer
$n$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Theorem 9
(`jis-2026-26.2.2-thm-9`). -/
public theorem maximalSchreierCount_eq_two_mul_sub {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (maximalSchreierCount 1 q n : ℤ) = 2 * schreierCount 1 q n - schreierCount 1 q (n + 1) := by
  have hmax := maximalSchreierCount_eq_two_mul_sub.maximalSchreierCount_add_card_family_one q n
  have hsucc := maximalSchreierCount_eq_two_mul_sub.card_family_succ hq hn
  have hn' := maximalSchreierCount_eq_two_mul_sub.card_family_zero q n
  have hn'' := maximalSchreierCount_eq_two_mul_sub.card_family_zero q (n + 1)
  omega

end MetaMathlibExt
