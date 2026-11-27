/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Tauto

namespace MetaMathlibExt

open scoped Pointwise

private def grid (m r : ℤ) : Finset ℤ :=
  (Finset.Icc 0 m).image fun i => 4 * i + r

private theorem mem_grid (m r z : ℤ) :
    z ∈ grid m r ↔ ∃ i : ℤ, 0 ≤ i ∧ i ≤ m ∧ 4 * i + r = z := by
  simp [grid, Finset.mem_image, Finset.mem_Icc, and_assoc]

private theorem mem_replicate (n : ℕ) (a z : ℤ) (l : List ℕ) :
    z ∈ setOfConsecutiveDifferences a (List.replicate n 4 ++ l) ↔
      (∃ i : ℤ, 0 ≤ i ∧ i < n ∧ a + 4 * i = z) ∨
        z ∈ setOfConsecutiveDifferences (a + 4 * n) l := by
  induction n generalizing a with
  | zero => simp; omega
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, setOfConsecutiveDifferences_cons,
      Finset.mem_insert, ih, Nat.cast_add, Nat.cast_one]
    constructor
    · rintro (rfl | ⟨i, hi, hin, he⟩ | hz)
      · exact Or.inl ⟨0, by omega, by omega, by omega⟩
      · exact Or.inl ⟨i + 1, by omega, by omega, by omega⟩
      · right
        convert hz using 1; congr 1; omega
    · rintro (⟨i, hi, hin, he⟩ | hz)
      · by_cases h : i = 0
        · left; omega
        · right; left
          exact ⟨i - 1, by omega, by omega, by omega⟩
      · right; right
        convert hz using 1; congr 1; omega

private theorem mem_block (n : ℕ) (a z : ℤ) (l : List ℕ) :
    z ∈ setOfConsecutiveDifferences a (chuBlock n ++ l) ↔
      z = a ∨ (∃ i : ℤ, 0 ≤ i ∧ i ≤ n ∧ a + 4 * i + 1 = z) ∨
        z ∈ setOfConsecutiveDifferences (a + 4 * (n + 1)) l := by
  simp only [chuBlock, List.cons_append, List.append_assoc,
    setOfConsecutiveDifferences_cons, Finset.mem_insert, mem_replicate]
  constructor
  · rintro (h | ⟨i, hi, hin, he⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, hi, by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨n, by omega, by omega, by omega⟩)
    · right; right
      convert h using 1; congr 1; omega
  · rintro (h | ⟨i, hi, hin, he⟩ | h)
    · exact Or.inl h
    · right
      by_cases h' : i < n
      · exact Or.inl ⟨i, hi, h', by omega⟩
      · right; left; omega
    · right; right; right
      convert h using 1; congr 1; omega

private def exceptional (a : ℤ) : Finset ℤ :=
  {0, 2, 4, 4 * a, 8 * a, 12 * a, 12 * a + 2}

private theorem family_eq (k : ℕ) :
    setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ chuBlock (k + 1) ++ [1, 1]) =
        grid (3 * (k + 2)) 1 ∪ exceptional (k + 2) := by
  ext z
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    setOfConsecutiveDifferences_cons, Finset.mem_insert, mem_block,
    setOfConsecutiveDifferences, Finset.mem_singleton, Finset.mem_union,
    exceptional, mem_grid, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  constructor
  · rintro (h | h | h | h | ⟨i, hi, hin, he⟩ | h | ⟨i, hi, hin, he⟩ |
      h | ⟨i, hi, hin, he⟩ | h | h | h)
    · right; omega
    · left; exact ⟨0, by omega, by omega, by omega⟩
    · right; omega
    · right; omega
    · left; exact ⟨i + 1, by omega, by omega, by omega⟩
    · right; omega
    · left; exact ⟨i + k + 2, by omega, by omega, by omega⟩
    · right; omega
    · left; exact ⟨i + 2 * k + 4, by omega, by omega, by omega⟩
    · right; omega
    · left; exact ⟨3 * (k + 2), by omega, by omega, by omega⟩
    · right; omega
  · rintro (⟨i, hi, him, he⟩ | h)
    · by_cases h0 : i = 0
      · omega
      by_cases h1 : i ≤ k + 1
      · right; right; right; right; left
        exact ⟨i - 1, by omega, by omega, by omega⟩
      by_cases h2 : i ≤ 2 * k + 3
      · right; right; right; right; right; right; left
        exact ⟨i - k - 2, by omega, by omega, by omega⟩
      by_cases h3 : i ≤ 3 * k + 5
      · right; right; right; right; right; right; right; right; left
        exact ⟨i - 2 * k - 4, by omega, by omega, by omega⟩
      · omega
    · omega

private theorem grid_add (m r s : ℤ) (hm : 0 ≤ m) :
    grid m r + grid m s = grid (2 * m) (r + s) := by
  ext z
  simp only [Finset.mem_add, mem_grid]
  constructor
  · rintro ⟨x, ⟨i, hi, him, rfl⟩, y, ⟨j, hj, hjm, rfl⟩, rfl⟩
    exact ⟨i + j, by omega, by omega, by omega⟩
  · rintro ⟨i, hi, him, rfl⟩
    by_cases h : i ≤ m
    · exact ⟨4 * i + r, ⟨i, hi, h, rfl⟩,
        s, ⟨0, by omega, hm, by omega⟩, by omega⟩
    · exact ⟨4 * m + r, ⟨m, hm, le_rfl, rfl⟩,
        4 * (i - m) + s, ⟨i - m, by omega, by omega, rfl⟩, by omega⟩

private theorem mixed_add (m : ℤ) (E : Finset ℤ)
    (hends : ({0, 2, 4 * m, 4 * m + 2} : Finset ℤ) ⊆ E)
    (hE : ∀ e ∈ E, ∃ d : ℤ, 0 ≤ d ∧ d ≤ m ∧ (e = 4 * d ∨ e = 4 * d + 2)) :
    E + grid m 1 = grid (2 * m) 1 ∪ grid (2 * m) 3 := by
  ext z
  simp only [Finset.mem_add, Finset.mem_union, mem_grid]
  constructor
  · rintro ⟨e, he, x, ⟨i, hi, him, rfl⟩, rfl⟩
    obtain ⟨d, hd, hdm, hde | hde⟩ := hE e he
    · left; exact ⟨d + i, by omega, by omega, by omega⟩
    · right; exact ⟨d + i, by omega, by omega, by omega⟩
  · rintro (⟨i, hi, him, rfl⟩ | ⟨i, hi, him, rfl⟩)
    · by_cases h : i ≤ m
      · exact ⟨0, hends (by simp), 4 * i + 1, ⟨i, hi, h, rfl⟩, by omega⟩
      · exact ⟨4 * m, hends (by simp), 4 * (i - m) + 1,
          ⟨i - m, by omega, by omega, rfl⟩, by omega⟩
    · by_cases h : i ≤ m
      · exact ⟨2, hends (by simp), 4 * i + 1, ⟨i, hi, h, rfl⟩, by omega⟩
      · exact ⟨4 * m + 2, hends (by simp), 4 * (i - m) + 1,
          ⟨i - m, by omega, by omega, rfl⟩, by omega⟩

private def reflected (a : ℤ) : Finset ℤ :=
  {0, 2, 12 * a, 12 * a + 2, 12 * a - 2, 8 * a + 2, 4 * a + 2}

private theorem exceptional_mixed (a : ℤ) (ha : 3 ≤ a) :
    exceptional a + grid (3 * a) 1 = grid (6 * a) 1 ∪ grid (6 * a) 3 := by
  rw [show 6 * a = 2 * (3 * a) by omega]
  apply mixed_add
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    simp only [exceptional, Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro e he
    simp only [exceptional, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨0, by omega, by omega, Or.inr (by omega)⟩
    · exact ⟨1, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨a, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨2 * a, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨3 * a, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨3 * a, by omega, by omega, Or.inr (by omega)⟩

private theorem reflected_mixed (a : ℤ) (ha : 3 ≤ a) :
    reflected a + grid (3 * a) 1 = grid (6 * a) 1 ∪ grid (6 * a) 3 := by
  rw [show 6 * a = 2 * (3 * a) by omega]
  apply mixed_add
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    simp only [reflected, Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro e he
    simp only [reflected, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨0, by omega, by omega, Or.inr (by omega)⟩
    · exact ⟨3 * a, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨3 * a, by omega, by omega, Or.inr (by omega)⟩
    · exact ⟨3 * a - 1, by omega, by omega, Or.inr (by omega)⟩
    · exact ⟨2 * a, by omega, by omega, Or.inr (by omega)⟩
    · exact ⟨a, by omega, by omega, Or.inr (by omega)⟩

private def sumExceptions (a : ℤ) : Finset ℤ :=
  {0, 4, 8, 4 * a, 4 * a + 4, 8 * a, 8 * a + 4, 12 * a, 12 * a + 4,
    16 * a, 20 * a, 24 * a, 24 * a + 4}

private def differenceExceptions (a : ℤ) : Finset ℤ :=
  {0, 4, 4 * a, 4 * a + 4, 8 * a, 8 * a + 4, 12 * a, 12 * a + 4,
    16 * a, 16 * a + 4, 20 * a, 20 * a + 4, 24 * a, 24 * a + 4}

private def commonSums (a : ℤ) : Finset ℤ :=
  grid (6 * a) 1 ∪ grid (6 * a) 2 ∪ grid (6 * a) 3

private theorem exceptional_add (a : ℤ) (ha : 3 ≤ a) :
    grid (6 * a) 2 ∪ (exceptional a + exceptional a) =
      grid (6 * a) 2 ∪ sumExceptions a := by
  ext z
  simp only [Finset.mem_union]
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · obtain ⟨x, hx, y, hy, he⟩ := Finset.mem_add.mp hz
      simp only [exceptional, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (right; simp only [sumExceptions, Finset.mem_insert, Finset.mem_singleton]; omega)
        | (left; apply (mem_grid _ _ _).mpr;
            refine ⟨(z - 2) / 4, ?_, ?_, ?_⟩ <;> omega)
  · rintro (hz | hz)
    · exact Or.inl hz
    · right
      simp only [Finset.mem_add, exceptional, sumExceptions, Finset.mem_insert,
        Finset.mem_singleton, or_and_right, exists_or, exists_eq_left] at hz ⊢
      omega

private theorem reflected_add (a : ℤ) (ha : 3 ≤ a) :
    grid (6 * a) 2 ∪ (exceptional a + reflected a) =
      grid (6 * a) 2 ∪ differenceExceptions a := by
  ext z
  simp only [Finset.mem_union]
  constructor
  · rintro (hz | hz)
    · exact Or.inl hz
    · obtain ⟨x, hx, y, hy, he⟩ := Finset.mem_add.mp hz
      simp only [exceptional, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [reflected, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (right; simp only [differenceExceptions, Finset.mem_insert, Finset.mem_singleton]; omega)
        | (left; apply (mem_grid _ _ _).mpr;
            refine ⟨(z - 2) / 4, ?_, ?_, ?_⟩ <;> omega)
  · rintro (hz | hz)
    · exact Or.inl hz
    · right
      simp only [Finset.mem_add, exceptional, reflected, differenceExceptions,
        Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or,
        exists_eq_left] at hz ⊢
      omega

private theorem merge_shared (P Q R S T : Prop) (h : Q ∨ S ↔ Q ∨ T) :
    ((Q ∨ P ∨ R) ∨ (P ∨ R) ∨ S) ↔ ((P ∨ Q) ∨ R) ∨ T := by
  tauto

private theorem sum_decomposition (a : ℤ) (ha : 3 ≤ a) :
    (grid (3 * a) 1 ∪ exceptional a) + (grid (3 * a) 1 ∪ exceptional a) =
      commonSums a ∪ sumExceptions a := by
  rw [Finset.union_add, Finset.add_union, Finset.add_union,
    grid_add _ _ _ (by omega), add_comm (grid (3 * a) 1) (exceptional a),
    exceptional_mixed a ha]
  simp only [show 2 * (3 * a) = 6 * a by omega, show (1 + 1 : ℤ) = 2 by decide]
  have he := exceptional_add a ha
  ext z
  have hez := Finset.ext_iff.mp he z
  simp only [Finset.mem_union] at hez
  simp only [commonSums, Finset.mem_union]
  exact merge_shared _ _ _ _ _ hez

private theorem difference_decomposition (a : ℤ) (ha : 3 ≤ a) :
    (grid (3 * a) 1 ∪ exceptional a) + (grid (3 * a) 1 ∪ reflected a) =
      commonSums a ∪ differenceExceptions a := by
  rw [Finset.union_add, Finset.add_union, Finset.add_union,
    grid_add _ _ _ (by omega), add_comm (grid (3 * a) 1) (reflected a),
    reflected_mixed a ha, exceptional_mixed a ha]
  simp only [show 2 * (3 * a) = 6 * a by omega, show (1 + 1 : ℤ) = 2 by decide]
  have he := reflected_add a ha
  ext z
  have hez := Finset.ext_iff.mp he z
  simp only [Finset.mem_union] at hez
  simp only [commonSums, Finset.mem_union]
  exact merge_shared _ _ _ _ _ hez

private theorem reflection_eq (a : ℤ) (ha : 3 ≤ a) :
    (grid (3 * a) 1 ∪ exceptional a).image (fun x => 12 * a + 2 - x) =
      grid (3 * a) 1 ∪ reflected a := by
  ext z
  simp only [Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · obtain ⟨i, hi, him, rfl⟩ := (mem_grid _ _ _).mp hx
      left
      exact (mem_grid _ _ _).mpr ⟨3 * a - i, by omega, by omega, by omega⟩
    · right
      simp only [exceptional, reflected, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      omega
  · rintro (hz | hz)
    · obtain ⟨i, hi, him, rfl⟩ := (mem_grid _ _ _).mp hz
      exact ⟨4 * (3 * a - i) + 1,
        Or.inl ((mem_grid _ _ _).mpr ⟨3 * a - i, by omega, by omega, rfl⟩), by omega⟩
    · refine ⟨12 * a + 2 - z, Or.inr ?_, by omega⟩
      simp only [exceptional, reflected, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      omega

private theorem translate_difference (A : Finset ℤ) (c : ℤ) :
    (A - A).image (fun z => c + z) = A + A.image (fun x => c - x) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_sub, Finset.mem_add]
  constructor
  · rintro ⟨d, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, c - y, ⟨y, hy, rfl⟩, by omega⟩
  · rintro ⟨x, hx, y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨x - t, ⟨x, hx, t, ht, rfl⟩, by omega⟩

private theorem exception_cards (a : ℤ) (ha : 3 ≤ a) :
    (sumExceptions a).card = 13 ∧ (differenceExceptions a).card = 14 := by
  constructor <;> simp only [sumExceptions, differenceExceptions]
  all_goals
    repeat rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)]
    rfl

private theorem common_disjoint (a : ℤ) (E : Finset ℤ)
    (hE : ∀ z ∈ E, z % 4 = 0) : Disjoint (commonSums a) E := by
  apply Finset.disjoint_left.mpr
  intro z hz he
  have h := hE z he
  simp only [commonSums, Finset.mem_union, mem_grid] at hz
  rcases hz with (⟨i, hi, him, heq⟩ | ⟨i, hi, him, heq⟩) | ⟨i, hi, him, heq⟩ <;> omega

@[expose] public section

/-- **A difference-dominated family of Chu et al.** Let $k$ be a positive integer and let
$A = (0 \mid 1, 1, 2, M^k, M^{k+1}, M^{k+1}, 1, 1) \subseteq \mathbb{Z}$ be the set of partial
sums, starting at $0$, of the difference sequence formed by $1, 1, 2$, the Chu difference blocks
$M^k$, $M^{k+1}$ and $M^{k+1}$, and $1, 1$. Then $A$ is difference-dominated:
$|A + A| < |A - A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 2 (`integers-2024-A32-thm-2`). -/
public theorem chu_family_difference_dominated {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card < (A - A).card := by
  let a : ℤ := k + 2
  have ha : 3 ≤ a := by dsimp [a]; omega
  dsimp only
  rw [family_eq k]
  change ((grid (3 * a) 1 ∪ exceptional a) + (grid (3 * a) 1 ∪ exceptional a)).card <
    ((grid (3 * a) 1 ∪ exceptional a) - (grid (3 * a) 1 ∪ exceptional a)).card
  have htranslate := Finset.card_image_of_injective
    ((grid (3 * a) 1 ∪ exceptional a) - (grid (3 * a) 1 ∪ exceptional a))
    (show Function.Injective (fun z : ℤ => 12 * a + 2 + z) from fun _ _ h => add_left_cancel h)
  rw [translate_difference, reflection_eq a ha, difference_decomposition a ha] at htranslate
  rw [← htranslate, sum_decomposition a ha]
  have hs : Disjoint (commonSums a) (sumExceptions a) := by
    apply common_disjoint
    intro z hz
    simp only [sumExceptions, Finset.mem_insert, Finset.mem_singleton] at hz
    omega
  have hd : Disjoint (commonSums a) (differenceExceptions a) := by
    apply common_disjoint
    intro z hz
    simp only [differenceExceptions, Finset.mem_insert, Finset.mem_singleton] at hz
    omega
  rw [Finset.card_union_of_disjoint hs, Finset.card_union_of_disjoint hd,
    (exception_cards a ha).1, (exception_cards a ha).2]
  omega

end

end MetaMathlibExt
