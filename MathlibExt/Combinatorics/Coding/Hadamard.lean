/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.Hadamard

/-- The dot product of two binary vectors. -/
def dot {m : ℕ} (a r : Fin m → ZMod 2) : ZMod 2 :=
  ∑ i, a i * r i

/-- The Hadamard codeword of `a`: evaluation of the linear
functional `dot a` at every vector `r`. -/
def hadCode {m : ℕ} (a : Fin m → ZMod 2) :
    (Fin m → ZMod 2) → ZMod 2 :=
  fun r => dot a r

private theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 :=
  (by decide : ∀ y : ZMod 2, y ≠ 0 → y = 1) x hx

private theorem zmod2_eq_zero_of_ne_one {x : ZMod 2} (hx : x ≠ 1) : x = 0 :=
  (by decide : ∀ y : ZMod 2, y ≠ 1 → y = 0) x hx

private theorem exists_coord_eq_one {m : ℕ} (a : Fin m → ZMod 2) (ha : a ≠ 0) :
    ∃ i₀, a i₀ = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ⟨i, zmod2_eq_one_of_ne_zero ?_⟩
  simpa using hi

private theorem dot_update_flip {m : ℕ} (a r : Fin m → ZMod 2) (i₀ : Fin m)
    (hai₀ : a i₀ = 1) :
    dot a (Function.update r i₀ (r i₀ + 1)) = dot a r + 1 := by
  have hS : (∑ i ∈ Finset.univ.erase i₀, a i * Function.update r i₀ (r i₀ + 1) i)
      = ∑ i ∈ Finset.univ.erase i₀, a i * r i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    rw [Function.update_of_ne hne]
  unfold dot
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
    Function.update_self, hai₀, hS]
  ring

private theorem dot_add_left {m : ℕ} (a b r : Fin m → ZMod 2) :
    dot (a + b) r = dot a r + dot b r := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.add_apply, add_mul]

private theorem dot_basis {m : ℕ} (a : Fin m → ZMod 2) (i : Fin m) :
    dot a (Function.update 0 i 1) = a i := by
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      j ≠ i → a j * Function.update (0 : Fin m → ZMod 2) i 1 j = 0 := by
    intro j _ hji
    rw [Function.update_of_ne hji]
    simp
  have h1 : i ∉ Finset.univ →
      a i * Function.update (0 : Fin m → ZMod 2) i 1 i = 0 :=
    fun hi => absurd (Finset.mem_univ i) hi
  unfold dot
  trans a i * Function.update (0 : Fin m → ZMod 2) i 1 i
  · exact Finset.sum_eq_single i h0 h1
  · rw [Function.update_self, mul_one]

/-- Every nonzero Hadamard codeword has weight exactly half
the block length: `dot a r = 1` for exactly `2 ^ (m - 1)` of
the `2 ^ m` vectors `r`. See `hammingNorm_hadCode` for the
same count as the Hamming norm of `hadCode a`. -/
theorem hadWeight {m : ℕ} (a : Fin m → ZMod 2) (ha : a ≠ 0) :
    (Finset.univ.filter (fun r => dot a r = 1)).card =
      2 ^ (m - 1) := by
  obtain ⟨i₀, hai₀⟩ := exists_coord_eq_one a ha
  have hflip : ∀ r : Fin m → ZMod 2,
      dot a (Function.update r i₀ (r i₀ + 1)) = dot a r + 1 :=
    fun r => dot_update_flip a r i₀ hai₀
  have hinv : ∀ r : Fin m → ZMod 2,
      Function.update (Function.update r i₀ (r i₀ + 1)) i₀
        (Function.update r i₀ (r i₀ + 1) i₀ + 1) = r := by
    intro r
    rw [Function.update_self, Function.update_idem]
    have h2 : r i₀ + 1 + 1 = r i₀ :=
      (by decide : ∀ x : ZMod 2, x + 1 + 1 = x) (r i₀)
    rw [h2]
    exact Function.update_eq_self i₀ r
  have heq : (Finset.univ.filter (fun r => dot a r = 1)).card
      = (Finset.univ.filter (fun r => ¬ (dot a r = 1))).card := by
    apply Finset.card_bij' (fun (r : Fin m → ZMod 2) _ => Function.update r i₀ (r i₀ + 1))
      (fun (r : Fin m → ZMod 2) _ => Function.update r i₀ (r i₀ + 1))
    · intro r hr
      have hr2 : dot a r = 1 := (Finset.mem_filter.mp hr).2
      show Function.update r i₀ (r i₀ + 1) ∈
        Finset.univ.filter (fun r => ¬ (dot a r = 1))
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show ¬ (dot a (Function.update r i₀ (r i₀ + 1)) = 1)
      rw [hflip r, hr2]
      decide
    · intro r hr
      have hr2 : ¬ (dot a r = 1) := (Finset.mem_filter.mp hr).2
      have hr0 : dot a r = 0 := zmod2_eq_zero_of_ne_one hr2
      show Function.update r i₀ (r i₀ + 1) ∈
        Finset.univ.filter (fun r => dot a r = 1)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show dot a (Function.update r i₀ (r i₀ + 1)) = 1
      rw [hflip r, hr0]
      decide
    · intro r _
      exact hinv r
    · intro r _
      exact hinv r
  have hsum : (Finset.univ.filter (fun r => dot a r = 1)).card
      + (Finset.univ.filter (fun r => ¬ (dot a r = 1))).card
      = (Finset.univ : Finset (Fin m → ZMod 2)).card :=
    Finset.card_filter_add_card_filter_not _
  have huniv : (Finset.univ : Finset (Fin m → ZMod 2)).card = 2 ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hm : m ≠ 0 := by
    rintro rfl
    exact ha (funext fun i => absurd i.2 (Nat.not_lt_zero _))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  rw [Nat.add_sub_cancel]
  rw [huniv, pow_succ] at hsum
  omega

/-- `hadWeight` in Mathlib's Hamming vocabulary: a nonzero
Hadamard codeword has Hamming norm `2 ^ (m - 1)`. -/
theorem hammingNorm_hadCode {m : ℕ} (a : Fin m → ZMod 2) (ha : a ≠ 0) :
    hammingNorm (hadCode a) = 2 ^ (m - 1) := by
  rw [hammingNorm, ← hadWeight a ha]
  congr 1
  apply Finset.filter_congr
  intro r _
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 ↔ x = 1) (dot a r)

/-- Distinct Hadamard codewords are at Hamming distance
exactly `2 ^ (m - 1)`. For `m = 0` there is only one
codeword, so the hypothesis `a ≠ b` cannot hold and the
statement is vacuous. -/
theorem hadDist {m : ℕ} (a b : Fin m → ZMod 2) (hab : a ≠ b) :
    hammingDist (hadCode a) (hadCode b) = 2 ^ (m - 1) := by
  have hab0 : a + b ≠ 0 := by
    intro hcon
    apply hab
    funext i
    have hi : a i + b i = 0 := by
      have h := congrFun hcon i
      simpa using h
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) (a i) (b i) hi
  rw [hammingDist, ← hadWeight (a + b) hab0]
  congr 1
  apply Finset.filter_congr
  intro r _
  rw [dot_add_left]
  exact (by decide : ∀ u v : ZMod 2, (u ≠ v) ↔ (u + v = 1)) (dot a r) (dot b r)

/-- The Hadamard encoding is injective (its dimension is
`m`). -/
theorem hadCode_injective {m : ℕ} :
    Function.Injective (hadCode (m := m)) := by
  intro a b hab
  funext i
  have h := congrFun hab (Function.update (0 : Fin m → ZMod 2) i 1)
  simp only [hadCode] at h
  rw [dot_basis, dot_basis] at h
  exact h

end MathlibExt.Combinatorics.Coding.Hadamard
