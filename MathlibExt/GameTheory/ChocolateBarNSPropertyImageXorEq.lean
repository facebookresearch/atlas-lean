/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Batteries.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bitwise
import MathlibExt.Data.Nat.DyadicBlock

/-!
# Nim-sum images for an NS function

The nim-sum image below a width is unchanged when the height is clamped by an NS function.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20).
-/

namespace MetaMathlibExt.HasNSProperty

private theorem exists_differing_bit {a b : ℕ} (hab : a ≠ b) :
    ∃ k, a.testBit k ≠ b.testBit k ∧ a / 2 ^ (k + 1) = b / 2 ^ (k + 1) := by
  obtain ⟨k, hk, hhigh⟩ := Nat.exists_most_significant_bit (Nat.xor_ne_zero_iff.mpr hab)
  refine ⟨k, ?_, Nat.eq_of_testBit_eq fun j ↦ ?_⟩
  · simpa only [Nat.testBit_xor, bne_iff_ne] using hk
  · simp only [Nat.testBit_div_two_pow]
    have hj := hhigh (j + (k + 1)) (by omega)
    simpa only [Nat.testBit_xor, bne_eq_false_iff_eq] using hj

private theorem min_quotient_eq {g : ℕ → ℕ} (hg : HasNSProperty g)
    {a b k : ℕ} (hab : a / 2 ^ (k + 1) = b / 2 ^ (k + 1)) (x : ℕ) :
    min (g a) x / 2 ^ k = min (g b) x / 2 ^ k := by
  apply min_div_two_pow_eq_of_div_two_pow_eq
  simpa only [Nat.add_sub_cancel] using hg.2 a b (k + 1) (by omega) hab

private theorem testBit_eq_of_quotient_eq {a b k : ℕ}
    (hab : a / 2 ^ k = b / 2 ^ k) {j : ℕ} (hkj : k ≤ j) :
    a.testBit j = b.testBit j := by
  have h := congrArg (fun n : ℕ ↦ n.testBit (j - k)) hab
  simpa only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hkj] using h

private theorem transform_lt {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z w : ℕ} (hx : x ≤ g z) (hw : w < z) : x ^^^ min (g w) x ^^^ w < z := by
  obtain ⟨k, hbit, hquot⟩ := exists_differing_bit hw.ne
  have hhigh : ∀ j, k < j → w.testBit j = z.testBit j := fun j hj ↦
    testBit_eq_of_quotient_eq hquot (by omega)
  have hwbit : w.testBit k = false := by
    by_contra hn
    have hwt : w.testBit k = true := Bool.eq_true_of_ne_false hn
    have hzf : z.testBit k = false := by
      cases hz : z.testBit k <;> simp_all
    exact hw.asymm (Nat.lt_of_testBit k hzf hwt fun j hj ↦ (hhigh j hj).symm)
  have hzbit : z.testBit k = true := by
    cases hz : z.testBit k <;> simp_all
  have hmin : min (g w) x / 2 ^ k = x / 2 ^ k := by
    simpa only [min_eq_right hx] using min_quotient_eq hg hquot x
  have htrans : (x ^^^ min (g w) x ^^^ w) / 2 ^ k = w / 2 ^ k := by
    rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow, hmin, Nat.xor_self, Nat.zero_xor]
  refine Nat.lt_of_testBit k ?_ hzbit fun j hj ↦ ?_
  · exact (testBit_eq_of_quotient_eq htrans le_rfl).trans hwbit
  · exact (testBit_eq_of_quotient_eq htrans (by omega)).trans (hhigh j hj)

private theorem transform_injective {g : ℕ → ℕ} (hg : HasNSProperty g) (x : ℕ) :
    Function.Injective (fun w ↦ x ^^^ min (g w) x ^^^ w) := by
  intro a b hab
  by_contra hne
  obtain ⟨k, hbit, hquot⟩ := exists_differing_bit hne
  have hmin := min_quotient_eq hg hquot x
  have h := congrArg (fun n : ℕ ↦ n / 2 ^ k) hab
  simp only [Nat.xor_div_two_pow, hmin, Nat.xor_right_inj] at h
  exact hbit (testBit_eq_of_quotient_eq h le_rfl)

/-- **Nim-sum image identity for one NS function.** Let $g : \mathbb{N} \to \mathbb{N}$ have the
NS property and let $x, z \in \mathbb{N}$ with $x \le g(z)$. Writing $\oplus$ for the nim-sum
(bitwise exclusive or) of natural numbers, the sets $\{x \oplus w : w < z\}$ and
$\{\min(g(w), x) \oplus w : w < z\}$ are equal, where $w$ ranges over the natural numbers.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20) (`integers-2025-G3-lem-5`). -/
public theorem image_xor_eq {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z : ℕ} (hx : x ≤ g z) :
    {c | ∃ w < z, c = x ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ w'} := by
  let f : Fin z → Fin z := fun w ↦ ⟨x ^^^ min (g w) x ^^^ w, transform_lt hg hx w.isLt⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact transform_injective hg x (congrArg Fin.val hab)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  ext c
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have hvval := congrArg Fin.val hv
    change x ^^^ min (g v) x ^^^ v = w at hvval
    refine ⟨v.val, v.isLt, ?_⟩
    rw [← hvval]
    simp only [Nat.xor_assoc, Nat.xor_xor_cancel_left]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨x ^^^ min (g w) x ^^^ w, transform_lt hg hx hw, ?_⟩
    simp only [Nat.xor_assoc, Nat.xor_xor_cancel_left]

end MetaMathlibExt.HasNSProperty
