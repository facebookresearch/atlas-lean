/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Bitwise
import MathlibExt.Data.Nat.DyadicBlock

/-! # Nim-sum image identity for two NS functions

The nim-sum image of two truncated NS functions agrees with the image obtained by
keeping both coordinates fixed.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (19).
-/

namespace MetaMathlibExt.HasNSProperty

private theorem xor_lt_of_contract {f : ℕ → ℕ}
    (hf : ∀ a b i : ℕ, a / 2 ^ (i + 1) = b / 2 ^ (i + 1) →
      f a / 2 ^ i = f b / 2 ^ i) {a b : ℕ} (hab : a < b) :
    f a ^^^ f b ^^^ a < b := by
  obtain ⟨i, hi, hhigh⟩ := Nat.exists_most_significant_bit (Nat.xor_ne_zero_iff.mpr hab.ne)
  have hbits : ∀ j, i < j → a.testBit j = b.testBit j := by
    intro j hj
    have h := hhigh j hj
    cases ha : a.testBit j <;> cases hb : b.testBit j <;>
      simp_all only [Nat.testBit_xor, Bool.false_xor, Bool.xor_false, Bool.xor_self,
        Bool.true_eq_false]
  have hdiv : a / 2 ^ (i + 1) = b / 2 ^ (i + 1) := by
    apply Nat.eq_of_testBit_eq
    intro j
    simpa only [Nat.testBit_div_two_pow] using hbits (j + (i + 1)) (by omega)
  have hfdiv := hf a b i hdiv
  have hfbits : ∀ j, i ≤ j → (f a).testBit j = (f b).testBit j := by
    intro j hj
    have h := congrArg (fun n : ℕ ↦ n.testBit (j - i)) hfdiv
    simpa only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hj] using h
  have hai : a.testBit i = false := by
    cases ha : a.testBit i
    · rfl
    · cases hb : b.testBit i
      · exact (hab.asymm (Nat.lt_of_testBit i hb ha (fun j hj ↦ (hbits j hj).symm))).elim
      · simp [Nat.testBit_xor, ha, hb] at hi
  have hbi : b.testBit i = true := by
    simpa only [Nat.testBit_xor, hai, Bool.false_xor] using hi
  apply Nat.lt_of_testBit i
  · simp only [Nat.testBit_xor, hfbits i le_rfl, Bool.xor_self, hai]
  · exact hbi
  · intro j hj
    simpa only [Nat.testBit_xor, hfbits j (by omega), Bool.xor_self, Bool.false_xor] using
      hbits j hj

private theorem xor_map_injective {f : ℕ → ℕ}
    (hf : ∀ a b i : ℕ, a / 2 ^ (i + 1) = b / 2 ^ (i + 1) →
      f a / 2 ^ i = f b / 2 ^ i) : Function.Injective (fun a ↦ f a ^^^ a) := by
  intro a b hab
  have hnot : ∀ u v, u < v → f u ^^^ u ≠ f v ^^^ v := by
    intro u v huv heq
    have hlt := xor_lt_of_contract hf huv
    have hv : f u ^^^ f v ^^^ u = v := by
      calc
        f u ^^^ f v ^^^ u = f v ^^^ (f u ^^^ u) := by
          ac_rfl
        _ = v := by rw [heq, Nat.xor_xor_cancel_left]
    exact (hv ▸ hlt).false
  rcases lt_trichotomy a b with h | h | h
  · exact (hnot a b h hab).elim
  · exact h
  · exact (hnot b a h hab.symm).elim

private theorem xor_map_surjective {f : ℕ → ℕ}
    (hf : ∀ a b i : ℕ, a / 2 ^ (i + 1) = b / 2 ^ (i + 1) →
      f a / 2 ^ i = f b / 2 ^ i) (z : ℕ) :
    ∀ w < z, ∃ v < z, f v ^^^ v = f z ^^^ w := by
  let F : Fin z → Fin z := fun v ↦
    ⟨f v ^^^ f z ^^^ v, xor_lt_of_contract hf v.isLt⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Fin.ext
    apply xor_map_injective hf
    have h := congrArg Fin.val hab
    change f a ^^^ f z ^^^ a = f b ^^^ f z ^^^ b at h
    rw [Nat.xor_right_comm (f a), Nat.xor_right_comm (f b)] at h
    exact Nat.xor_left_inj.mp h
  intro w hw
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hF ⟨w, hw⟩
  refine ⟨v, v.isLt, ?_⟩
  have h := congrArg Fin.val hv
  change f v ^^^ f z ^^^ v = w at h
  calc
    f v ^^^ v = f z ^^^ (f v ^^^ f z ^^^ v) := by
      rw [Nat.xor_right_comm (f v), Nat.xor_comm (f v ^^^ v),
        Nat.xor_xor_cancel_left]
    _ = f z ^^^ w := congrArg (fun n ↦ f z ^^^ n) h

@[expose] public section

/-- **Nim-sum image identity for two NS functions.** Let $g, h : \mathbb{N} \to \mathbb{N}$ have
the NS property and let $x, y, z \in \mathbb{N}$ with $x \le g(z)$ and $y \le h(z)$. Writing
$\oplus$ for the nim-sum (bitwise exclusive or) of natural numbers, the sets
$\{x \oplus y \oplus w : w < z\}$ and $\{\min(g(w), x) \oplus \min(h(w), y) \oplus w : w < z\}$
are equal, where $w$ ranges over the natural numbers.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (19) (`integers-2025-G3-lem-5`). -/
public theorem image_xor_xor_eq {g h : ℕ → ℕ} (hg : HasNSProperty g)
    (hh : HasNSProperty h) {x y z : ℕ} (hx : x ≤ g z) (hy : y ≤ h z) :
    {c | ∃ w < z, c = x ^^^ y ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ min (h w') y ^^^ w'}
    := by
  let f : ℕ → ℕ := fun w ↦ min (g w) x ^^^ min (h w) y
  have hf : ∀ a b i : ℕ, a / 2 ^ (i + 1) = b / 2 ^ (i + 1) →
      f a / 2 ^ i = f b / 2 ^ i := by
    intro a b i hab
    have hgdiv : g a / 2 ^ i = g b / 2 ^ i := by
      simpa only [Nat.add_sub_cancel] using hg.2 a b (i + 1) (by omega) hab
    have hhdiv : h a / 2 ^ i = h b / 2 ^ i := by
      simpa only [Nat.add_sub_cancel] using hh.2 a b (i + 1) (by omega) hab
    dsimp only [f]
    rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow,
      min_div_two_pow_eq_of_div_two_pow_eq hgdiv x,
      min_div_two_pow_eq_of_div_two_pow_eq hhdiv y]
  have hfz : f z = x ^^^ y := by
    dsimp only [f]
    rw [min_eq_right hx, min_eq_right hy]
  ext c
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, heq⟩ := xor_map_surjective hf z w hw
    refine ⟨v, hv, ?_⟩
    change x ^^^ y ^^^ w = f v ^^^ v
    rw [heq, hfz]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨f w ^^^ f z ^^^ w, xor_lt_of_contract hf hw, ?_⟩
    change f w ^^^ w = (x ^^^ y) ^^^ (f w ^^^ f z ^^^ w)
    rw [← hfz, Nat.xor_right_comm (f w), Nat.xor_comm (f w ^^^ w),
      Nat.xor_xor_cancel_left]

end

end MetaMathlibExt.HasNSProperty
