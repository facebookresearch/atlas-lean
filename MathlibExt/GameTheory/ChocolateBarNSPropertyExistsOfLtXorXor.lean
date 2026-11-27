/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Bitwise

/-! # Mex step for chocolate bars with two functions

The mex step for chocolate bars with two functions with the `NS` property: every value below
the nim-sum `x ⊕ y ⊕ z` is a nim-sum with one coordinate lowered or with the width cut, from
R. Miyadera, H. Manabe and A. Singh, *Generalizations of Two-Dimensional and
Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Lemma 3 (b).
The definition of the `NS` property is Definition 11 (p. 9) of the same paper; nim-sum `⊕` is
`Nat.xor` (`^^^`) and `Z≥0` is `ℕ`.
-/

namespace MetaMathlibExt

namespace HasNSProperty

@[expose] public section

/-- The first Nim witness reproduces the target. -/
private theorem xorA_eq (c y z : ℕ) : c = ((c ^^^ z) ^^^ y) ^^^ y ^^^ z := by
  rw [Nat.xor_xor_cancel_right, Nat.xor_xor_cancel_right]

/-- The second Nim witness reproduces the target. -/
private theorem xorB_eq (c x z : ℕ) : c = x ^^^ ((c ^^^ z) ^^^ x) ^^^ z := by
  rw [Nat.xor_comm (c ^^^ z) x, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor,
    Nat.xor_xor_cancel_right]

/-- The third Nim witness reproduces the target. -/
private theorem xorC_eq (c x y : ℕ) : c = (x ^^^ y) ^^^ (c ^^^ (x ^^^ y)) := by
  rw [Nat.xor_comm (x ^^^ y), Nat.xor_xor_cancel_right]

/-- Below a triple nim-sum, some pile can be lowered to hit the target. -/
private theorem nim_trichotomy {x y z c : ℕ} (hc : c < x ^^^ y ^^^ z) :
    (∃ u < x, c = u ^^^ y ^^^ z) ∨ (∃ v < y, c = x ^^^ v ^^^ z) ∨
      ∃ w < z, c = x ^^^ y ^^^ w := by
  rcases Nat.lt_xor_cases hc with h1 | h1
  · rcases Nat.lt_xor_cases h1 with h2 | h2
    · exact Or.inl ⟨(c ^^^ z) ^^^ y, h2, xorA_eq c y z⟩
    · exact Or.inr (Or.inl ⟨(c ^^^ z) ^^^ x, h2, xorB_eq c x z⟩)
  · exact Or.inr (Or.inr ⟨c ^^^ (x ^^^ y), h1, xorC_eq c x y⟩)

/-- **Mex step for chocolate bars with two functions.** Let $g, h : \mathbb{N} \to \mathbb{N}$
have the NS property, and let $x, y, z, c$ be natural numbers with $x \le g(z)$, $y \le h(z)$
and $c < x \oplus y \oplus z$, where $\oplus$ is nim-sum (bitwise exclusive or). Then
$c = u \oplus y \oplus z$ for some $u < x$, or $c = x \oplus v \oplus z$ for some $v < y$, or
$c = \min(g(w), x) \oplus \min(h(w), y) \oplus w$ for some $w < z$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (b) (`integers-2025-G3-lem-3`). -/
public theorem exists_of_lt_xor_xor {g h : ℕ → ℕ}
    (hg : HasNSProperty g) (hh : HasNSProperty h) {x y z c : ℕ} (hx : x ≤ g z)
    (hy : y ≤ h z) (hc : c < x ^^^ y ^^^ z) :
    (∃ u < x, c = u ^^^ y ^^^ z) ∨ (∃ v < y, c = x ^^^ v ^^^ z) ∨
      ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w := by
  rcases nim_trichotomy hc with ⟨u, hu, hueq⟩ | ⟨v, hv, hveq⟩ | ⟨w₀, hw₀, hw₀eq⟩
  · exact Or.inl ⟨u, hu, hueq⟩
  · exact Or.inr (Or.inl ⟨v, hv, hveq⟩)
  · have hset := image_foldl_xor_eq_image_min (f := ![g, h]) (x := ![x, y])
      (Fin.forall_fin_two.mpr ⟨hg, hh⟩) (Fin.forall_fin_two.mpr ⟨hx, hy⟩)
    have hmem : c ∈ {c | ∃ w < z, c = (List.ofFn ![x, y]).foldl (· ^^^ ·) 0 ^^^ w} :=
      ⟨w₀, hw₀, by simpa using hw₀eq⟩
    obtain ⟨w, hw, hweq⟩ := hset ▸ hmem
    exact Or.inr (Or.inr ⟨w, hw, by simpa [min_comm] using hweq⟩)

end

end HasNSProperty

end MetaMathlibExt
