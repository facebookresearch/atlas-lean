/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.MinMax

/-! # Mex step for chocolate bars with one function

Every natural number below the nim-sum of an admissible position is attained by a move.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (a).
-/

namespace MetaMathlibExt.HasNSProperty

private theorem half {g : ℕ → ℕ} (hg : HasNSProperty g) :
    HasNSProperty (fun w ↦ g (2 * w) / 2) := by
  constructor
  · intro a b hab
    exact Nat.div_le_div_right (hg.1 (Nat.mul_le_mul_left 2 hab))
  · intro a b i hi hab
    have hab' : 2 * a / 2 ^ (i + 1) = 2 * b / 2 ^ (i + 1) := by
      simpa only [Nat.pow_succ', Nat.mul_div_mul_left _ _ (by decide : 0 < 2)] using hab
    have h := hg.2 (2 * a) (2 * b) (i + 1) (by omega) hab'
    have he : 2 * 2 ^ (i - 1) = 2 ^ i := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    simpa only [Nat.add_sub_cancel, Nat.div_div_eq_div_mul, he] using h

/-- **Mex step for chocolate bars with one function.** Let $g : \mathbb{N} \to \mathbb{N}$ have
the NS property, and let $x, z, c$ be natural numbers with $x \le g(z)$ and $c < x \oplus z$,
where $\oplus$ is nim-sum (bitwise exclusive or). Then $c = u \oplus z$ for some $u < x$, or
$c = \min(g(w), x) \oplus w$ for some $w < z$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (a) (`integers-2025-G3-lem-3`). -/
public theorem exists_of_lt_xor {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z c : ℕ} (hx : x ≤ g z) (hc : c < x ^^^ z) :
    (∃ u < x, c = u ^^^ z) ∨ ∃ w < z, c = min (g w) x ^^^ w := by
  induction z using Nat.strong_induction_on generalizing g x c with
  | ind z ih =>
    by_cases hz : z = 0
    · subst z
      exact Or.inl ⟨c, by simpa using hc, by simp⟩
    have hdiv := Nat.xor_div_two (a := x) (b := z)
    have hmod := Nat.xor_mod_two_eq (m := x) (n := z)
    by_cases hc' : c / 2 < x / 2 ^^^ z / 2
    · have hgpair : g (2 * (z / 2)) = g z := by
        simpa using hg.2 (2 * (z / 2)) z 1 (by decide) (by omega)
      have hx' : x / 2 ≤ g (2 * (z / 2)) / 2 := by
        rw [hgpair]
        exact Nat.div_le_div_right hx
      obtain ⟨u, hu, he⟩ | ⟨w, hw, he⟩ :=
        ih (z / 2) (by omega) (half hg) hx' hc'
      · let u' := 2 * u + (c + z) % 2
        have hu' : u' / 2 = u := by dsimp [u']; omega
        have hediv : (u' ^^^ z) / 2 = c / 2 := by
          rw [Nat.xor_div_two, hu', ← he]
        have hemod : (u' ^^^ z) % 2 = c % 2 := by
          rw [Nat.xor_mod_two_eq]
          dsimp [u']
          omega
        exact Or.inl ⟨u', by dsimp [u']; omega, by omega⟩
      · let a := min (g (2 * w)) x
        let w' := 2 * w + (c + a) % 2
        have hw' : w' / 2 = w := by dsimp [w']; omega
        have hgpair : g w' = g (2 * w) := by
          simpa using hg.2 w' (2 * w) 1 (by decide) (by simpa using hw')
        have hmin : a / 2 = min (g (2 * w) / 2) (x / 2) := by
          have hmono : Monotone (fun n : ℕ ↦ n / 2) :=
            fun _ _ h ↦ Nat.div_le_div_right h
          exact hmono.map_min
        have hediv : (a ^^^ w') / 2 = c / 2 := by
          rw [Nat.xor_div_two, hw', hmin, ← he]
        have hemod : (a ^^^ w') % 2 = c % 2 := by
          rw [Nat.xor_mod_two_eq]
          dsimp [w']
          omega
        refine Or.inr ⟨w', by dsimp [w']; omega, ?_⟩
        rw [hgpair]
        change c = a ^^^ w'
        omega
    · have he : c / 2 = x / 2 ^^^ z / 2 := by omega
      by_cases hxbit : x % 2 = 1
      · have hzbit : z % 2 = 0 := by omega
        have hediv : ((x - 1) ^^^ z) / 2 = c / 2 := by
          rw [Nat.xor_div_two, he]
          congr 1
          omega
        have hemod : ((x - 1) ^^^ z) % 2 = c % 2 := by
          rw [Nat.xor_mod_two_eq]
          omega
        exact Or.inl ⟨x - 1, by omega, by omega⟩
      · have hzbit : z % 2 = 1 := by omega
        have hgpair : g (z - 1) = g z := by
          simpa using hg.2 (z - 1) z 1 (by decide) (by omega)
        have hediv : (x ^^^ (z - 1)) / 2 = c / 2 := by
          rw [Nat.xor_div_two, he]
          congr 1
          omega
        have hemod : (x ^^^ (z - 1)) % 2 = c % 2 := by
          rw [Nat.xor_mod_two_eq]
          omega
        refine Or.inr ⟨z - 1, by omega, ?_⟩
        rw [hgpair, min_eq_right hx]
        omega

end MetaMathlibExt.HasNSProperty
