/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ChocolateBarNSProperty
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Init

/-! # Mex step for chocolate bars with two functions

The mex step for chocolate bars with two functions with the `NS` property: every value below
the nim-sum `x ⊕ y ⊕ z` is a nim-sum with one coordinate lowered or with the width cut, from
R. Miyadera, H. Manabe and A. Singh, *Generalizations of Two-Dimensional and
Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Lemma 3 (b).
The definition of the `NS` property is taken from the arXiv version (arXiv:2207.09134v1,
Section 2); nim-sum `⊕` is `Nat.xor` (`^^^`) and `Z≥0` is `ℕ`.
-/

namespace MetaMathlibExt

namespace HasNSProperty

@[expose] public section

/-- Xor-ing twice with the same number cancels. -/
private theorem xor_cancel_right (a b : ℕ) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The first Nim witness reproduces the target. -/
private theorem xorA_eq (c y z : ℕ) : c = ((c ^^^ z) ^^^ y) ^^^ y ^^^ z := by
  have e : (((c ^^^ z) ^^^ y) ^^^ y) = (c ^^^ z) := xor_cancel_right _ _
  rw [e]
  exact (xor_cancel_right c z).symm

/-- The second Nim witness reproduces the target. -/
private theorem xorB_eq (c x z : ℕ) : c = x ^^^ ((c ^^^ z) ^^^ x) ^^^ z := by
  have ein : x ^^^ ((c ^^^ z) ^^^ x) = c ^^^ z := by
    rw [← Nat.xor_assoc, Nat.xor_comm x (c ^^^ z), xor_cancel_right]
  calc c = (c ^^^ z) ^^^ z := (xor_cancel_right c z).symm
    _ = (x ^^^ ((c ^^^ z) ^^^ x)) ^^^ z := by rw [ein]

/-- The third Nim witness reproduces the target. -/
private theorem xorC_eq (c x y : ℕ) : c = (x ^^^ y) ^^^ (c ^^^ (x ^^^ y)) := by
  calc c = (c ^^^ (x ^^^ y)) ^^^ (x ^^^ y) := (xor_cancel_right c (x ^^^ y)).symm
    _ = (x ^^^ y) ^^^ (c ^^^ (x ^^^ y)) := Nat.xor_comm _ _

/-- Below a triple nim-sum, some pile can be lowered to hit the target. -/
private theorem nim_trichotomy {x y z c : ℕ} (hc : c < x ^^^ y ^^^ z) :
    (∃ u < x, c = u ^^^ y ^^^ z) ∨ (∃ v < y, c = x ^^^ v ^^^ z) ∨
      ∃ w < z, c = x ^^^ y ^^^ w := by
  rcases Nat.lt_xor_cases hc with h1 | h1
  · rcases Nat.lt_xor_cases h1 with h2 | h2
    · exact Or.inl ⟨(c ^^^ z) ^^^ y, h2, xorA_eq c y z⟩
    · exact Or.inr (Or.inl ⟨(c ^^^ z) ^^^ x, h2, xorB_eq c x z⟩)
  · exact Or.inr (Or.inr ⟨c ^^^ (x ^^^ y), h1, xorC_eq c x y⟩)

/-- The `j`-th bit of `n / 2` is the successor bit of `n`. -/
private theorem testBit_div_two (n j : ℕ) : (n / 2).testBit j = n.testBit j.succ := by
  conv_rhs => rw [← Nat.bit_bodd_div2 n]
  rw [Nat.testBit_bit_succ, Nat.div2_val]

/-- Halving distributes over `Nat.xor`. -/
private theorem xor_div_two (a b : ℕ) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_div_two, Nat.testBit_xor]

/-- Halving distributes over a triple `Nat.xor`. -/
private theorem xor3_div_two (a b d : ℕ) :
    (a ^^^ b ^^^ d) / 2 = a / 2 ^^^ b / 2 ^^^ d / 2 := by
  rw [xor_div_two, xor_div_two]

/-- The parity of a triple xor is the parity of the sum. -/
private theorem xor3_mod_two (a b d : ℕ) : (a ^^^ b ^^^ d) % 2 = (a + b + d) % 2 := by
  have h1 : (a ^^^ b) % 2 = (a + b) % 2 := Nat.xor_mod_two_eq
  have h2 : ((a ^^^ b) ^^^ d) % 2 = ((a ^^^ b) + d) % 2 := Nat.xor_mod_two_eq
  omega

/-- A number is determined by its half and its parity. -/
private theorem eq_of_div_two_eq_mod_two_eq {A C : ℕ} (hdiv : A / 2 = C / 2)
    (hmod : A % 2 = C % 2) : A = C := by
  have h1 := Nat.div_add_mod A 2
  have h2 := Nat.div_add_mod C 2
  omega

/-- Halving distributes over `min`. -/
private theorem min_div_two (a b : ℕ) : min a b / 2 = min (a / 2) (b / 2) := by
  omega

/-- An `NS` function takes equal values on numbers with equal halves. -/
private theorem ns_apply_eq_of_div_two_eq {g : ℕ → ℕ} (hg : HasNSProperty g) {w z : ℕ}
    (h : w / 2 = z / 2) : g w = g z := by
  have h' : w / 2 ^ 1 = z / 2 ^ 1 := by simpa using h
  have h2 := hg.2 w z 1 Nat.one_pos h'
  rwa [Nat.sub_self, pow_zero, Nat.div_one, Nat.div_one] at h2

/-- `(2 * n) / 2 ^ (i + 1) = n / 2 ^ i`. -/
private theorem two_mul_div_two_pow_succ (n i : ℕ) :
    (2 * n) / 2 ^ (i + 1) = n / 2 ^ i := by
  have h1 : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, ← Nat.div_div_eq_div_mul, h2]

/-- The even-input half of an `NS` function has the `NS` property. -/
private theorem half_ns {g : ℕ → ℕ} (hg : HasNSProperty g) :
    HasNSProperty fun n => g (2 * n) / 2 := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact Nat.div_le_div_right (hg.1 (show 2 * a ≤ 2 * b by omega))
  · intro n n' i hi hdiv
    change (g (2 * n) / 2) / 2 ^ (i - 1) = (g (2 * n') / 2) / 2 ^ (i - 1)
    have hpow : 2 * 2 ^ (i - 1) = 2 ^ i := by
      have h1 : i - 1 + 1 = i := by omega
      have h2 : 2 ^ (i - 1 + 1) = 2 * 2 ^ (i - 1) := pow_succ' 2 (i - 1)
      rw [← h2, h1]
    have e1 : (g (2 * n) / 2) / 2 ^ (i - 1) = g (2 * n) / 2 ^ i := by
      rw [Nat.div_div_eq_div_mul, hpow]
    have e2 : (g (2 * n') / 2) / 2 ^ (i - 1) = g (2 * n') / 2 ^ i := by
      rw [Nat.div_div_eq_div_mul, hpow]
    rw [e1, e2]
    have hdiv' : (2 * n) / 2 ^ (i + 1) = (2 * n') / 2 ^ (i + 1) := by
      rw [two_mul_div_two_pow_succ, two_mul_div_two_pow_succ]
      exact hdiv
    have hns := hg.2 (2 * n) (2 * n') (i + 1) (by omega) hdiv'
    rwa [Nat.add_sub_cancel] at hns

/-- `x / 2` is bounded by the halved function at `z / 2`. -/
private theorem half_le {g : ℕ → ℕ} {x z : ℕ} (hx : x ≤ g z) (hg : HasNSProperty g) :
    x / 2 ≤ g (2 * (z / 2)) / 2 := by
  have hgz : g z = g (2 * (z / 2)) :=
    ns_apply_eq_of_div_two_eq hg (show z / 2 = (2 * (z / 2)) / 2 by omega)
  rw [← hgz]
  exact Nat.div_le_div_right hx

/-- Lifting a halved first-pile witness to the original piles. -/
private theorem lift_exists_u {x y z c u' : ℕ} (hu' : u' < x / 2)
    (heq : c / 2 = u' ^^^ y / 2 ^^^ z / 2) : ∃ u < x, c = u ^^^ y ^^^ z := by
  refine ⟨2 * u' + (c + y + z) % 2, by omega, ?_⟩
  have hdiv : ((2 * u' + (c + y + z) % 2) ^^^ y ^^^ z) / 2 = c / 2 := by
    rw [xor3_div_two]
    have hu2 : (2 * u' + (c + y + z) % 2) / 2 = u' := by omega
    rw [hu2]
    exact heq.symm
  have hmod : ((2 * u' + (c + y + z) % 2) ^^^ y ^^^ z) % 2 = c % 2 := by
    rw [xor3_mod_two]
    omega
  exact (eq_of_div_two_eq_mod_two_eq hdiv hmod).symm

/-- Lifting a halved second-pile witness to the original piles. -/
private theorem lift_exists_v {x y z c v' : ℕ} (hv' : v' < y / 2)
    (heq : c / 2 = x / 2 ^^^ v' ^^^ z / 2) : ∃ v < y, c = x ^^^ v ^^^ z := by
  refine ⟨2 * v' + (c + x + z) % 2, by omega, ?_⟩
  have hdiv : (x ^^^ (2 * v' + (c + x + z) % 2) ^^^ z) / 2 = c / 2 := by
    rw [xor3_div_two]
    have hv2 : (2 * v' + (c + x + z) % 2) / 2 = v' := by omega
    rw [hv2]
    exact heq.symm
  have hmod : (x ^^^ (2 * v' + (c + x + z) % 2) ^^^ z) % 2 = c % 2 := by
    rw [xor3_mod_two]
    omega
  exact (eq_of_div_two_eq_mod_two_eq hdiv hmod).symm

/-- Lifting a halved width witness to a clamped chocolate move. -/
private theorem lift_exists_w {g h : ℕ → ℕ} (hg : HasNSProperty g) (hh : HasNSProperty h)
    {x y z c w' : ℕ} (hw' : w' < z / 2)
    (heq : c / 2 = min (g (2 * w') / 2) (x / 2) ^^^ min (h (2 * w') / 2) (y / 2) ^^^ w') :
    ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w := by
  set B : ℕ := (c + min (g (2 * w')) x + min (h (2 * w')) y) % 2 with hB
  refine ⟨2 * w' + B, by omega, ?_⟩
  have hgw : g (2 * w' + B) = g (2 * w') :=
    ns_apply_eq_of_div_two_eq hg (show (2 * w' + B) / 2 = (2 * w') / 2 by omega)
  have hhw : h (2 * w' + B) = h (2 * w') :=
    ns_apply_eq_of_div_two_eq hh (show (2 * w' + B) / 2 = (2 * w') / 2 by omega)
  have hdiv : (min (g (2 * w' + B)) x ^^^ min (h (2 * w' + B)) y ^^^ (2 * w' + B)) / 2 =
      c / 2 := by
    rw [hgw, hhw, xor3_div_two]
    have hw2 : (2 * w' + B) / 2 = w' := by omega
    rw [hw2, min_div_two, min_div_two]
    exact heq.symm
  have hmod : (min (g (2 * w' + B)) x ^^^ min (h (2 * w' + B)) y ^^^ (2 * w' + B)) % 2 =
      c % 2 := by
    rw [hgw, hhw, xor3_mod_two]
    omega
  exact (eq_of_div_two_eq_mod_two_eq hdiv hmod).symm

/-- The mex step, by strong induction on the width. -/
private theorem exists_of_lt_xor_xor_aux : ∀ (z : ℕ) (g h : ℕ → ℕ) (x y c : ℕ),
    HasNSProperty g → HasNSProperty h → x ≤ g z → y ≤ h z → c < x ^^^ y ^^^ z →
    (∃ u < x, c = u ^^^ y ^^^ z) ∨ (∃ v < y, c = x ^^^ v ^^^ z) ∨
      ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w := by
  intro z
  induction z using Nat.strong_induction_on with
  | ind z IH =>
    intro g h x y c hg hh hx hy hc
    rcases nim_trichotomy hc with ⟨u, hu, hueq⟩ | ⟨v, hv, hveq⟩ | ⟨w0, hw0, hw0eq⟩
    · exact Or.inl ⟨u, hu, hueq⟩
    · exact Or.inr (Or.inl ⟨v, hv, hveq⟩)
    · by_cases heq : c / 2 = (x ^^^ y ^^^ z) / 2
      · have hw02 : w0 / 2 = z / 2 := by
          have e1 : c / 2 = x / 2 ^^^ y / 2 ^^^ w0 / 2 := by
            rw [hw0eq]
            exact xor3_div_two _ _ _
          have e2 : (x ^^^ y ^^^ z) / 2 = x / 2 ^^^ y / 2 ^^^ z / 2 :=
            xor3_div_two _ _ _
          rw [e1, e2] at heq
          exact Nat.xor_right_inj.mp heq
        have hgw : g w0 = g z := ns_apply_eq_of_div_two_eq hg hw02
        have hhw : h w0 = h z := ns_apply_eq_of_div_two_eq hh hw02
        have hgx : min (g w0) x = x := by
          rw [hgw]
          exact min_eq_right hx
        have hgy : min (h w0) y = y := by
          rw [hhw]
          exact min_eq_right hy
        refine Or.inr (Or.inr ⟨w0, hw0, ?_⟩)
        rw [hgx, hgy]
        exact hw0eq
      · have hlt : c / 2 < (x ^^^ y ^^^ z) / 2 :=
          lt_of_le_of_ne (Nat.div_le_div_right (le_of_lt hc)) heq
        have hz2_lt : z / 2 < z := by omega
        have hX2 : (x ^^^ y ^^^ z) / 2 = x / 2 ^^^ y / 2 ^^^ z / 2 :=
          xor3_div_two _ _ _
        rw [hX2] at hlt
        obtain ⟨u', hu', hu'eq⟩ | ⟨v', hv', hv'eq⟩ | ⟨w', hw', hw'eq⟩ :=
          IH (z / 2) hz2_lt (fun n => g (2 * n) / 2) (fun n => h (2 * n) / 2) (x / 2)
            (y / 2) (c / 2) (half_ns hg) (half_ns hh) (half_le hx hg) (half_le hy hh) hlt
        · exact Or.inl (lift_exists_u hu' hu'eq)
        · exact Or.inr (Or.inl (lift_exists_v hv' hv'eq))
        · exact Or.inr (Or.inr (lift_exists_w hg hh hw' hw'eq))

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
      ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w :=
  exists_of_lt_xor_xor_aux z g h x y c hg hh hx hy hc

end

end HasNSProperty

end MetaMathlibExt
