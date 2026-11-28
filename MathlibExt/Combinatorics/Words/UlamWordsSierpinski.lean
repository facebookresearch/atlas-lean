/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.UlamWords
import all MathlibExt.Combinatorics.Words.UlamWords

/-!
# Ulam words and the discrete Sierpiński triangle

For natural numbers `x` and `y` with `1 ≤ y ≤ x`, the word `1^y 0^(x-y)` is Ulam exactly
when `(x, y)` is the singleton exception `(1, 1)` or belongs to the discrete Sierpiński triangle.
For words with both letters, the endpoint cuts give Pascal's recurrence modulo two, and Lucas's
theorem matches the odd binomial coefficients with the original and two translated copies at each
stage.

## References

* Paul Adutwum, Hopper Clark, Ro Emerson, Alexandra (Sasha) Sheydvasser,
  Arseniy (Senia) Sheydvasser, and Axelle Tougouma, *Distributions of Ulam Words up to Length 30*,
  INTEGERS 25 (2025), Article A102, Theorem 9, pp. 11–12.
* `MathlibExt.Combinatorics.Words.UlamWords`: the endpoint cut lemma
  `isUlamWord_three_ones_zeros_iff.block_succ` and the base-case and symmetry lemmas
  `isUlamWord_three_ones_zeros_iff.one_leading`,
  `isUlamWord_three_ones_zeros_iff.length_eq_one_of_replicate`,
  `isUlamWord_zeros_four_ones_zeros_iff.ulam_reverse` and
  `isUlamWord_map_not_and_ulamResidueCount_eq`. For Lucas's theorem in base two we use
  `card_ulam_zeros_one_zeros.odd_choose_digit` from the same module.
-/

namespace MetaMathlibExt

namespace isUlamWord_ones_zeros_iff_mem_discreteSierpinski

open isUlamWord_three_ones_zeros_iff isUlamWord_zeros_four_ones_zeros_iff
  card_ulam_zeros_one_zeros

private theorem block_iff_odd_choose (a b : ℕ) :
    IsUlamWord (block (a + 1) (b + 1)) ↔ Odd ((a + b).choose a) := by
  induction a generalizing b with
  | zero => simp [one_leading]
  | succ a ih =>
    induction b with
    | zero =>
      have hw := (isUlamWord_map_not_and_ulamResidueCount_eq.1 _ (one_leading (a + 2))).1
      have hr := (ulam_reverse _).2 hw
      simpa [block, List.map_append, List.reverse_append] using iff_true_intro hr
    | succ b ihb =>
      rw [block_succ (a + 1) (b + 1) (by omega), ih (b + 1), ihb,
        show a + 1 + (b + 1) = (a + (b + 1)) + 1 by omega, Nat.choose_succ_succ',
        show a + 1 + b = a + (b + 1) by omega, Nat.odd_add, ← Nat.not_odd_iff_even]

-- Iterate the low-bit criterion to separate the first n bits from the remaining ones.
private theorem odd_choose_add_pow_mul (n i j r s : ℕ) (hr : r < 2 ^ n) (hs : s < 2 ^ n) :
    Odd ((r + 2 ^ n * i).choose (s + 2 ^ n * j)) ↔ Odd (r.choose s) ∧ Odd (i.choose j) := by
  induction n generalizing r s with
  | zero =>
    have hr₀ : r = 0 := by simpa using hr
    have hs₀ : s = 0 := by simpa using hs
    simp [hr₀, hs₀]
  | succ n ih =>
    rw [pow_succ'] at hr hs ⊢
    rw [odd_choose_digit, odd_choose_digit r s]
    simp only [mul_assoc, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
    rw [ih (r / 2) (s / 2) (by omega) (by omega), and_assoc]

private theorem mem_stage_iff (n : ℕ) (p : ℕ × ℕ) :
    p ∈ discreteSierpinskiStage n ↔
      ∃ r s, p = (r + 2, s + 1) ∧ r < 2 ^ n ∧ Odd (r.choose s) := by
  have col_le_row {r s : ℕ} (h : Odd (r.choose s)) : s ≤ r := by
    by_contra! hlt
    simp [Nat.choose_eq_zero_of_lt hlt] at h
  induction n generalizing p with
  | zero =>
    simp only [discreteSierpinskiStage, pow_zero, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨0, 0, rfl, by decide, by decide⟩
    · rintro ⟨r, s, rfl, hr, ho⟩
      have hs := col_le_row ho
      exact Prod.ext (by omega) (by omega)
  | succ n ih =>
    have odd_left {r s : ℕ} (hr : r < 2 ^ n) (hs : s < 2 ^ n) :
        Odd ((r + 2 ^ n).choose s) ↔ Odd (r.choose s) := by
      simpa using odd_choose_add_pow_mul n 1 0 r s hr hs
    have odd_right {r s : ℕ} (hr : r < 2 ^ n) (hs : s < 2 ^ n) :
        Odd ((r + 2 ^ n).choose (s + 2 ^ n)) ↔ Odd (r.choose s) := by
      simpa using odd_choose_add_pow_mul n 1 1 r s hr hs
    simp only [discreteSierpinskiStage, Set.mem_union, Set.mem_image, pow_succ']
    constructor
    · rintro ((hp | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩)
      · obtain ⟨r, s, rfl, hr, ho⟩ := (ih p).1 hp
        exact ⟨r, s, rfl, by omega, ho⟩
      · obtain ⟨r, s, rfl, hr, ho⟩ := (ih q).1 hq
        refine ⟨r + 2 ^ n, s, ?_, by omega, (odd_left hr ((col_le_row ho).trans_lt hr)).2 ho⟩
        exact Prod.ext (Nat.add_right_comm _ _ _) rfl
      · obtain ⟨r, s, rfl, hr, ho⟩ := (ih q).1 hq
        refine ⟨r + 2 ^ n, s + 2 ^ n, ?_, by omega,
          (odd_right hr ((col_le_row ho).trans_lt hr)).2 ho⟩
        exact Prod.ext (Nat.add_right_comm _ _ _) (Nat.add_right_comm _ _ _)
    · rintro ⟨r, s, rfl, hr, ho⟩
      by_cases h : r < 2 ^ n
      · exact Or.inl (Or.inl ((ih _).2 ⟨r, s, rfl, h, ho⟩))
      have hrow : r - 2 ^ n < 2 ^ n := by omega
      have hcol := col_le_row ho
      by_cases hs : s < 2 ^ n
      · have ho' := (odd_left hrow hs).1 (by simpa only [Nat.sub_add_cancel (by omega : 2 ^ n ≤ r)])
        refine Or.inl (Or.inr ⟨(r - 2 ^ n + 2, s + 1),
          (ih _).2 ⟨_, _, rfl, hrow, ho'⟩, Prod.ext ?_ rfl⟩)
        change r - 2 ^ n + 2 + 2 ^ n = r + 2
        omega
      · have hs' : s - 2 ^ n < 2 ^ n := by omega
        have ho' := (odd_right hrow hs').1 (by
          simpa only [Nat.sub_add_cancel (by omega : 2 ^ n ≤ r),
            Nat.sub_add_cancel (by omega : 2 ^ n ≤ s)])
        refine Or.inr ⟨(r - 2 ^ n + 2, s - 2 ^ n + 1),
          (ih _).2 ⟨_, _, rfl, hrow, ho'⟩, Prod.ext ?_ ?_⟩
        · change r - 2 ^ n + 2 + 2 ^ n = r + 2
          omega
        · change s - 2 ^ n + 1 + 2 ^ n = s + 1
          omega

private theorem mem_triangle_iff (p : ℕ × ℕ) :
    p ∈ discreteSierpinski ↔ ∃ r s, p = (r + 2, s + 1) ∧ Odd (r.choose s) := by
  rw [discreteSierpinski, Set.mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨r, s, hp, _, ho⟩ := (mem_stage_iff n p).1 hn
    exact ⟨r, s, hp, ho⟩
  · rintro ⟨r, s, hp, ho⟩
    exact ⟨r, (mem_stage_iff r p).2 ⟨r, s, hp, Nat.lt_two_pow_self, ho⟩⟩

end isUlamWord_ones_zeros_iff_mem_discreteSierpinski

open isUlamWord_ones_zeros_iff_mem_discreteSierpinski isUlamWord_three_ones_zeros_iff in
/-- **Ulam words made of ones followed by zeros.** For natural numbers $x$ and $y$ with
$1 \le y \le x$, the word $1^y 0^{x-y}$ ($y$ ones followed by $x - y$ zeros) is an Ulam word if
and only if $(x, y) = (1, 1)$ or $(x, y)$ belongs to the discrete Sierpiński triangle
$\mathcal{S}$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 9
(precise form of Theorem 3). -/
public theorem isUlamWord_ones_zeros_iff_mem_discreteSierpinski (x y : ℕ) (hy : 1 ≤ y)
    (hyx : y ≤ x) :
    IsUlamWord (List.replicate y true ++ List.replicate (x - y) false) ↔
      (x, y) = (1, 1) ∨ (x, y) ∈ discreteSierpinski := by
  have hreplicate : IsUlamWord (List.replicate y true) ↔ y = 1 := by
    constructor
    · exact length_eq_one_of_replicate
    · rintro rfl
      decide
  rw [mem_triangle_iff]
  simp only [Prod.mk.injEq]
  by_cases h : y = x
  · subst x
    have hdiag : ¬ ∃ r s : ℕ, (y = r + 2 ∧ y = s + 1) ∧ Odd (r.choose s) := by
      rintro ⟨r, s, ⟨hr, hs⟩, ho⟩
      simp [Nat.choose_eq_zero_of_lt (by omega : r < s)] at ho
    simpa [hdiag] using hreplicate
  · have hpair : ¬(x = 1 ∧ y = 1) := by omega
    rw [or_iff_right hpair]
    have hword := block_iff_odd_choose (y - 1) (x - y - 1)
    rw [show y - 1 + 1 = y by omega, show x - y - 1 + 1 = x - y by omega,
      show y - 1 + (x - y - 1) = x - 2 by omega] at hword
    change IsUlamWord (block y (x - y)) ↔ _
    rw [hword]
    constructor
    · exact fun ho => ⟨x - 2, y - 1, ⟨by omega, by omega⟩, ho⟩
    · rintro ⟨r, s, ⟨rfl, rfl⟩, ho⟩
      simpa using ho

end MetaMathlibExt
