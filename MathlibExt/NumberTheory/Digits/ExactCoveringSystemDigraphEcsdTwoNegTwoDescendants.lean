/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraph
import Mathlib.Tactic.Ring

/-!
# Descendants in the digraph `G(2n, -2n + a)`

The descendants after a positive number of edges are characterized by two ranges of
coefficients of the offset, with the extreme coefficients stated separately.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 1.
-/

namespace MetaMathlibExt

private theorem isKDescendant_first (R : ℤ → ℤ → Prop) (k : ℕ) (m n : ℤ) :
    IsKDescendant R (k + 1) m n ↔ ∃ x, R m x ∧ IsKDescendant R k x n := by
  induction k generalizing n with
  | zero => simp [IsKDescendant]
  | succ k ih =>
    change (∃ y, IsKDescendant R (k + 1) m y ∧ R y n) ↔
      ∃ x, R m x ∧ ∃ y, IsKDescendant R k x y ∧ R y n
    simp only [ih]
    constructor
    · rintro ⟨y, ⟨x, hmx, hxy⟩, hyn⟩
      exact ⟨x, hmx, y, hxy, hyn⟩
    · rintro ⟨x, hmx, y, hxy, hyn⟩
      exact ⟨y, ⟨x, hmx, hxy⟩, hyn⟩

private theorem descendants_ranges (a m n : ℤ) (k : ℕ) :
    IsKDescendant (ecsdAdj ![2, -2] ![0, a]) (k + 1) m n ↔
      (∃ b : ℕ, b < 2 ^ k ∧ n = 2 ^ (k + 1) * m - b * a) ∨
      (∃ b : ℕ, 1 ≤ b ∧ b ≤ 2 ^ k ∧ n = -(2 ^ (k + 1) * m - b * a)) := by
  induction k generalizing m with
  | zero =>
    rw [isKDescendant_one, ecsdAdj_two]
    simp only [pow_zero, add_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨0, by omega, by simpa using h⟩
      · exact Or.inr ⟨1, by omega, by omega, by simpa [sub_eq_add_neg, add_comm] using h⟩
    · rintro (⟨b, hb, h⟩ | ⟨b, hb, hb', h⟩)
      · have : b = 0 := by omega
        subst b
        exact Or.inl (by simpa using h)
      · have : b = 1 := by omega
        subst b
        exact Or.inr (by simpa [sub_eq_add_neg, add_comm] using h)
  | succ k ih =>
    rw [isKDescendant_first]
    simp only [ecsdAdj_two, add_zero, or_and_right, exists_or, exists_eq_left]
    rw [ih, ih]
    have hpow : (2 : ℤ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by
      rw [pow_succ, mul_comm]
    have hbound : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by
      rw [pow_succ, mul_comm]
    have hcast : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 ^ (k + 1) := by
      simp
    constructor
    · rintro ((⟨b, hb, h⟩ | ⟨b, hb, hb', h⟩) | (⟨b, hb, h⟩ | ⟨b, hb, hb', h⟩))
      · refine Or.inl ⟨b, by omega, ?_⟩
        rw [h, hpow]
        ring
      · refine Or.inr ⟨b, hb, by omega, ?_⟩
        rw [h, hpow]
        ring
      · refine Or.inr ⟨2 ^ (k + 1) - b, by omega, by omega, ?_⟩
        rw [h, hpow, Nat.cast_sub (by omega), hcast]
        ring
      · refine Or.inl ⟨2 ^ (k + 1) - b, by omega, ?_⟩
        rw [h, hpow, Nat.cast_sub (by omega), hcast]
        ring
    · rintro (⟨b, hb, h⟩ | ⟨b, hb, hb', h⟩)
      · by_cases hsmall : b < 2 ^ k
        · refine Or.inl (Or.inl ⟨b, hsmall, ?_⟩)
          rw [h, hpow]
          ring
        · refine Or.inr (Or.inr ⟨2 ^ (k + 1) - b, by omega, by omega, ?_⟩)
          rw [h, hpow, Nat.cast_sub (by omega), hcast]
          ring
      · by_cases hsmall : b ≤ 2 ^ k
        · refine Or.inl (Or.inr ⟨b, hb, hsmall, ?_⟩)
          rw [h, hpow]
          ring
        · refine Or.inr (Or.inl ⟨2 ^ (k + 1) - b, by omega, ?_⟩)
          rw [h, hpow, Nat.cast_sub (by omega), hcast]
          ring

/-- **Descendants in the digraph $G(2n, -2n + a)$.** Let $a$ and $m$ be integers and let
$k \ge 1$. In the digraph $G(2n, -2n + a)$ on $\mathbb{Z}$, with an edge $x \to 2x$ and an edge
$x \to -2x + a$ for every integer $x$, the $k$-descendants of $m$ (the ends of directed walks of
exactly $k$ edges from $m$) are exactly the integers $2^k m$, the integers $2^k m - ba$ and
$-(2^k m - ba)$ for natural numbers $b$ with $1 \le b < 2^{k-1}$, and $-(2^k m - 2^{k-1} a)$.

This holds for every integer $a$, not only for odd $a$, for which $G(2n, -2n + a)$ is an exact
covering system digraph.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 1
(`integers-2026-A107-prop-1`). -/
public theorem ecsd_two_neg_two_descendants (a m n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    IsKDescendant (ecsdAdj ![2, -2] ![0, a]) k m n ↔
      n = 2 ^ k * m ∨
        (∃ b : ℕ, 1 ≤ b ∧ b < 2 ^ (k - 1) ∧
          (n = 2 ^ k * m - b * a ∨ n = -(2 ^ k * m - b * a))) ∨
        n = -(2 ^ k * m - 2 ^ (k - 1) * a)
    := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [descendants_ranges]
  have hpos : 0 < (2 : ℕ) ^ j := pow_pos (by decide) _
  constructor
  · rintro (⟨b, hb, h⟩ | ⟨b, hb, hb', h⟩)
    · by_cases hz : b = 0
      · subst b
        exact Or.inl (by simpa using h)
      · exact Or.inr (Or.inl ⟨b, by omega, hb, Or.inl h⟩)
    · by_cases heq : b = 2 ^ j
      · subst b
        exact Or.inr (Or.inr (by simpa using h))
      · exact Or.inr (Or.inl ⟨b, hb, by omega, Or.inr h⟩)
  · rintro (h | ⟨b, hb, hb', h | h⟩ | h)
    · exact Or.inl ⟨0, hpos, by simpa using h⟩
    · exact Or.inl ⟨b, hb', h⟩
    · exact Or.inr ⟨b, hb, by omega, h⟩
    · exact Or.inr ⟨2 ^ j, by omega, le_rfl, by simpa using h⟩

end MetaMathlibExt
