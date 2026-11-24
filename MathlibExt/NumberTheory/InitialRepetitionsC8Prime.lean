/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.InitialRepetitionsC8

/-!
# Prime-progression parity for partitions with a distinguished even part

For index `j`, remove one copy of each even part from `2` through `2j`. The remaining parts
are a subset of the integers from `1` through `j` and the even parts larger than `2j`.
The empty staircase accounts for the distinct-even-part term. This description gives the
coefficients of the second Rogers–Ramanujan series times the square of the Euler product
over the field of two elements.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The initial-repetitions partition function $c_8'$.** For $n \ge 0$, $c_8'(n)$ is the number
of partitions of $n$ into distinct even parts plus the sum, over $m = 1, \dots, n$, of the number
of partitions of $n$ in which every even number $2i$ with $1 \le i \le m$ is a part, every even
part at most $m$ appears at most twice, every odd part at most $m$ appears exactly once, and every
part greater than $m$ is even and appears exactly once.

Equivalently, $c_8'(n)$ counts partitions of $n$ with a possibly distinguished part: either all
parts are even and distinct and no part is distinguished, or a part $2m$ is distinguished and the
conditions above hold for $m$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 4 (definition of `c₈'`). -/
public def initialRepetitionsC8Prime (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
      ∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1).card +
    ∑ m ∈ Finset.Icc 1 n, ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
      (∀ i ∈ Finset.Icc 1 m, 2 * i ∈ p.parts) ∧
        (∀ a ∈ p.parts, Even a → a ≤ m → p.parts.count a ≤ 2) ∧
        (∀ a ∈ p.parts, Odd a → a ≤ m → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, m < a → Even a ∧ p.parts.count a = 1).card

end

namespace initialRepetitionsC8Prime_prime_mul_add_even

open Finset PowerSeries

/-- Partitions counted with the specified staircase. Index zero means no distinguished part. -/
private def marked (N j : ℕ) : Finset (Nat.Partition N) :=
  univ.filter fun p =>
    (∀ i ∈ Icc 1 j, 2 * i ∈ p.parts) ∧
      (∀ a ∈ p.parts, Even a → a ≤ j → p.parts.count a ≤ 2) ∧
      (∀ a ∈ p.parts, Odd a → a ≤ j → p.parts.count a = 1) ∧
      ∀ a ∈ p.parts, j < a → Even a ∧ p.parts.count a = 1

private theorem sum_marked (N : ℕ) : initialRepetitionsC8Prime N =
    ∑ j ∈ range (N + 1), (marked N j).card := by
  have h0 : marked N 0 = univ.filter (fun p : Nat.Partition N =>
      ∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1) := by
    ext p
    simp only [marked, mem_filter, mem_univ, true_and]
    constructor
    · exact fun h a ha => h.2.2.2 a ha (p.parts_pos ha)
    · intro h
      refine ⟨by simp, ?_, ?_, fun a ha _ => h a ha⟩
      · intro a ha _ hle
        have := p.parts_pos ha
        omega
      · exact fun a ha _ _ => (h a ha).2
  have hi : range (N + 1) = insert 0 (Icc 1 N) := by ext; simp; omega
  rw [hi, sum_insert (by simp), h0]
  rfl

private def staircase (j : ℕ) := (Icc 1 j).image fun i => 2 * i

private theorem mem_staircase {a j : ℕ} :
    a ∈ staircase j ↔ 0 < a ∧ Even a ∧ a ≤ 2 * j := by
  simp only [staircase, mem_image, mem_Icc, Nat.even_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨a / 2, by omega, by omega⟩

private theorem staircase_sum (j : ℕ) : (staircase j).val.sum = j ^ 2 + j := by
  rw [Finset.sum_val, staircase, sum_image (by intro a _ b _ h; dsimp at h; omega)]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ (j + 1 : ℕ)), ih]
    dsimp
    ring

private def optional (N j : ℕ) := Icc 1 j ∪ (Ioc j N).image (fun i => 2 * i)

private theorem mem_optional {a N j : ℕ} :
    a ∈ optional N j ↔ (0 < a ∧ a ≤ j) ∨ (Even a ∧ 2 * j < a ∧ a ≤ 2 * N) := by
  simp only [optional, mem_union, mem_Icc, mem_image, mem_Ioc, Nat.even_iff]
  constructor
  · rintro (h | ⟨i, h, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨a / 2, by omega, by omega⟩

private theorem count_parts (a : ℕ) (s : Finset ℕ) :
    s.val.count a = if a ∈ s then 1 else 0 := by
  split
  · exact Multiset.nodup_iff_count_eq_one.mp s.nodup a ‹_›
  · exact Multiset.count_eq_zero.mpr ‹_›

/-- A partition with staircase `j` has one compulsory copy of each staircase part
and at most one additional copy of each optional part. -/
private theorem mem_marked {N j : ℕ} (p : Nat.Partition N) : p ∈ marked N j ↔
    ∀ a, (staircase j).val.count a ≤ p.parts.count a ∧
      p.parts.count a ≤ (staircase j).val.count a + (optional N j).val.count a := by
  simp only [marked, mem_filter, mem_univ, true_and, count_parts]
  constructor
  · rintro ⟨hmem, he, ho, hlarge⟩ a
    by_cases ha : a ∈ p.parts
    · have hp := p.parts_pos ha
      have hn := p.le_of_mem_parts ha
      have hc := Multiset.count_pos.mpr ha
      have hlarge' := hlarge a ha
      have he' := he a ha
      have ho' := ho a ha
      simp only [mem_staircase, mem_optional, Nat.even_iff, Nat.odd_iff] at *
      split_ifs <;> omega
    · have hs : a ∉ staircase j := fun h => by
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h
        exact ha (hmem i hi)
      simp [hs, Multiset.count_eq_zero.mpr ha]
  · intro h
    constructor
    · intro i hi
      have hm : 2 * i ∈ staircase j := mem_image.mpr ⟨i, hi, rfl⟩
      apply Multiset.count_pos.mp
      have hc := (h (2 * i)).1
      simp only [hm, ite_true] at hc
      omega
    · have bounds (a) := (h a).2
      simp only [mem_staircase, mem_optional, Nat.even_iff] at bounds
      refine ⟨?_, ?_, ?_⟩
      · intro a ha he hj
        have H := bounds a
        split_ifs at H <;> omega
      · intro a ha ho hj
        have H := bounds a
        have hc := Multiset.count_pos.mpr ha
        have hpar := Nat.odd_iff.mp ho
        split_ifs at H <;> omega
      · intro a ha hj
        have H := bounds a
        have hc := Multiset.count_pos.mpr ha
        rw [Nat.even_iff]
        split_ifs at H <;> omega

private def subsets (N j : ℕ) :=
  (optional N j).powerset.filter fun s => j ^ 2 + j + s.val.sum = N

private theorem mem_subsets {N j : ℕ} {s : Finset ℕ} :
    s ∈ subsets N j ↔ s ⊆ optional N j ∧ j ^ 2 + j + s.val.sum = N := by
  simp [subsets]

private def assemble {N j : ℕ} {s : Finset ℕ} (h : s ∈ subsets N j) : Nat.Partition N where
  parts := (staircase j).val + s.val
  parts_pos := by
    intro a ha
    rcases Multiset.mem_add.mp ha with hm | hs
    · exact (mem_staircase.mp hm).1
    · have := mem_optional.mp ((mem_subsets.mp h).1 hs)
      omega
  parts_sum := by simpa only [Multiset.sum_add, staircase_sum] using (mem_subsets.mp h).2

private theorem card_marked (N j : ℕ) : (marked N j).card = (subsets N j).card := by
  classical
  symm
  apply card_bij (fun s hs => assemble hs)
  · intro s hs
    apply (mem_marked _).mpr
    intro a
    simp only [assemble, Multiset.count_add, Nat.le_add_right, Nat.add_le_add_iff_left, true_and]
    simp only [count_parts]
    split
    · simp [(mem_subsets.mp hs).1 ‹_›]
    · exact Nat.zero_le _
  · intro s hs t ht he
    exact Finset.val_inj.mp (add_left_cancel (congrArg Nat.Partition.parts he))
  · intro p hp
    let s := (optional N j).filter fun a => (staircase j).val.count a < p.parts.count a
    have he : (staircase j).val + s.val = p.parts := by
      ext a
      have H := (mem_marked _).mp hp a
      simp only [Multiset.count_add, count_parts, s, mem_filter]
      simp only [count_parts] at H
      by_cases hm : a ∈ staircase j <;> by_cases ho : a ∈ optional N j <;>
        simp only [hm, ho, true_and, false_and, ↓reduceIte] at H ⊢ <;>
        (try split) <;> omega
    have hs : s ∈ subsets N j := mem_subsets.mpr ⟨filter_subset _ _, by
      simpa only [Multiset.sum_add, staircase_sum, p.parts_sum] using congrArg Multiset.sum he⟩
    exact ⟨s, hs, Nat.Partition.ext he⟩

private theorem coeff_formula (N : ℕ) : (initialRepetitionsC8Prime N : ZMod 2) =
    coeff N (∑ j ∈ range (N + 1), X ^ (j ^ 2 + j) * ∏ a ∈ optional N j, (1 + X ^ a)) := by
  rw [sum_marked, Nat.cast_sum, map_sum]
  apply sum_congr rfl
  intro j _
  rw [card_marked, subsets, prod_one_add, mul_sum, map_sum, natCast_card_filter]
  apply sum_congr rfl
  intro s _
  rw [prod_pow_eq_pow_sum, ← pow_add, coeff_X_pow, Finset.sum_val]
  simp [eq_comm]

end initialRepetitionsC8Prime_prime_mul_add_even

open initialRepetitionsC8Prime_prime_mul_add_even in
/-- **$c_8'(N)$ is even when $15N + 4$ is not a square.** Let $c_8'$ be the partition function
that counts partitions with a possibly distinguished part. For every integer $N \ge 0$ such that
$15N + 4$ is not a perfect square, $c_8'(N)$ is even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 13 (`integers-2025-A32-thm-13`). -/
public theorem initialRepetitionsC8Prime_even_of_not_isSquare (N : ℕ)
    (hN : ¬ IsSquare (15 * N + 4)) :
    Even (initialRepetitionsC8Prime N) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  exact (coeff_formula N).trans (coeff_staircase_eq_zero N hN)

-- The modular reduction holds for any modulus and residue satisfying the nonsquare condition.
set_option linter.unusedVariables false in
/-- **Parity of $c_8'$ on residue classes modulo a prime.** Let $c_8'$ be the partition function
that counts partitions with a possibly distinguished part. Let $p \ge 7$ be a prime and let $r$ be
an integer with $1 \le r \le p - 1$ such that $15r + 4$ is not a square modulo $p$. Then
$c_8'(pn + r)$ is even for every integer $n \ge 0$.

Here $x$ is a square modulo $p$ when $x \equiv y^2 \pmod{p}$ for some integer $y$, so multiples
of $p$ count as squares.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 4 (`integers-2025-A32-cor-4`). -/
public theorem initialRepetitionsC8Prime_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h15 : ¬ IsSquare ((15 * r + 4 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC8Prime (p * n + r)) := by
  apply initialRepetitionsC8Prime_even_of_not_isSquare
  rintro ⟨x, hx⟩
  apply h15
  exact ⟨(x : ZMod p), by simpa using congrArg (fun a : ℕ => (a : ZMod p)) hx⟩

end MetaMathlibExt
