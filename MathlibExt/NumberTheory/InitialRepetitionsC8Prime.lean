/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
import MathlibExt.NumberTheory.DivisorCountParity

/-!
# Parity of $c_8'$ on residue classes modulo a prime

The partition function $c_8'$ counts partitions with a possibly distinguished part. The main
result, `MetaMathlibExt.initialRepetitionsC8Prime_prime_mul_add_even`, says that $c_8'(pn + r)$ is
even for every $n \ge 0$ when $p \ge 7$ is a prime and $15r + 4$ is not a square modulo $p$.

For a fixed index $m$, first remove one copy of each of the compulsory parts $2, 4, \dots, 2m$.
The remaining parts form a subset of the optional parts. Modulo two, the generating series of
$c_8'$ is the second Rogers–Ramanujan series times the square of the Euler product. The pentagonal
number theorem expands one Euler factor. A finite form of the second Rogers–Ramanujan identity,
proved here by two steps of the Bailey chain relative to $a = q$ starting from the unit Bailey
pair, expands the remaining product. Completing the squares in the resulting exponents identifies
$c_8'(N)$ modulo two with the number of representations $5x^2 + 3y^2 = 8(15N + 4)$ with
$x \equiv 1 \pmod 6$ and $y \equiv 3 \pmod{10}$. Two involutions show that this number is even
when $15N + 4$ is not a perfect square, and the prime-progression statement follows by reducing
a square modulo $p$.

The argument is the one used for $c_8$ in `MathlibExt.NumberTheory.InitialRepetitionsC8`, with the
second Rogers–Ramanujan identity in place of the first.
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

open Finset PowerSeries MathlibExt

/-! ## Counting by the distinguished index -/

/-- The compulsory even parts `2, 4, …, 2m` for the index `m`. -/
private def mandatoryParts (m : ℕ) := (range m).image (fun i => 2 * i + 2)

/-- Possible additional parts of a partition of `N`, each with multiplicity at most one. -/
private def optionalParts (N m : ℕ) := Icc 1 m ∪ (Ioc m N).image (fun i => 2 * i)

private theorem mem_mandatoryParts (a m : ℕ) :
    a ∈ mandatoryParts m ↔ Even a ∧ 0 < a ∧ a ≤ 2 * m := by
  simp only [mandatoryParts, mem_image, mem_range, Nat.even_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨a / 2 - 1, by omega, by omega⟩

private theorem mem_optionalParts (a N m : ℕ) :
    a ∈ optionalParts N m ↔ (0 < a ∧ a ≤ m) ∨ (Even a ∧ 2 * m < a ∧ a ≤ 2 * N) := by
  simp only [optionalParts, mem_union, mem_Icc, mem_image, mem_Ioc, Nat.even_iff]
  constructor
  · rintro (h | ⟨i, h, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨a / 2, by omega⟩

private theorem mandatoryParts_sum (m : ℕ) : (mandatoryParts m).val.sum = m ^ 2 + m := by
  have inj : Function.Injective (fun i : ℕ => 2 * i + 2) := by
    intro i k h
    dsimp at h
    omega
  rw [Finset.sum_val]
  unfold mandatoryParts
  rw [sum_image inj.injOn]
  simp only [id_eq]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    ring

/-- Bounds on multiplicities for the index `m`. -/
private def fits {N : ℕ} (p : Nat.Partition N) (m : ℕ) :=
  ∀ a, (if a ∈ mandatoryParts m then 1 else 0) ≤ p.parts.count a ∧
    p.parts.count a ≤ (if a ∈ mandatoryParts m then 1 else 0) +
      (if a ∈ optionalParts N m then 1 else 0)

private theorem cond_iff_fits {N : ℕ} (p : Nat.Partition N) (m : ℕ) :
    ((∀ i ∈ Icc 1 m, 2 * i ∈ p.parts) ∧
      (∀ a ∈ p.parts, Even a → a ≤ m → p.parts.count a ≤ 2) ∧
      (∀ a ∈ p.parts, Odd a → a ≤ m → p.parts.count a = 1) ∧
      ∀ a ∈ p.parts, m < a → Even a ∧ p.parts.count a = 1) ↔ fits p m := by
  constructor
  · rintro ⟨hman, hev, hodd, hbig⟩ a
    simp only [mem_mandatoryParts, mem_optionalParts]
    by_cases ha : a ∈ p.parts
    · have hpos := p.parts_pos ha
      have hle := p.le_of_mem_parts ha
      have hc := Multiset.count_pos.mpr ha
      rcases Nat.even_or_odd a with he | ho
      · by_cases hm : a ≤ m
        · have h2 := hev a ha he hm
          simp only [he, hpos, show a ≤ 2 * m by omega, and_self, ↓reduceIte, hm, true_or]
          omega
        · have h1 := (hbig a ha (by omega)).2
          by_cases ham : a ≤ 2 * m
          · simp only [he, hpos, ham, and_self, ↓reduceIte]
            split <;> omega
          · simp only [he, hpos, ham, and_false, ↓reduceIte, hm, true_and,
              show 2 * m < a by omega, show a ≤ 2 * N by omega, or_true]
            omega
      · have hne : ¬ Even a := Nat.not_even_iff_odd.mpr ho
        by_cases hm : a ≤ m
        · have h1 := hodd a ha ho hm
          simp only [hne, false_and, ↓reduceIte, hpos, hm, and_self, true_or]
          omega
        · exact absurd (hbig a ha (by omega)).1 hne
    · rw [Multiset.count_eq_zero.mpr ha]
      have hnm : ¬ (Even a ∧ 0 < a ∧ a ≤ 2 * m) := by
        rintro ⟨he, hpos, ham⟩
        obtain ⟨i, rfl⟩ := he
        exact ha (by simpa [two_mul] using hman i (mem_Icc.mpr ⟨by omega, by omega⟩))
      simp only [hnm, ↓reduceIte, le_refl, zero_le, and_self]
  · intro h
    refine ⟨fun i hi => ?_, fun a ha he hm => ?_, fun a ha ho hm => ?_, fun a ha hm => ?_⟩
    · obtain ⟨hi1, hi2⟩ := mem_Icc.mp hi
      have H := (h (2 * i)).1
      simp only [mem_mandatoryParts, even_two_mul, show 0 < 2 * i by omega,
        show 2 * i ≤ 2 * m by omega, and_self, ↓reduceIte] at H
      exact Multiset.count_pos.mp (by omega)
    · have H := (h a).2
      split at H <;> split at H <;> omega
    · have hc := Multiset.count_pos.mpr ha
      have hne : ¬ Even a := Nat.not_even_iff_odd.mpr ho
      have H := (h a).2
      simp only [mem_mandatoryParts, hne, false_and, ↓reduceIte, zero_add] at H
      split at H <;> omega
    · have hc := Multiset.count_pos.mpr ha
      have H := (h a).2
      simp only [mem_mandatoryParts, mem_optionalParts] at H
      rcases Nat.even_or_odd a with he | ho
      · refine ⟨he, ?_⟩
        split at H <;> split at H <;> omega
      · have hne : ¬ Even a := Nat.not_even_iff_odd.mpr ho
        simp only [hne, false_and, ↓reduceIte, zero_add, show ¬ a ≤ m by omega, and_false,
          or_self] at H
        omega

/-- The choices of optional parts that complete the compulsory parts to a partition of `N`. -/
private def choices (N m : ℕ) :=
  (optionalParts N m).powerset.filter fun s => m ^ 2 + m + s.val.sum = N

private theorem count_val (a : ℕ) (s : Finset ℕ) :
    s.val.count a = if a ∈ s then 1 else 0 := by
  split
  · exact Multiset.nodup_iff_count_eq_one.mp s.nodup a ‹_›
  · exact Multiset.count_eq_zero.mpr ‹_›

private def makePartition {N m : ℕ} {s : Finset ℕ} (h : s ∈ choices N m) :
    Nat.Partition N where
  parts := (mandatoryParts m).val + s.val
  parts_pos := by
    intro a ha
    rcases Multiset.mem_add.mp ha with hb | hs
    · exact ((mem_mandatoryParts _ _).mp hb).2.1
    · have := (mem_optionalParts _ _ _).mp (mem_powerset.mp (mem_filter.mp h).1 hs)
      omega
  parts_sum := by
    rw [Multiset.sum_add, mandatoryParts_sum]
    exact (mem_filter.mp h).2

private theorem fits_make {N m : ℕ} {s : Finset ℕ} (h : s ∈ choices N m) :
    fits (makePartition h) m := by
  intro a
  simp only [makePartition, Multiset.count_add, count_val, Nat.le_add_right, true_and,
    Nat.add_le_add_iff_left]
  have hs := mem_powerset.mp (mem_filter.mp h).1
  split
  · simp [hs ‹_›]
  · exact Nat.zero_le _

/-- Removing the compulsory even parts gives a bijection with finite subset choices. -/
private theorem card_cond (N m : ℕ) :
    ((univ : Finset (Nat.Partition N)).filter fun p =>
      (∀ i ∈ Icc 1 m, 2 * i ∈ p.parts) ∧
        (∀ a ∈ p.parts, Even a → a ≤ m → p.parts.count a ≤ 2) ∧
        (∀ a ∈ p.parts, Odd a → a ≤ m → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, m < a → Even a ∧ p.parts.count a = 1).card = (choices N m).card := by
  symm
  apply card_bij (fun s hs => makePartition hs)
  · intro s hs
    exact mem_filter.mpr ⟨mem_univ _, (cond_iff_fits _ _).mpr (fits_make hs)⟩
  · intro s hs t ht he
    have he' := congrArg Nat.Partition.parts he
    change (mandatoryParts m).val + s.val = (mandatoryParts m).val + t.val at he'
    exact Finset.val_inj.mp (add_left_cancel he')
  · intro p hp
    have h := (cond_iff_fits _ _).mp (mem_filter.mp hp).2
    let s := (optionalParts N m).filter fun a => (mandatoryParts m).val.count a < p.parts.count a
    have hs : (mandatoryParts m).val + s.val = p.parts := by
      ext a
      have H := h a
      simp only [Multiset.count_add, count_val, s, mem_filter]
      by_cases hb : a ∈ mandatoryParts m <;> by_cases ho : a ∈ optionalParts N m <;>
        simp only [hb, ho, true_and, false_and, ↓reduceIte] at H ⊢ <;>
        (try split) <;> omega
    have hsum := congrArg Multiset.sum hs
    rw [Multiset.sum_add, mandatoryParts_sum, p.parts_sum] at hsum
    exact ⟨s, mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), hsum⟩,
      Nat.Partition.ext hs⟩

/-- The index `m = 0` accounts for the partitions into distinct even parts. -/
private theorem c8p_card (N : ℕ) :
    initialRepetitionsC8Prime N = ∑ m ∈ range (N + 1), (choices N m).card := by
  rw [sum_range_succ', ← card_cond N 0, add_comm]
  unfold initialRepetitionsC8Prime
  congr 1
  · congr 1
    apply filter_congr
    intro p _
    constructor
    · intro h
      exact ⟨fun i hi => absurd (mem_Icc.mp hi) (by omega),
        fun a ha _ h0 => absurd (p.parts_pos ha) (by omega),
        fun a ha _ h0 => absurd (p.parts_pos ha) (by omega), fun a ha _ => h a ha⟩
    · exact fun h a ha => h.2.2.2 a ha (p.parts_pos ha)
  · rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact sum_congr rfl fun m _ => by rw [add_comm 1 m, card_cond]

private theorem c8p_coeff (N : ℕ) : (initialRepetitionsC8Prime N : ZMod 2) =
    coeff N (∑ m ∈ range (N + 1), X ^ (m ^ 2 + m) * ∏ a ∈ optionalParts N m, (1 + X ^ a)) := by
  rw [c8p_card, Nat.cast_sum, map_sum]
  apply sum_congr rfl
  intro m _
  rw [prod_one_add, mul_sum, map_sum, choices, natCast_card_filter]
  apply sum_congr rfl
  intro s _
  rw [prod_pow_eq_pow_sum, ← pow_add, coeff_X_pow, Finset.sum_val]
  simp [eq_comm]

/-- Over the two-element field, a tail factor `1 + X^(2a)` is the square of `1 - X^a`. -/
private theorem c8p_factored (N : ℕ) : (initialRepetitionsC8Prime N : ZMod 2) =
    coeff N ((∏ i ∈ range N, (1 - X ^ (i + 1))) *
      ∑ j ∈ range (N + 1), X ^ (j ^ 2 + j) * ∏ i ∈ range (N - j), (1 - X ^ (j + i + 1))) := by
  rw [c8p_coeff, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjn := Nat.le_of_lt_succ (mem_range.mp hj)
  have hdis : Disjoint (Icc 1 j) ((Ioc j N).image (fun i => 2 * i)) := by
    simp only [disjoint_left, mem_Icc, mem_image, mem_Ioc]
    rintro a ha ⟨k, hk, rfl⟩
    omega
  have inj : Function.Injective (fun i : ℕ => 2 * i) := by
    intro i k h
    dsimp at h
    omega
  rw [optionalParts, prod_union hdis, prod_image inj.injOn]
  have hI (a b : ℕ) (f : ℕ → PowerSeries (ZMod 2)) :
      ∏ i ∈ Ioc a b, f i = ∏ t ∈ range (b - a), f (a + t + 1) := by
    rw [← Ico_succ_succ_eq_Ioc, prod_Ico_eq_prod_range]
    simp [Nat.add_right_comm]
  rw [show Icc 1 j = Ioc 0 j by ext; simp [Nat.succ_le_iff]]
  rw [hI, hI]
  simp only [Nat.sub_zero, Nat.zero_add]
  have splitN : N = j + (N - j) := by omega
  conv_rhs =>
    enter [1]
    rw [splitN, prod_range_add]
  let : CharP (PowerSeries (ZMod 2)) 2 := charP_of_injective_ringHom C_injective 2
  have he (a : ℕ) : 1 + (X : PowerSeries (ZMod 2)) ^ (2 * a) = (1 - X ^ a) * (1 - X ^ a) := by
    rw [CharTwo.sub_eq_add, ← sq, add_sq, show (2 : PowerSeries (ZMod 2)) = 0 by
      simpa using CharP.cast_eq_zero (PowerSeries (ZMod 2)) 2,
      zero_mul, zero_mul, add_zero, one_pow, ← pow_mul, Nat.mul_comm a 2]
  simp_rw [he, prod_mul_distrib, CharTwo.sub_eq_add]
  ring

/-! ## The q-Chu–Vandermonde sum and the Bailey lemma relative to `a = q` -/

private theorem chuVander_term {R : Type*} [CommRing R] (Q : R) (M a i : ℕ) (hi : i ≤ M) :
    Q ^ ((i + 1) ^ 2 + a * (i + 1)) * gaussBinom Q (M + 1) (i + 1)
      * ∏ t ∈ range (M + 1 - (i + 1)), (1 - Q ^ (a + (i + 1) + 1 + t))
    = (Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
        * ∏ t ∈ range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t)))
      + ((Q ^ ((i + 1) ^ 2 + (a + 1) * (i + 1)) * gaussBinom Q M (i + 1)
          * ∏ t ∈ range (M + 1 - (i + 1)), (1 - Q ^ (a + (i + 1) + 1 + t)))
        - (Q ^ (i ^ 2 + (a + 1) * i) * gaussBinom Q M i
          * ∏ t ∈ range (M + 1 - i), (1 - Q ^ (a + i + 1 + t)))) := by
  have hQ1 : ∏ t ∈ range (M + 1 - (i + 1)), (1 - Q ^ (a + (i + 1) + 1 + t))
      = ∏ t ∈ range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t)) := by
    rw [show M + 1 - (i + 1) = M - i by omega]
    exact prod_congr rfl fun t _ => by rw [show a + (i + 1) + 1 + t = a + 1 + i + 1 + t by omega]
  have hQ0 : ∏ t ∈ range (M + 1 - i), (1 - Q ^ (a + i + 1 + t))
      = (∏ t ∈ range (M - i), (1 - Q ^ ((a + 1) + i + 1 + t))) * (1 - Q ^ (a + i + 1)) := by
    rw [show M + 1 - i = (M - i) + 1 by omega, prod_range_succ']
    congr 1
    exact prod_congr rfl fun t _ => by rw [show a + i + 1 + (t + 1) = a + 1 + i + 1 + t by omega]
  have qE1 : Q ^ ((i + 1) ^ 2 + a * (i + 1)) = Q ^ (i ^ 2 + (a + 1) * i) * Q ^ (a + i + 1) := by
    rw [← pow_add]
    congr 1
    ring
  have qE2 : Q ^ ((i + 1) ^ 2 + (a + 1) * (i + 1))
      = Q ^ ((i + 1) ^ 2 + a * (i + 1)) * Q ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    ring
  rw [gaussBinom_succ_succ, hQ1, hQ0, qE2, qE1]
  ring

/-- The q-Chu–Vandermonde sum `∑ᵢ Q^(i² + a i) [M, i]_Q (Q^(a+i+1); Q)_{M-i} = 1`. -/
private theorem chuVander {R : Type*} [CommRing R] (Q : R) (M a : ℕ) :
    ∑ i ∈ range (M + 1), Q ^ (i ^ 2 + a * i) * gaussBinom Q M i
      * ∏ t ∈ range (M - i), (1 - Q ^ (a + i + 1 + t)) = 1 := by
  induction M generalizing a with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ', sum_congr rfl fun i hi =>
      chuVander_term Q M a i (Nat.lt_succ_iff.mp (mem_range.mp hi)), sum_add_distrib,
      sum_range_sub (fun k => Q ^ (k ^ 2 + (a + 1) * k) * gaussBinom Q M k
        * ∏ t ∈ range (M + 1 - k), (1 - Q ^ (a + k + 1 + t))) (M + 1), ih (a + 1),
      gaussBinom_eq_zero_of_lt Q M (M + 1) (Nat.lt_succ_self M)]
    simp

/-- The finite q-Pochhammer symbol `(q; q)_m` in `ℚ⟦X⟧`. -/
private noncomputable def poch (m : ℕ) : PowerSeries ℚ := qPochFin X m

/-- The inverse of `(q; q)_m`. -/
private noncomputable def ipoch (m : ℕ) : PowerSeries ℚ := (poch m)⁻¹

private theorem constantCoeff_poch (m : ℕ) : constantCoeff (poch m) = 1 := by
  simp [poch, qPochFin, map_prod]

private theorem poch_mul_ipoch (m : ℕ) : poch m * ipoch m = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp [constantCoeff_poch])

private theorem poch_add (a b : ℕ) :
    poch (a + b) = poch a * ∏ t ∈ range b, (1 - X ^ (a + t + 1)) := by
  simp only [poch, qPochFin, prod_range_add]

private theorem gaussBinom_eq {M k : ℕ} (h : k ≤ M) :
    gaussBinom (X : PowerSeries ℚ) M k = poch M * ipoch k * ipoch (M - k) := by
  have hp : gaussBinom (X : PowerSeries ℚ) M k * poch k * poch (M - k) = poch M :=
    gaussBinom_mul_qPochFin_mul_qPochFin _ M k h
  rw [← hp]
  linear_combination (gaussBinom (X : PowerSeries ℚ) M k) *
    ((poch_mul_ipoch k).symm * poch (M - k) * ipoch (M - k) - poch_mul_ipoch (M - k))

/-- Clear the denominators of a tail product. -/
private theorem tail_eq {a b : ℕ} (h : a ≤ b) :
    ∏ t ∈ range (b - a), (1 - (X : PowerSeries ℚ) ^ (a + t + 1)) = poch b * ipoch a := by
  have hs := poch_add a (b - a)
  rw [Nat.add_sub_cancel' h] at hs
  rw [hs]
  linear_combination (∏ t ∈ range (b - a), (1 - (X : PowerSeries ℚ) ^ (a + t + 1))) *
    (poch_mul_ipoch a).symm

/-- The Bailey kernel, a rescaled q-Chu–Vandermonde sum. -/
private theorem kernel (c M : ℕ) :
    ∑ i ∈ range (M + 1), X ^ (i ^ 2 + c * i) * ipoch (M - i) * ipoch i * ipoch (c + i) =
      ipoch M * ipoch (M + c) := by
  have hCV := chuVander (X : PowerSeries ℚ) M c
  set S := ∑ i ∈ range (M + 1), X ^ (i ^ 2 + c * i) * ipoch (M - i) * ipoch i * ipoch (c + i)
  have hS : S * (poch M * poch (M + c)) = 1 := by
    rw [← hCV, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hiM : i ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [gaussBinom_eq hiM]
    have ht := tail_eq (a := c + i) (b := M + c) (by omega)
    rw [show M + c - (c + i) = M - i by omega] at ht
    rw [show ∏ t ∈ range (M - i), (1 - (X : PowerSeries ℚ) ^ (c + i + 1 + t))
        = ∏ t ∈ range (M - i), (1 - (X : PowerSeries ℚ) ^ (c + i + t + 1)) from
      prod_congr rfl fun t _ => by rw [show c + i + 1 + t = c + i + t + 1 by omega], ht]
    ring
  linear_combination ipoch M * ipoch (M + c) * hS -
    S * poch (M + c) * ipoch (M + c) * poch_mul_ipoch M - S * poch_mul_ipoch (M + c)

/-- One step of the Bailey chain relative to `a = q`. -/
private theorem baileyStep (α β : ℕ → PowerSeries ℚ)
    (h : ∀ m, β m = ∑ r ∈ range (m + 1), α r * ipoch (m - r) * ipoch (m + r + 1)) (n : ℕ) :
    ∑ j ∈ range (n + 1), X ^ (j ^ 2 + j) * β j * ipoch (n - j) =
      ∑ r ∈ range (n + 1), X ^ (r ^ 2 + r) * α r * ipoch (n - r) * ipoch (n + r + 1) := by
  have hswap : ∑ j ∈ range (n + 1), X ^ (j ^ 2 + j) * β j * ipoch (n - j) =
      ∑ r ∈ range (n + 1), ∑ j ∈ Ico r (n + 1),
        X ^ (j ^ 2 + j) * (α r * ipoch (j - r) * ipoch (j + r + 1)) * ipoch (n - j) := by
    simp_rw [h, mul_sum, sum_mul, ← Nat.Ico_zero_eq_range]
    rw [← sum_Ico_Ico_comm]
  rw [hswap]
  refine sum_congr rfl fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 by omega]
  have hk := kernel (2 * r + 1) (n - r)
  rw [show n - r + (2 * r + 1) = n + r + 1 by omega] at hk
  calc ∑ i ∈ range (n - r + 1), X ^ ((r + i) ^ 2 + (r + i)) *
          (α r * ipoch (r + i - r) * ipoch (r + i + r + 1)) * ipoch (n - (r + i))
      = X ^ (r ^ 2 + r) * α r * ∑ i ∈ range (n - r + 1),
          X ^ (i ^ 2 + (2 * r + 1) * i) * ipoch (n - r - i) * ipoch i *
            ipoch (2 * r + 1 + i) := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [show r + i - r = i by omega, show r + i + r + 1 = 2 * r + 1 + i by omega,
          show n - (r + i) = n - r - i by omega, show (r + i) ^ 2 + (r + i) =
            (r ^ 2 + r) + (i ^ 2 + (2 * r + 1) * i) by ring, pow_add]
        ring
    _ = _ := by
        rw [hk]
        ring

/-! ## The unit Bailey pair relative to `a = q` -/

private theorem rothe_scale_term {R : Type*} [CommRing R] (Q x y : R) (m k : ℕ) :
    Q ^ (k.choose 2) * gaussBinom Q m k * (x * Q) ^ k * y ^ (m - k)
      = Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k) := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, pow_add, mul_pow]
  ring

private theorem rothe_succ_term {R : Type*} [CommRing R] (Q x y : R) (m k : ℕ) :
    Q ^ ((k + 1).choose 2) * gaussBinom Q (m + 1) (k + 1) * x ^ (k + 1)
        * y ^ (m + 1 - (k + 1))
      = x * (Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k))
        + Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1) * x ^ (k + 1)
          * y ^ (m - k) := by
  rw [show m + 1 - (k + 1) = m - k by omega, gaussBinom_succ_succ,
    Nat.choose_succ_succ' (k + 1), Nat.choose_one_right, pow_add]
  ring

/-- The homogeneous q-binomial theorem (Rothe). -/
private theorem rothe {R : Type*} [CommRing R] (Q x y : R) (m : ℕ) :
    ∏ i ∈ range m, (y + x * Q ^ i)
      = ∑ j ∈ range (m + 1), Q ^ (j.choose 2) * gaussBinom Q m j * x ^ j * y ^ (m - j) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    set S : R := ∑ k ∈ range (m + 1),
      Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m - k) with hS
    set T : R := ∑ k ∈ range (m + 1),
      Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1) * x ^ (k + 1) * y ^ (m - k) with hT
    have hL : ∏ i ∈ range (m + 1), (y + x * Q ^ i) = S * (y + x) := by
      rw [prod_range_succ']
      have hp : ∏ k ∈ range m, (y + x * Q ^ (k + 1)) = ∏ k ∈ range m, (y + (x * Q) * Q ^ k) :=
        prod_congr rfl fun k _ => by rw [pow_succ']; ring
      rw [hp, ih (x * Q), sum_congr rfl fun k _ => rothe_scale_term Q x y m k, hS]
      simp
    have hR : ∑ k ∈ range (m + 1 + 1),
          Q ^ (k.choose 2) * gaussBinom Q (m + 1) k * x ^ k * y ^ (m + 1 - k)
        = (x * S + T) + y ^ (m + 1) := by
      rw [sum_range_succ', sum_congr rfl fun k _ => rothe_succ_term Q x y m k, sum_add_distrib,
        ← mul_sum, hS, hT]
      simp
    have hTy : T + y ^ (m + 1) = y * S := by
      have h1 := sum_range_succ
        (fun k => Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m + 1 - k)) (m + 1)
      have h2 := sum_range_succ'
        (fun k => Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m + 1 - k)) (m + 1)
      have hyS : ∑ k ∈ range (m + 1),
          Q ^ ((k + 1).choose 2) * gaussBinom Q m k * x ^ k * y ^ (m + 1 - k) = y * S := by
        rw [hS, mul_sum]
        refine sum_congr rfl fun k hk => ?_
        rw [show m + 1 - k = (m - k) + 1 by have := mem_range.mp hk; omega, pow_succ]
        ring
      have hT' : ∑ k ∈ range (m + 1),
          Q ^ ((k + 1 + 1).choose 2) * gaussBinom Q m (k + 1) * x ^ (k + 1)
            * y ^ (m + 1 - (k + 1)) = T :=
        sum_congr rfl fun k _ => by rw [show m + 1 - (k + 1) = m - k by omega]
      have hc1 : (0 + 1 : ℕ).choose 2 = 0 := by decide
      rw [hyS, gaussBinom_eq_zero_of_lt Q m (m + 1) (Nat.lt_succ_self m), mul_zero, zero_mul,
        zero_mul, add_zero] at h1
      rw [hT', hc1, gaussBinom_zero_right, pow_zero, pow_zero, Nat.sub_zero] at h2
      linear_combination h1 - h2
    rw [hL, hR]
    linear_combination -hTy

/-- Fold a sum over `range (2n + 2)` around its midpoint. -/
private theorem sum_range_fold {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ range (2 * n + 2), f j = ∑ r ∈ range (n + 1), (f (n - r) + f (n + 1 + r)) := by
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, sum_range_add, sum_add_distrib,
    ← sum_range_reflect f (n + 1)]
  simp

private theorem two_mul_choose_two (k : ℕ) : 2 * (k.choose 2 : ℚ) = k * (k - 1) := by
  rw [Nat.cast_choose_two]
  ring

/-- The unit Bailey pair relative to `a = q`, with the factor `1 - q` absorbed. -/
private noncomputable def unitα (r : ℕ) : PowerSeries ℚ :=
  (-1) ^ r * X ^ (r.choose 2) * (1 - X ^ (2 * r + 1))

/-- Pair the terms `n - r` and `n + 1 + r` of a q-binomial expansion, where `n = b + 1`. -/
private theorem unit_pair_terms {b r : ℕ} (hr : r ≤ b + 1) :
    X ^ ((b + 1 - r).choose 2) * gaussBinom X (2 * (b + 1) + 1) (b + 1 - r) *
        (-1) ^ (b + 1 - r) * ((X : PowerSeries ℚ) ^ b) ^ (2 * (b + 1) + 1 - (b + 1 - r)) +
      X ^ ((b + 1 + 1 + r).choose 2) * gaussBinom X (2 * (b + 1) + 1) (b + 1 + 1 + r) *
        (-1) ^ (b + 1 + 1 + r) * (X ^ b) ^ (2 * (b + 1) + 1 - (b + 1 + 1 + r)) =
      (-1) ^ (b + 1) * X ^ ((b + 1).choose 2 + b ^ 2 + 2 * b) *
        (unitα r * gaussBinom X (2 * (b + 1) + 1) (b + 1 - r)) := by
  obtain ⟨a, ha⟩ : ∃ a, b + 1 = a + r := ⟨b + 1 - r, by omega⟩
  have hq : (b : ℚ) + 1 = a + r := by exact_mod_cast ha
  have hsym : gaussBinom (X : PowerSeries ℚ) (2 * (b + 1) + 1) (b + 1 + 1 + r) =
      gaussBinom X (2 * (b + 1) + 1) (b + 1 - r) := by
    rw [gaussBinom_eq (by omega), gaussBinom_eq (by omega),
      show 2 * (b + 1) + 1 - (b + 1 + 1 + r) = b + 1 - r by omega,
      show 2 * (b + 1) + 1 - (b + 1 - r) = b + 1 + 1 + r by omega]
    ring
  have hsign : ((-1 : PowerSeries ℚ)) ^ (b + 1 - r) = (-1) ^ (b + 1) * (-1) ^ r := by
    rw [show b + 1 = (b + 1 - r) + r by omega, pow_add, mul_assoc, ← pow_add, ← two_mul,
      pow_mul]
    simp [show b + 1 - r + r - r = b + 1 - r by omega]
  have e1 : (b + 1 - r).choose 2 + b * (2 * (b + 1) + 1 - (b + 1 - r)) =
      ((b + 1).choose 2 + b ^ 2 + 2 * b) + r.choose 2 := by
    rw [show b + 1 - r = a by omega, show 2 * (b + 1) + 1 - a = b + r + 2 by omega]
    have ha2 := two_mul_choose_two a
    have hr2 := two_mul_choose_two r
    have hb2 := two_mul_choose_two (b + 1)
    push_cast at hb2
    apply Nat.cast_injective (R := ℚ)
    push_cast
    nlinarith
  have e2 : (b + 1 + 1 + r).choose 2 + b * (2 * (b + 1) + 1 - (b + 1 + 1 + r)) =
      ((b + 1).choose 2 + b ^ 2 + 2 * b) + r.choose 2 + (2 * r + 1) := by
    rw [show 2 * (b + 1) + 1 - (b + 1 + 1 + r) = a by omega]
    have ha2 := two_mul_choose_two a
    have hr2 := two_mul_choose_two r
    have hb2 := two_mul_choose_two (b + 1)
    have hc2 := two_mul_choose_two (b + 1 + 1 + r)
    push_cast at hb2 hc2
    apply Nat.cast_injective (R := ℚ)
    push_cast
    nlinarith
  rw [hsym, hsign, ← pow_mul, ← pow_mul, show (-1 : PowerSeries ℚ) ^ (b + 1 + 1 + r) =
    -((-1) ^ (b + 1) * (-1) ^ r) by rw [pow_add, pow_add, pow_one]; ring]
  have k1 : (X : PowerSeries ℚ) ^ ((b + 1 - r).choose 2) *
      X ^ (b * (2 * (b + 1) + 1 - (b + 1 - r)))
      = X ^ ((b + 1).choose 2 + b ^ 2 + 2 * b) * X ^ (r.choose 2) := by
    rw [← pow_add, ← pow_add, e1]
  have k2 : (X : PowerSeries ℚ) ^ ((b + 1 + 1 + r).choose 2) *
      X ^ (b * (2 * (b + 1) + 1 - (b + 1 + 1 + r)))
      = X ^ ((b + 1).choose 2 + b ^ 2 + 2 * b) * X ^ (r.choose 2) * X ^ (2 * r + 1) := by
    rw [← pow_add, ← pow_add, ← pow_add, e2]
  unfold unitα
  linear_combination ((-1) ^ (b + 1) * (-1) ^ r *
      gaussBinom (X : PowerSeries ℚ) (2 * (b + 1) + 1) (b + 1 - r)) * k1 -
    ((-1) ^ (b + 1) * (-1) ^ r * gaussBinom (X : PowerSeries ℚ) (2 * (b + 1) + 1) (b + 1 - r)) *
      k2

/-- The unit Bailey pair: the q-binomial expansion of a product with a vanishing factor. -/
private theorem unitPair (m : ℕ) :
    ∑ r ∈ range (m + 1), unitα r * ipoch (m - r) * ipoch (m + r + 1) =
      if m = 0 then 1 else 0 := by
  rcases m with _ | b
  · simp [unitα, ipoch, poch, qPochFin]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    have hR := rothe (X : PowerSeries ℚ) (-1) (X ^ b) (2 * (b + 1) + 1)
    rw [prod_eq_zero (i := b) (mem_range.mpr (by omega)) (by ring),
      show 2 * (b + 1) + 1 + 1 = 2 * (b + 1) + 2 by ring, sum_range_fold,
      sum_congr rfl fun r hr => unit_pair_terms (Nat.lt_succ_iff.mp (mem_range.mp hr)),
      ← mul_sum] at hR
    have hne : (-1 : PowerSeries ℚ) ^ (b + 1) * X ^ ((b + 1).choose 2 + b ^ 2 + 2 * b) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ X_ne_zero)
    have hz : ∑ r ∈ range (b + 1 + 1),
        unitα r * gaussBinom X (2 * (b + 1) + 1) (b + 1 - r) = 0 :=
      (mul_eq_zero.mp hR.symm).resolve_left hne
    have hg : ∀ r ∈ range (b + 1 + 1), unitα r * ipoch (b + 1 - r) * ipoch (b + 1 + r + 1) =
        ipoch (2 * (b + 1) + 1) * (unitα r * gaussBinom X (2 * (b + 1) + 1) (b + 1 - r)) := by
      intro r hr
      have hrb := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [gaussBinom_eq (by omega), show 2 * (b + 1) + 1 - (b + 1 - r) = b + 1 + r + 1 by omega]
      linear_combination (unitα r * ipoch (b + 1 - r) * ipoch (b + 1 + r + 1)) *
        (poch_mul_ipoch (2 * (b + 1) + 1)).symm
    rw [sum_congr rfl hg, ← mul_sum, hz, mul_zero]

/-! ## The finite second Rogers–Ramanujan identity and its truncation -/

/-- A summand of the partial theta sum of the second Rogers–Ramanujan identity. -/
private noncomputable def thetaTerm (r : ℕ) : PowerSeries ℚ :=
  (-1) ^ r * (X ^ (5 * r.choose 2 + 4 * r) - X ^ (5 * r.choose 2 + 6 * r + 1))

private theorem sq_eq_choose (r : ℕ) : r ^ 2 = 2 * r.choose 2 + r := by
  apply Nat.cast_injective (R := ℚ)
  push_cast
  linear_combination -two_mul_choose_two r

private theorem thetaTerm_eq (r : ℕ) :
    X ^ (r ^ 2 + r) * (X ^ (r ^ 2 + r) * unitα r) = thetaTerm r := by
  have h := sq_eq_choose r
  unfold thetaTerm unitα
  rw [show 5 * r.choose 2 + 6 * r + 1 = (r ^ 2 + r) + (r ^ 2 + r) + r.choose 2 + (2 * r + 1) by
    omega, show 5 * r.choose 2 + 4 * r = (r ^ 2 + r) + (r ^ 2 + r) + r.choose 2 by omega]
  simp only [pow_add]
  ring

/-- The finite form of the second Rogers–Ramanujan identity, from two Bailey steps. -/
private theorem finite_identity (n : ℕ) :
    ∑ j ∈ range (n + 1), X ^ (j ^ 2 + j) * ipoch j * ipoch (n - j) =
      ∑ r ∈ range (n + 1), thetaTerm r * ipoch (n - r) * ipoch (n + r + 1) := by
  have hI : ∀ m, ipoch m = ∑ r ∈ range (m + 1),
      (X ^ (r ^ 2 + r) * unitα r) * ipoch (m - r) * ipoch (m + r + 1) := by
    intro m
    have hs := baileyStep unitα (fun k => if k = 0 then 1 else 0) (fun k => (unitPair k).symm) m
    rw [sum_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd (by simp) h)] at hs
    simp only [ite_true, pow_zero, mul_one, Nat.sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, one_mul] at hs
    rw [hs]
  rw [baileyStep (fun r => X ^ (r ^ 2 + r) * unitα r) ipoch hI n]
  exact sum_congr rfl fun r _ => by rw [← thetaTerm_eq r]

private theorem X_pow_dvd_tail (e K : ℕ) :
    (X : PowerSeries ℚ) ^ e ∣ (∏ t ∈ range K, (1 - X ^ (e + t))) - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [prod_range_succ, show (∏ t ∈ range K, (1 - (X : PowerSeries ℚ) ^ (e + t))) *
        (1 - X ^ (e + K)) - 1 = ((∏ t ∈ range K, (1 - X ^ (e + t))) - 1) -
          (∏ t ∈ range K, (1 - X ^ (e + t))) * X ^ K * X ^ e by rw [pow_add]; ring]
    exact dvd_sub ih (dvd_mul_left _ _)

private theorem X_pow_dvd_poch_sub (a K : ℕ) :
    (X : PowerSeries ℚ) ^ (a + 1) ∣ poch (a + K) - poch a := by
  have ht : ∏ t ∈ range K, (1 - (X : PowerSeries ℚ) ^ (a + t + 1)) =
      ∏ t ∈ range K, (1 - X ^ ((a + 1) + t)) :=
    prod_congr rfl fun t _ => by rw [show a + t + 1 = a + 1 + t by omega]
  rw [poch_add, ht, show poch a * ∏ t ∈ range K, (1 - (X : PowerSeries ℚ) ^ ((a + 1) + t)) -
    poch a = poch a * ((∏ t ∈ range K, (1 - X ^ ((a + 1) + t))) - 1) by ring]
  exact dvd_mul_of_dvd_right (X_pow_dvd_tail _ _) _

private theorem X_pow_dvd_ratio_sub_one {a b : ℕ} (h : a ≤ b) :
    (X : PowerSeries ℚ) ^ (a + 1) ∣ poch b * ipoch a - 1 := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show poch (a + K) * ipoch a - 1 = (poch (a + K) - poch a) * ipoch a by
    rw [sub_mul, poch_mul_ipoch]]
  exact dvd_mul_of_dvd_left (X_pow_dvd_poch_sub a K) _

private theorem X_pow_dvd_ratio_sub_one' {a b : ℕ} (h : a ≤ b) :
    (X : PowerSeries ℚ) ^ (a + 1) ∣ poch a * ipoch b - 1 := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show poch a * ipoch (a + K) - 1 = -((poch (a + K) - poch a) * ipoch (a + K)) by
    rw [sub_mul, poch_mul_ipoch]; ring]
  exact dvd_neg.mpr (dvd_mul_of_dvd_left (X_pow_dvd_poch_sub a K) _)

private theorem X_pow_dvd_thetaTerm (r : ℕ) : (X : PowerSeries ℚ) ^ r ∣ thetaTerm r :=
  dvd_mul_of_dvd_right (dvd_sub (pow_dvd_pow _ (by omega)) (pow_dvd_pow _ (by omega))) _

/-- The truncated second Rogers–Ramanujan series with its denominators cleared. -/
private def tailSum {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  ∑ j ∈ range (n + 1), q ^ (j ^ 2 + j) * ∏ i ∈ range (n - j), (1 - q ^ (j + i + 1))

/-- The partial theta sum `∑ (-1)^r (q^(r(5r+3)/2) - q^((r+1)(5r+2)/2))`. -/
private def thetaSum {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  ∑ r ∈ range (n + 1),
    (-1) ^ r * (q ^ (5 * r.choose 2 + 4 * r) - q ^ (5 * r.choose 2 + 6 * r + 1))

/-- The truncated second Rogers–Ramanujan identity: both sums agree through degree `n`. -/
private theorem trunc (n : ℕ) :
    (X : PowerSeries ℚ) ^ (n + 1) ∣ tailSum X n - thetaSum X n := by
  have hT : tailSum (X : PowerSeries ℚ) n =
      ∑ j ∈ range (n + 1), X ^ (j ^ 2 + j) * (poch n * ipoch j) :=
    sum_congr rfl fun j hj => by rw [tail_eq (Nat.lt_succ_iff.mp (mem_range.mp hj))]
  have hM : ∑ j ∈ range (n + 1),
        X ^ (j ^ 2 + j) * (poch n * ipoch j) * (poch n * ipoch (n - j)) =
      ∑ r ∈ range (n + 1),
        thetaTerm r * ((poch n * ipoch (n - r)) * (poch n * ipoch (n + r + 1))) := by
    have h := congrArg (fun t => poch n * poch n * t) (finite_identity n)
    simp only [mul_sum] at h
    convert h using 2 <;> ring
  have key : tailSum (X : PowerSeries ℚ) n - thetaSum X n =
      ∑ j ∈ range (n + 1), X ^ (j ^ 2 + j) * (poch n * ipoch j) * (1 - poch n * ipoch (n - j)) +
        ∑ r ∈ range (n + 1),
          thetaTerm r * ((poch n * ipoch (n - r)) * (poch n * ipoch (n + r + 1)) - 1) := by
    rw [hT, show thetaSum (X : PowerSeries ℚ) n = ∑ r ∈ range (n + 1), thetaTerm r from rfl]
    simp only [mul_sub, mul_one, sum_sub_distrib]
    linear_combination hM
  rw [key]
  refine dvd_add (dvd_sum fun j hj => ?_) (dvd_sum fun r hr => ?_)
  · have hjn := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h1 : (X : PowerSeries ℚ) ^ (n - j + 1) ∣ 1 - poch n * ipoch (n - j) := by
      rw [← neg_sub]
      exact dvd_neg.mpr (X_pow_dvd_ratio_sub_one (by omega))
    have h2 := mul_dvd_mul (dvd_mul_right ((X : PowerSeries ℚ) ^ (j ^ 2 + j))
      (poch n * ipoch j)) h1
    rw [← pow_add] at h2
    exact (pow_dvd_pow _ (by omega)).trans h2
  · have hrn := Nat.lt_succ_iff.mp (mem_range.mp hr)
    have hU : (X : PowerSeries ℚ) ^ (n - r + 1) ∣ poch n * ipoch (n - r) - 1 :=
      X_pow_dvd_ratio_sub_one (by omega)
    have hV : (X : PowerSeries ℚ) ^ (n + 1) ∣ poch n * ipoch (n + r + 1) - 1 :=
      X_pow_dvd_ratio_sub_one' (by omega)
    rw [show thetaTerm r * ((poch n * ipoch (n - r)) * (poch n * ipoch (n + r + 1)) - 1) =
      thetaTerm r * (poch n * ipoch (n - r) - 1) * (poch n * ipoch (n + r + 1)) +
        thetaTerm r * (poch n * ipoch (n + r + 1) - 1) by ring]
    refine dvd_add (dvd_mul_of_dvd_left ?_ _) (dvd_mul_of_dvd_right hV _)
    have h := mul_dvd_mul (X_pow_dvd_thetaTerm r) hU
    rwa [← pow_add, show r + (n - r + 1) = n + 1 by omega] at h

/-! ## Euler and Rogers–Ramanujan coefficients modulo two -/

private theorem map_tail {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n : ℕ) : f (tailSum q n) = tailSum (f q) n := by
  simp [tailSum]

private theorem map_theta {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n : ℕ) : f (thetaSum q n) = thetaSum (f q) n := by
  simp [thetaSum]

/-- Compare integral coefficients over the rationals, then reduce them modulo two. -/
private theorem coeff_tail_eq_theta {n k : ℕ} (hk : k ≤ n) :
    coeff k (tailSum (X : PowerSeries (ZMod 2)) n) = coeff k (thetaSum X n) := by
  have h := (X_pow_dvd_iff.mp (trunc n)) k (by omega)
  rw [map_sub, sub_eq_zero] at h
  have hi : coeff k (tailSum (X : PowerSeries ℤ) n) = coeff k (thetaSum X n) := by
    apply Int.cast_injective (α := ℚ)
    change coeff k (map (Int.castRingHom ℚ) (tailSum X n)) =
      coeff k (map (Int.castRingHom ℚ) (thetaSum X n))
    simpa only [map_tail, map_theta, map_X] using h
  have hz := congrArg (Int.castRingHom (ZMod 2)) hi
  change coeff k (map (Int.castRingHom (ZMod 2)) (tailSum X n)) =
    coeff k (map (Int.castRingHom (ZMod 2)) (thetaSum X n)) at hz
  simpa only [map_tail, map_theta, map_X] using hz

private theorem finite_euler_coeff {n k : ℕ} (hk : k ≤ n) :
    coeff k (∏ i ∈ range n, (1 - X ^ (i + 1) : PowerSeries (ZMod 2))) =
      coeff k (pentagonalSeries (ZMod 2)) := by
  have hE := coeff_prod_one_sub_X_pow_eventually_eq (ZMod 2) k
  obtain ⟨s, hs⟩ := Filter.eventually_atTop.mp hE
  have h := hs (range n ∪ s) subset_union_right
  rw [← union_sdiff_self_eq_union, prod_union disjoint_sdiff] at h
  rw [coeff_mul_prod_one_sub_of_lt_order] at h
  · exact h
  · intro i hi
    have hb := (mem_sdiff.mp hi).2
    simp only [mem_range, not_lt] at hb
    rw [order_X_pow, Nat.cast_lt]
    omega

/-- The exponent `k(5k + 3)/2` of the second Rogers–Ramanujan theta sum, split by sign. -/
private def thetaExponent : ℤ → ℕ
  | .ofNat r => 5 * r.choose 2 + 4 * r
  | .negSucc r => 5 * r.choose 2 + 6 * r + 1

private def indices (N : ℕ) :=
  (range (N + 1)).image Int.ofNat ∪ (range (N + 1)).image Int.negSucc

private theorem mem_indices {N : ℕ} {k : ℤ} (h : thetaExponent k ≤ N) : k ∈ indices N := by
  cases k with
  | ofNat r =>
    simp only [thetaExponent] at h
    exact mem_union_left _ (mem_image.mpr ⟨r, mem_range.mpr (by omega), rfl⟩)
  | negSucc r =>
    simp only [thetaExponent] at h
    exact mem_union_right _ (mem_image.mpr ⟨r, mem_range.mpr (by omega), rfl⟩)

private theorem thetaSum_eq (N : ℕ) : thetaSum (X : PowerSeries (ZMod 2)) N =
    ∑ k ∈ indices N, X ^ thetaExponent k := by
  let : CharP (PowerSeries (ZMod 2)) 2 := charP_of_injective_ringHom C_injective 2
  have hd : Disjoint ((range (N + 1)).image Int.ofNat) ((range (N + 1)).image Int.negSucc) := by
    simp [disjoint_left]
  rw [indices, sum_union hd, sum_image Int.ofNat_injective.injOn,
    sum_image (fun _ _ _ _ h => Int.negSucc.inj h)]
  simp [thetaSum, thetaExponent, CharTwo.neg_eq, CharTwo.sub_eq_add, sum_add_distrib]

private theorem thetaExponent_sq (k : ℤ) :
    40 * (thetaExponent k : ℤ) + 9 = (10 * k + 3) ^ 2 := by
  have hc (r : ℕ) : 2 * (r.choose 2 : ℤ) = (r : ℤ) * (r - 1) := by
    exact_mod_cast (by rw [Nat.cast_choose_two]; ring : 2 * (r.choose 2 : ℚ) = r * (r - 1))
  cases k with
  | ofNat r =>
    simp only [thetaExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.ofNat_eq_natCast]
    linear_combination 100 * hc r
  | negSucc r =>
    simp only [thetaExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Int.negSucc_eq]
    linear_combination 100 * hc r

private theorem thetaExponent_injective : Function.Injective thetaExponent := by
  intro a b hab
  have H := thetaExponent_sq a
  rw [hab, thetaExponent_sq b] at H
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp H with h | h <;> omega

/-- `d` is a pentagonal exponent: `24d + 1 = x²` with `x ≡ 1 (mod 6)`. -/
private def hasPentagonalRoot (d : ℕ) := ∃ x : ℤ, x % 6 = 1 ∧ x ^ 2 = 24 * (d : ℤ) + 1

/-- `d` is a theta exponent: `40d + 9 = y²` with `y ≡ 3 (mod 10)`. -/
private def hasThetaRoot (d : ℕ) := ∃ y : ℤ, y % 10 = 3 ∧ y ^ 2 = 40 * (d : ℤ) + 9

private theorem theta_root (d : ℕ) : hasThetaRoot d ↔ ∃ k, thetaExponent k = d := by
  constructor
  · rintro ⟨y, hy, hs⟩
    let k := (y - 3) / 10
    have hk : 10 * k + 3 = y := by omega
    have H := thetaExponent_sq k
    rw [hk, hs] at H
    exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨10 * k + 3, by omega, (thetaExponent_sq k).symm⟩

private theorem coeff_theta {n d : ℕ} (hd : d ≤ n) :
    letI := Classical.propDecidable
    coeff d (thetaSum (X : PowerSeries (ZMod 2)) n) = if hasThetaRoot d then 1 else 0 := by
  classical
  rw [thetaSum_eq, map_sum]
  simp only [coeff_X_pow]
  split
  · rename_i h
    obtain ⟨k, hk⟩ := (theta_root _).mp h
    rw [sum_eq_single k]
    · simp [hk]
    · intro b _ hb
      exact ite_eq_right (fun H => hb (thetaExponent_injective (H.symm.trans hk.symm)))
    · exact fun hmem => (hmem (mem_indices (hk ▸ hd))).elim
  · rename_i h
    exact sum_eq_zero (fun k _ => ite_eq_right (fun he => h ((theta_root _).mpr ⟨k, he.symm⟩)))

private theorem coeff_pentagonal_root (d : ℕ) :
    letI := Classical.propDecidable
    coeff d (pentagonalSeries (ZMod 2)) = if hasPentagonalRoot d then 1 else 0 := by
  classical
  have hs (k : ℤ) : 24 * (pentagonal k : ℤ) + 1 = (1 - 6 * k) ^ 2 := by
    linarith [two_mul_natCast_pentagonal k]
  have equiv : hasPentagonalRoot d ↔ d ∈ Set.range pentagonal := by
    constructor
    · rintro ⟨x, hx, he⟩
      let k := (1 - x) / 6
      have hk : 1 - 6 * k = x := by omega
      have h := hs k
      rw [hk, he] at h
      exact ⟨k, by omega⟩
    · rintro ⟨k, rfl⟩
      exact ⟨1 - 6 * k, by omega, (hs _).symm⟩
  split
  · rename_i h
    obtain ⟨k, rfl⟩ := equiv.mp h
    rw [coeff_pentagonalSeries_pentagonal]
    rcases Int.even_or_odd k with he | ho
    · simp [Int.negOnePow_even k he]
    · simp [Int.negOnePow_odd k ho, CharTwo.neg_eq]
  · exact coeff_pentagonalSeries_eq_zero _ (fun h => ‹¬ hasPentagonalRoot d› (equiv.mpr h))

/-! ## Parity of the representation count -/

private def box (N : ℕ) : Finset ℤ :=
  Icc (-(8 * (15 * (N : ℤ) + 4))) (8 * (15 * (N : ℤ) + 4))

private def shell (N : ℕ) : Finset (ℤ × ℤ) :=
  ((box N) ×ˢ (box N)).filter fun (x, y) => 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 4)

private theorem mem_shell (N : ℕ) (x y : ℤ) :
    (x, y) ∈ shell N ↔ 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 4) := by
  simp only [shell, mem_filter, mem_product, box, mem_Icc, and_iff_right_iff_imp]
  intro h
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (y + 1),
      sq_nonneg x, sq_nonneg y]

/-- Choose the sign of the second coordinate by the congruence modulo four. -/
private def lattice (N : ℕ) :=
  (shell N).filter fun (x, y) => x % 3 = 1 ∧ x % 4 = y % 4

private theorem mem_lattice (N : ℕ) (x y : ℤ) :
    (x, y) ∈ lattice N ↔
      5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 4) ∧ x % 3 = 1 ∧ x % 4 = y % 4 := by
  simp [lattice, mem_shell]

/-- Put `d = (x - y)/4`. The reflection `(x, y) ↦ (x - 3d, x + d)` negates `d`.
Its fixed points have `x = y` and hence `15N + 4 = x²`. -/
private theorem even_lattice {N : ℕ} (hn : ¬ IsSquare (15 * N + 4)) :
    Even (lattice N).card := by
  let f : ℤ × ℤ → ℤ × ℤ := fun (x, y) =>
    let d := (x - y) / 4
    (x - 3 * d, x + d)
  have eqn {x y : ℤ} (h : x % 4 = y % 4) : 4 * ((x - y) / 4) = x - y := by omega
  apply Finset.even_card_of_involution (f := f)
  · rintro ⟨x, y⟩ h
    rcases (mem_lattice N x y).mp h with ⟨hQ, hx, hm⟩
    apply (mem_lattice _ _ _).mpr
    refine ⟨?_, by omega, by omega⟩
    have hd := eqn hm
    linear_combination hQ - (3 * y + 3 * x - 12 * ((x - y) / 4)) * hd
  · rintro ⟨x, y⟩ h
    have hm := ((mem_lattice N x y).mp h).2.2
    dsimp [f]
    congr 1 <;> omega
  · rintro ⟨x, y⟩ h he
    rcases (mem_lattice N x y).mp h with ⟨hQ, hx, hm⟩
    have he' := congrArg Prod.snd he
    dsimp [f] at he'
    have hxy : x = y := by omega
    subst y
    have H : (15 * N + 4 : ℕ) = x.natAbs * x.natAbs := by
      have hs : (15 * (N : ℤ) + 4) = x * x := by linarith
      exact_mod_cast (show 15 * (N : ℤ) + 4 = (x.natAbs : ℤ) * x.natAbs by
        simpa [Int.natCast_natAbs, ← abs_mul, abs_of_nonneg (mul_self_nonneg x)] using hs)
    exact hn ⟨_, H⟩

/-- When the coordinates are even, both signs of `y` satisfy the congruence modulo four.
The equation modulo five rules out the fixed points with `y = 0`. -/
private theorem even_even_lattice (N : ℕ) :
    Even ((lattice N).filter fun z => z.1 % 2 = 0).card := by
  apply Finset.even_card_of_involution (f := fun z => (z.1, -z.2))
  · rintro ⟨x, y⟩ h
    simp only [mem_filter, mem_lattice] at h ⊢
    obtain ⟨⟨hQ, hx, hm⟩, h2⟩ := h
    exact ⟨⟨by simpa using hQ, hx, by omega⟩, h2⟩
  · rintro ⟨x, y⟩ _
    simp
  · rintro ⟨x, y⟩ h he
    have hQ := ((mem_lattice _ _ _).mp (mem_filter.mp h).1).1
    have he' := congrArg Prod.snd he
    change - y = y at he'
    have : y = 0 := by omega
    subst y
    ring_nf at hQ
    omega

private theorem even_odd_lattice {N : ℕ} (hn : ¬ IsSquare (15 * N + 4)) :
    Even ((lattice N).filter fun z => z.1 % 2 ≠ 0).card := by
  have h := Finset.card_filter_add_card_filter_not (s := lattice N) (p := fun z => z.1 % 2 = 0)
  have he := even_even_lattice N
  have hall := even_lattice hn
  rw [← h, Nat.even_add] at hall
  exact hall.mp he

private def thetaPairs (N : ℕ) :=
  (shell N).filter fun (x, y) => x % 6 = 1 ∧ y % 10 = 3

private theorem mem_thetaPairs (N : ℕ) (x y : ℤ) :
    (x, y) ∈ thetaPairs N ↔
      5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 4) ∧ x % 6 = 1 ∧ y % 10 = 3 := by
  simp [thetaPairs, mem_shell]

private theorem y_mod_five {N : ℕ} {x y : ℤ}
    (h : 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 4)) : y % 5 = 2 ∨ y % 5 = 3 := by
  have he := congrArg (fun t : ℤ => (t : ZMod 5)) h
  push_cast at he
  have test : ∀ a b c : ZMod 5,
      5 * a ^ 2 + 3 * b ^ 2 = 8 * (15 * c + 4) → b = 2 ∨ b = 3 := by decide
  rcases test _ _ _ he with hy | hy
  · exact Or.inl ((ZMod.intCast_eq_intCast_iff y 2 5).mp (by simpa using hy))
  · exact Or.inr ((ZMod.intCast_eq_intCast_iff y 3 5).mp (by simpa using hy))

private theorem odd_mod_four {x : ℤ} (h : x % 2 = 1) : x % 4 = 1 ∨ x % 4 = 3 := by
  have he := Int.emod_emod_of_dvd x (by decide : (2 : ℤ) ∣ 4)
  omega

/-- For odd coordinates, precisely one sign of `y` gives the required residue modulo four. -/
private theorem even_thetaPairs {N : ℕ} (hn : ¬ IsSquare (15 * N + 4)) :
    Even (thetaPairs N).card := by
  rw [show (thetaPairs N).card =
      ((lattice N).filter fun z => z.1 % 2 ≠ 0).card from ?_]
  · exact even_odd_lattice hn
  apply Finset.card_nbij'
    (fun (x, y) => (x, if x % 4 = y % 4 then y else -y))
    (fun (x, y) => (x, if y % 10 = 3 then y else -y))
  · rintro ⟨x, y⟩ h
    obtain ⟨hQ, hx, hy⟩ := (mem_thetaPairs N x y).mp h
    change _ ∈ Finset.filter _ _
    simp only [mem_filter, mem_lattice]
    rcases odd_mod_four (x := x) (by omega) with h1 | h1 <;>
      rcases odd_mod_four (x := y) (by omega) with h2 | h2 <;> split <;> simp_all <;> omega
  · rintro ⟨x, y⟩ h
    change _ ∈ Finset.filter _ _ at h
    obtain ⟨⟨hQ, hx, hm⟩, ho⟩ := (show (_ ∧ _ ∧ _) ∧ x % 2 ≠ 0 by
      simpa only [mem_filter, mem_lattice] using h)
    apply (mem_thetaPairs N _ _).mpr
    have hy := y_mod_five hQ
    split <;> simp_all <;> omega
  · rintro ⟨x, y⟩ h
    obtain ⟨hQ, hx, hy⟩ := (mem_thetaPairs N x y).mp h
    dsimp only
    split <;> (try split) <;> simp_all
    omega
  · rintro ⟨x, y⟩ h
    change _ ∈ Finset.filter _ _ at h
    obtain ⟨⟨hQ, hx, hm⟩, ho⟩ := (show (_ ∧ _ ∧ _) ∧ x % 2 ≠ 0 by
      simpa only [mem_filter, mem_lattice] using h)
    dsimp only
    split <;> (try split) <;> simp_all
    omega

/-! ## Matching lattice points with the coefficient of the product -/

private noncomputable def degreePairs (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (antidiagonal N).filter fun (a, b) => hasPentagonalRoot a ∧ hasThetaRoot b

private theorem mem_degreePairs {N a b : ℕ} :
    (a, b) ∈ degreePairs N ↔ a + b = N ∧ hasPentagonalRoot a ∧ hasThetaRoot b := by
  classical
  simp [degreePairs]

private theorem c8p_degreePairs (N : ℕ) : (initialRepetitionsC8Prime N : ZMod 2) =
    ((degreePairs N).card : ZMod 2) := by
  classical
  rw [c8p_factored, coeff_mul]
  change _ = ((Finset.filter _ (antidiagonal N)).card : ZMod 2)
  rw [natCast_card_filter]
  apply sum_congr rfl
  rintro ⟨a, b⟩ hab
  have he := mem_antidiagonal.mp hab
  change _ * coeff b (tailSum X N) = _
  rw [finite_euler_coeff (by omega : a ≤ N), coeff_tail_eq_theta (by omega : b ≤ N),
    coeff_pentagonal_root, coeff_theta (by omega : b ≤ N)]
  split_ifs <;> simp_all

/-- Complete the two squares to identify pairs of series exponents with lattice points. -/
private theorem thetaPairs_card (N : ℕ) : (thetaPairs N).card = (degreePairs N).card := by
  classical
  let u (x : ℤ) := pentagonal ((1 - x) / 6)
  let v (y : ℤ) := thetaExponent ((y - 3) / 10)
  have hu (x : ℤ) (hx : x % 6 = 1) : x ^ 2 = 24 * (u x : ℤ) + 1 := by
    have h := two_mul_natCast_pentagonal ((1 - x) / 6)
    have he : x = 1 - 6 * ((1 - x) / 6) := by omega
    unfold u
    calc
      x ^ 2 = (1 - 6 * ((1 - x) / 6)) ^ 2 := congrArg (· ^ 2) he
      _ = _ := by linarith
  have hv (y : ℤ) (hy : y % 10 = 3) : y ^ 2 = 40 * (v y : ℤ) + 9 := by
    have he : 10 * ((y - 3) / 10) + 3 = y := by omega
    simpa only [v, he] using (thetaExponent_sq ((y - 3) / 10)).symm
  apply card_nbij (fun (x, y) => (u x, v y))
  · rintro ⟨x, y⟩ h
    obtain ⟨hQ, hx, hy⟩ := (mem_thetaPairs N x y).mp h
    apply mem_degreePairs.mpr
    refine ⟨?_, ⟨x, hx, hu x hx⟩, ⟨y, hy, hv y hy⟩⟩
    exact_mod_cast (show (u x : ℤ) + (v y : ℤ) = N by linarith [hu x hx, hv y hy])
  · rintro ⟨x, y⟩ h ⟨x', y'⟩ h' he
    obtain ⟨_, hx, hy⟩ := (mem_thetaPairs N x y).mp h
    obtain ⟨_, hx', hy'⟩ := (mem_thetaPairs N x' y').mp h'
    obtain ⟨ha, hb⟩ := Prod.mk.inj he
    have ex : x ^ 2 = x' ^ 2 := by rw [hu x hx, ha, ← hu x' hx']
    have ey : y ^ 2 = y' ^ 2 := by rw [hv y hy, hb, ← hv y' hy']
    apply Prod.ext
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp ex with h | h <;> dsimp <;> omega
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp ey with h | h <;> dsimp <;> omega
  · rintro ⟨a, b⟩ h
    obtain ⟨hab, ⟨x, hx, ex⟩, ⟨y, hy, ey⟩⟩ := mem_degreePairs.mp h
    have hQ : 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 4) := by
      rw [ex, ey, ← hab]
      push_cast
      ring
    refine ⟨⟨x, y⟩, (mem_thetaPairs N x y).mpr ⟨hQ, hx, hy⟩, ?_⟩
    have ha := hu x hx
    have hb := hv y hy
    change (u x, v y) = (a, b)
    congr 1 <;> omega

/-- The general nonsquare parity statement behind the prime-progression theorem. -/
private theorem even_of_not_isSquare (N : ℕ) (hN : ¬ IsSquare (15 * N + 4)) :
    Even (initialRepetitionsC8Prime N) := by
  obtain ⟨k, hk⟩ := even_thetaPairs hN
  have h := c8p_degreePairs N
  rw [← thetaPairs_card, hk, Nat.cast_add, CharTwo.add_self_eq_zero] at h
  exact ZMod.natCast_eq_zero_iff_even.mp h

end initialRepetitionsC8Prime_prime_mul_add_even

-- The modular reduction also works without the bounds on the prime and residue.
set_option linter.unusedVariables false in
open initialRepetitionsC8Prime_prime_mul_add_even in
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
  apply even_of_not_isSquare
  rintro ⟨x, hx⟩
  apply h15
  refine ⟨(x : ZMod p), ?_⟩
  simpa using congrArg (fun a : ℕ => (a : ZMod p)) hx

end MetaMathlibExt
