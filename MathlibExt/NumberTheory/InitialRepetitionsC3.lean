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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Parity of partitions counted by $c_3$

The parity of the initial-repetitions partition count $c_3$ on prime progressions follows
by reducing its generating series to the square and cube of Euler's product modulo two.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The initial-repetitions partition function $c_3$.** For $n \ge 0$, $c_3(n)$ is the number
of partitions of $n$ for which there is an integer $j$ with $1 \le j \le n$ such that the part $1$
appears exactly $j^2$ or $j^2 + 1$ times, every odd part larger than $1$ appears exactly once,
every even part appears exactly once, and every even part greater than $2j$ is at least $4j + 4$
and divisible by $4$.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₃`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC3 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    ∃ j ∈ Finset.Icc 1 n, (p.parts.count 1 = j ^ 2 ∨ p.parts.count 1 = j ^ 2 + 1) ∧
      (∀ a ∈ p.parts, Odd a → 1 < a → p.parts.count a = 1) ∧
      (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
      ∀ a ∈ p.parts, Even a → 2 * j < a → 4 * j + 4 ≤ a ∧ 4 ∣ a).card

end

namespace initialRepetitionsC3_prime_mul_add_even

open Finset MathlibExt PowerSeries

/-! ## The subset generating function -/

/-- The parts that can be added after the compulsory copies of one have been placed. -/
private def optionalParts (M j : ℕ) :=
  ((range M).image (fun i => 2 * i + 1) ∪ (range j).image (fun i => 2 * (i + 1))) ∪
    (Ico j M).image (fun i => 4 * (i + 1))

private theorem mem_optionalParts (a M j : ℕ) :
    a ∈ optionalParts M j ↔
      (Odd a ∧ a < 2 * M) ∨ (Even a ∧ 0 < a ∧ a ≤ 2 * j) ∨
        (4 * j + 4 ≤ a ∧ a ≤ 4 * M ∧ 4 ∣ a) := by
  simp only [optionalParts, mem_union, mem_image, mem_range, mem_Ico, Nat.odd_iff,
    Nat.even_iff, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) <;> omega
  · rintro (h | h | h)
    · exact Or.inl (Or.inl ⟨a / 2, by omega, by omega⟩)
    · exact Or.inl (Or.inr ⟨a / 2 - 1, by omega, by omega⟩)
    · exact Or.inr ⟨a / 4 - 1, by omega, by omega⟩

private def validAt {N : ℕ} (p : Nat.Partition N) (j : ℕ) :=
  (p.parts.count 1 = j ^ 2 ∨ p.parts.count 1 = j ^ 2 + 1) ∧
    (∀ a ∈ p.parts, Odd a → 1 < a → p.parts.count a = 1) ∧
    (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
    ∀ a ∈ p.parts, Even a → 2 * j < a → 4 * j + 4 ≤ a ∧ 4 ∣ a

private def fits {N : ℕ} (p : Nat.Partition N) (M j : ℕ) :=
  ∀ a, (if 1 = a then j ^ 2 else 0) ≤ p.parts.count a ∧
    p.parts.count a ≤ (if 1 = a then j ^ 2 else 0) + (if a ∈ optionalParts M j then 1 else 0)

private theorem one_mem_optionalParts {M j : ℕ} (hM : 0 < M) :
    1 ∈ optionalParts M j :=
  (mem_optionalParts _ _ _).2 (Or.inl ⟨by decide, by omega⟩)

private theorem validAt_iff_fits {N M j : ℕ} (p : Nat.Partition N)
    (hNM : N ≤ M) (hM : 0 < M) : validAt p j ↔ fits p M j := by
  have hOne := one_mem_optionalParts (j := j) hM
  constructor
  · rintro ⟨hcount, hodd, heven, hlarge⟩ a
    by_cases ha1 : a = 1
    · subst a
      simp only [ite_true, hOne]
      omega
    simp only [Ne.symm ha1, ↓reduceIte, zero_le, zero_add, true_and]
    by_cases ha : a ∈ p.parts
    · have hpos := p.parts_pos ha
      have hle := p.le_of_mem_parts ha
      have hmem : a ∈ optionalParts M j := by
        apply (mem_optionalParts _ _ _).2
        rcases Nat.even_or_odd a with he | ho
        · by_cases hsmall : a ≤ 2 * j
          · exact Or.inr (Or.inl ⟨he, hpos, hsmall⟩)
          · obtain ⟨hmin, hdvd⟩ := hlarge a ha he (by omega)
            exact Or.inr (Or.inr ⟨hmin, by omega, hdvd⟩)
        · exact Or.inl ⟨ho, by omega⟩
      simp only [hmem, ↓reduceIte]
      rcases Nat.even_or_odd a with he | ho
      · exact (heven a ha he).le
      · exact (hodd a ha ho (by omega)).le
    · simp [Multiset.count_eq_zero.mpr ha]
  · intro h
    have hcount := h 1
    simp only [ite_true, hOne] at hcount
    have hs (a : ℕ) (ha : a ∈ p.parts) (ha1 : a ≠ 1) :
        p.parts.count a = 1 ∧ a ∈ optionalParts M j := by
      have hc := (h a).2
      have hpos := Multiset.count_pos.mpr ha
      simp only [Ne.symm ha1, ↓reduceIte, zero_add] at hc
      by_cases hmem : a ∈ optionalParts M j
      · simp only [hmem, ↓reduceIte] at hc
        exact ⟨by omega, hmem⟩
      · simp only [hmem, ↓reduceIte] at hc
        omega
    refine ⟨?_, fun a ha _ ha1 => (hs a ha (by omega)).1,
      fun a ha he => (hs a ha (by rintro rfl; exact (by decide : ¬ Even 1) he)).1, ?_⟩
    · by_cases hEq : p.parts.count 1 = j ^ 2
      · exact Or.inl hEq
      · exact Or.inr (by omega)
    intro a ha he hj
    have hmem := (hs a ha (by rintro rfl; exact (by decide : ¬ Even 1) he)).2
    rcases (mem_optionalParts _ _ _).1 hmem with ho | hsmall | hlarge
    · exact False.elim (Nat.not_odd_iff_even.mpr he ho.1)
    · omega
    · exact ⟨hlarge.1, hlarge.2.2⟩

private theorem fits_unique {N M j k : ℕ} {p : Nat.Partition N}
    (hM : 0 < M) (hj : 1 ≤ j) (hk : 1 ≤ k) (hf : fits p M j) (hg : fits p M k) : j = k := by
  have hOne (i : ℕ) := one_mem_optionalParts (j := i) hM
  have hf1 := hf 1
  have hg1 := hg 1
  simp only [ite_true, hOne] at hf1 hg1
  rcases lt_trichotomy j k with h | h | h
  · have hsq := Nat.pow_le_pow_left (by omega : j + 1 ≤ k) 2
    nlinarith
  · exact h
  · have hsq := Nat.pow_le_pow_left (by omega : k + 1 ≤ j) 2
    nlinarith

private def choices (N M : ℕ) :=
  (Icc 1 M).sigma fun j =>
    (optionalParts M j).powerset.filter fun s => j ^ 2 + s.val.sum = N

private theorem mem_choices {N M j : ℕ} {s : Finset ℕ} :
    (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N M ↔
      j ∈ Icc 1 M ∧ s ⊆ optionalParts M j ∧ j ^ 2 + s.val.sum = N := by
  simp [choices]

private theorem count_val (a : ℕ) (s : Finset ℕ) :
    s.val.count a = if a ∈ s then 1 else 0 := by
  split
  · exact Multiset.nodup_iff_count_eq_one.mp s.nodup a ‹_›
  · exact Multiset.count_eq_zero.mpr ‹_›

private def makePartition {N M j : ℕ} {s : Finset ℕ}
    (h : (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N M) : Nat.Partition N where
  parts := Multiset.replicate (j ^ 2) 1 + s.val
  parts_pos := by
    intro a ha
    rcases Multiset.mem_add.mp ha with hb | hs
    · simp [(Multiset.mem_replicate.mp hb).2]
    · have ho := (mem_optionalParts _ _ _).mp ((mem_choices.mp h).2.1 hs)
      simp only [Nat.odd_iff] at ho
      omega
  parts_sum := by simpa [Multiset.sum_add] using (mem_choices.mp h).2.2

private theorem fits_make {N M j : ℕ} {s : Finset ℕ}
    (h : (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N M) : fits (makePartition h) M j := by
  intro a
  simp only [makePartition, Multiset.count_add, Multiset.count_replicate, count_val,
    Nat.le_add_right, true_and, Nat.add_le_add_iff_left]
  have hs := (mem_choices.mp h).2.1
  by_cases ha : a ∈ s
  · simp [ha, hs ha]
  · simp [ha]

private theorem c3_card {N M : ℕ} (hNM : N ≤ M) (hM : 0 < M) :
    initialRepetitionsC3 N = (choices N M).card := by
  classical
  symm
  unfold initialRepetitionsC3
  apply card_bij (fun z hz => makePartition (j := z.1) (s := z.2) hz)
  · rintro ⟨j, s⟩ hz
    have h := (validAt_iff_fits _ hNM hM).mpr (fits_make hz)
    have hb := (mem_choices.mp hz).2.2
    have hj := (mem_Icc.mp (mem_choices.mp hz).1).1
    have hjN : j ≤ N := by
      have hsq := Nat.le_self_pow (by decide : 2 ≠ 0) j
      omega
    exact mem_filter.mpr ⟨mem_univ _, j, mem_Icc.mpr ⟨hj, hjN⟩, h⟩
  · rintro ⟨j, s⟩ h ⟨k, t⟩ h' he
    have hf := fits_make h
    rw [he] at hf
    obtain rfl := fits_unique hM (mem_Icc.mp (mem_choices.mp h).1).1
      (mem_Icc.mp (mem_choices.mp h').1).1 hf (fits_make h')
    have he' := congrArg Nat.Partition.parts he
    change Multiset.replicate (j ^ 2) 1 + s.val = Multiset.replicate (j ^ 2) 1 + t.val at he'
    obtain rfl := Finset.val_inj.mp (add_left_cancel he')
    rfl
  · intro p hp
    obtain ⟨j, hj, (h : validAt p j)⟩ := (mem_filter.mp hp).2
    have hf := (validAt_iff_fits _ hNM hM).mp h
    let s := (optionalParts M j).filter fun a => (if 1 = a then j ^ 2 else 0) < p.parts.count a
    have hs : Multiset.replicate (j ^ 2) 1 + s.val = p.parts := by
      ext a
      have ha := hf a
      simp only [Multiset.count_add, Multiset.count_replicate, count_val, s, mem_filter]
      generalize (if 1 = a then j ^ 2 else 0) = base at ha ⊢
      by_cases ho : a ∈ optionalParts M j
      · simp only [ho, true_and, ↓reduceIte] at ha ⊢
        split <;> omega
      · simp only [ho, false_and, ↓reduceIte] at ha ⊢
        omega
    have hsum := congrArg Multiset.sum hs
    have hjM : j ∈ Icc 1 M := mem_Icc.mpr ⟨(mem_Icc.mp hj).1, (mem_Icc.mp hj).2.trans hNM⟩
    have hc : (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N M :=
      mem_choices.mpr ⟨hjM, filter_subset _ _, by simpa [p.parts_sum] using hsum⟩
    exact ⟨⟨j, s⟩, hc, Nat.Partition.ext hs⟩

private theorem c3_coeff {N M : ℕ} (hNM : N ≤ M) (hM : 0 < M) :
    (initialRepetitionsC3 N : ZMod 2) =
      coeff N (∑ j ∈ Icc 1 M, X ^ (j ^ 2) * ∏ a ∈ optionalParts M j, (1 + X ^ a)) := by
  rw [c3_card hNM hM, choices, card_sigma, Nat.cast_sum, map_sum]
  apply sum_congr rfl
  intro j _
  rw [prod_one_add, mul_sum, map_sum, natCast_card_filter]
  apply sum_congr rfl
  intro s _
  rw [prod_pow_eq_pow_sum, ← pow_add, coeff_X_pow, Finset.sum_val]
  simp [eq_comm]

/-! ## Finite products modulo a power of $X$ -/

private abbrev Series := PowerSeries (ZMod 2)

private abbrev Truncated (N : ℕ) := Series ⧸ Ideal.span {(X : Series) ^ (N + 1)}

private noncomputable def cut (N : ℕ) : Series →+* Truncated N := Ideal.Quotient.mk _

private noncomputable def truncatedX (N : ℕ) : Truncated N := cut N X

private theorem cut_eq_iff {N : ℕ} {f g : Series} :
    cut N f = cut N g ↔ ∀ k ≤ N, coeff k f = coeff k g := by
  rw [cut, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton, X_pow_dvd_iff]
  simp only [Nat.lt_succ_iff, map_sub, sub_eq_zero]

local instance seriesCharTwo : CharP Series 2 := charP_of_injective_ringHom C_injective 2

local instance truncatedCharTwo (N : ℕ) : CharP (Truncated N) 2 := by
  apply CharTwo.of_one_ne_zero_of_two_eq_zero
  · intro h
    have h' : cut N 1 = cut N 0 := by simpa using h
    simpa using cut_eq_iff.mp h' 0 (Nat.zero_le N)
  · have h := congrArg (cut N) (CharP.cast_eq_zero Series 2)
    simp only [map_natCast, map_zero] at h
    simpa only [Nat.cast_two] using h

private theorem truncatedX_pow_eq_zero {N k : ℕ} (hk : N < k) : truncatedX N ^ k = 0 := by
  rw [truncatedX, ← map_pow, cut, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ (by omega)

private theorem truncatedProd_isUnit (N : ℕ) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) : IsUnit (∏ i ∈ s, (1 + truncatedX N ^ f i)) := by
  have h : IsUnit (∏ i ∈ s, (1 + (X : Series) ^ f i)) := by
    apply isUnit_iff_constantCoeff.mpr
    rw [map_prod]
    have hval : (∏ i ∈ s, constantCoeff (1 + (X : Series) ^ f i)) = 1 := by
      apply prod_eq_one
      intro i hi
      simp [Nat.ne_of_gt (hf i hi)]
    rw [hval]
    exact isUnit_one
  simpa [truncatedX] using h.map (cut N)

private theorem prod_optionalParts {R : Type*} [CommRing R] (x : R) (M j : ℕ) :
    ∏ a ∈ optionalParts M j, (1 + x ^ a) =
      (∏ i ∈ range M, (1 + x ^ (2 * i + 1))) *
        (∏ i ∈ range j, (1 + x ^ (2 * (i + 1)))) *
          ∏ i ∈ Ico j M, (1 + x ^ (4 * (i + 1))) := by
  have hdis₁ : Disjoint ((range M).image (fun i => 2 * i + 1))
      ((range j).image (fun i => 2 * (i + 1))) := by
    simp only [disjoint_left, mem_image, mem_range]
    rintro a ⟨i, _, rfl⟩ ⟨k, _, h⟩
    omega
  have hdis₂ : Disjoint ((range M).image (fun i => 2 * i + 1) ∪
      (range j).image (fun i => 2 * (i + 1))) ((Ico j M).image (fun i => 4 * (i + 1))) := by
    simp only [disjoint_left, mem_union, mem_image, mem_range, mem_Ico]
    rintro a (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) ⟨k, hk, h⟩ <;> omega
  rw [optionalParts, prod_union hdis₂, prod_union hdis₁]
  rw [prod_image (fun _ _ _ _ h => by omega), prod_image (fun _ _ _ _ h => by omega),
    prod_image (fun _ _ _ _ h => by omega)]

private theorem factor_sq {R : Type*} [CommRing R] [CharP R 2] (x : R) (k : ℕ) :
    (1 + x ^ k) ^ 2 = 1 + x ^ (2 * k) := by
  rw [CharTwo.add_sq, one_pow, ← pow_mul, Nat.mul_comm]

private theorem qPochFin_even {R : Type*} [CommRing R] [CharP R 2] (x : R) (m : ℕ) :
    qPochFin (x ^ 2) m = ∏ i ∈ range m, (1 + x ^ (2 * (i + 1))) := by
  simp [qPochFin, pow_mul, CharTwo.sub_eq_add]

private theorem oddProduct_gaussBinom {R : Type*} [CommRing R] (x z : R) (m : ℕ) :
    ∏ i ∈ range m, (1 + z * x ^ (2 * i + 1)) =
      ∑ j ∈ range (m + 1), z ^ j * x ^ (j ^ 2) * gaussBinom (x ^ 2) m j := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    have hprod : (∏ i ∈ range m, (1 + z * x ^ (2 * (i + 1) + 1))) =
        ∏ i ∈ range m, (1 + (z * x ^ 2) * x ^ (2 * i + 1)) := by
      apply prod_congr rfl
      intro i _
      rw [mul_assoc, ← pow_add]
      congr 3
      omega
    rw [prod_range_succ', hprod, ih]
    let f (j : ℕ) := (z * x ^ 2) ^ j * x ^ (j ^ 2) * gaussBinom (x ^ 2) m j
    have h₀ : f (m + 1) = 0 := by simp [f, gaussBinom_eq_zero_of_lt]
    have h₁ : f 0 = 1 := by simp [f]
    simp only [Nat.mul_zero, Nat.zero_add, pow_one]
    change (∑ j ∈ range (m + 1), f j) * (1 + z * x) = _
    have hshift : ∑ j ∈ range (m + 1), f j = (∑ j ∈ range (m + 1), f (j + 1)) + 1 := by
      rw [sum_range_succ' (f := f), h₁]
      rw [sum_range_succ (f := fun j => f (j + 1)), h₀, add_zero]
    have hsplit : (∑ j ∈ range (m + 1), f j) * (1 + z * x) =
        (∑ j ∈ range (m + 1), (f (j + 1) + f j * (z * x))) + 1 := by
      rw [mul_add, mul_one, sum_mul, sum_add_distrib]
      conv_lhs => enter [1]; rw [hshift]
      ring
    rw [hsplit]
    conv_rhs => rw [sum_range_succ']
    simp only [zero_pow (by decide : 2 ≠ 0), pow_zero, gaussBinom_zero_right, mul_one]
    congr 1
    apply sum_congr rfl
    intro j _
    have hexp : j ^ 2 + 2 * j + 1 = (j + 1) ^ 2 := by ring
    have hp : x ^ (2 * j) * x ^ (j ^ 2) * x = x ^ ((j + 1) ^ 2) := by
      rw [← pow_add, ← pow_succ, Nat.add_comm (2 * j), hexp]
    simp only [f, mul_pow, gaussBinom_succ_succ, mul_add, ← pow_mul]
    calc
      _ = z ^ (j + 1) * (x ^ ((j + 1) ^ 2) * x ^ (2 * (j + 1))) *
            gaussBinom (x ^ 2) m (j + 1) +
          z ^ (j + 1) * (x ^ (2 * j) * x ^ (j ^ 2) * x) * gaussBinom (x ^ 2) m j := by
        rw [pow_succ z]
        ring
      _ = _ := by rw [hp]; ring

private theorem prod_truncated_stable {N k l d : ℕ} (hk : N ≤ k) (hkl : k ≤ l) (hd : 0 < d) :
    (∏ i ∈ range l, (1 + truncatedX N ^ (d * (i + 1)))) =
      ∏ i ∈ range k, (1 + truncatedX N ^ (d * (i + 1))) := by
  rw [← prod_range_mul_prod_Ico _ hkl]
  suffices (∏ i ∈ Ico k l, (1 + truncatedX N ^ (d * (i + 1)))) = 1 by rw [this, mul_one]
  apply prod_eq_one
  intro i hi
  have h := (mem_Ico.mp hi).1
  rw [truncatedX_pow_eq_zero (by nlinarith), add_zero]

private theorem qPochFin_truncated_isUnit (N m : ℕ) : IsUnit (qPochFin (truncatedX N ^ 2) m) := by
  rw [qPochFin_even]
  exact truncatedProd_isUnit N _ _ (fun i _ => by omega)

private theorem evenTail_eq_gaussBinom {N M j : ℕ} (hj : j ≤ N) (hM : 2 * N ≤ M) :
    (∏ i ∈ Ico j M, (1 + truncatedX N ^ (2 * (i + 1)))) =
      qPochFin (truncatedX N ^ 2) M * gaussBinom (truncatedX N ^ 2) M j := by
  let x := truncatedX N
  have h := gaussBinom_mul_qPochFin_mul_qPochFin (x ^ 2) M j (by omega)
  -- Both products include all factors that contribute through degree N.
  have hstable : qPochFin (x ^ 2) M = qPochFin (x ^ 2) (M - j) := by
    simpa only [qPochFin_even, x] using
      (prod_truncated_stable (N := N) (k := M - j) (l := M) (d := 2)
        (by omega) (by omega) (by decide))
  rw [← hstable] at h
  have hB : gaussBinom (x ^ 2) M j * qPochFin (x ^ 2) j = 1 :=
    (qPochFin_truncated_isUnit N M).mul_right_cancel (by simpa only [one_mul, x] using h)
  apply (qPochFin_truncated_isUnit N j).mul_left_cancel
  calc
    _ = qPochFin (x ^ 2) M := by
      simp only [qPochFin_even]
      exact prod_range_mul_prod_Ico _ (by omega)
    _ = qPochFin (x ^ 2) j * (qPochFin (x ^ 2) M * gaussBinom (x ^ 2) M j) := by
      rw [show qPochFin (x ^ 2) j * (qPochFin (x ^ 2) M * gaussBinom (x ^ 2) M j) =
          (gaussBinom (x ^ 2) M j * qPochFin (x ^ 2) j) * qPochFin (x ^ 2) M by ring,
        hB, one_mul]

private theorem eulerProd_split {R : Type*} [CommRing R] (x : R) (M : ℕ) :
    (∏ i ∈ range (2 * M), (1 + x ^ (i + 1))) =
      (∏ i ∈ range M, (1 + x ^ (2 * i + 1))) *
        ∏ i ∈ range M, (1 + x ^ (2 * (i + 1))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by omega, prod_range_succ, prod_range_succ, ih]
    rw [prod_range_succ, prod_range_succ, show 2 * M + 1 + 1 = 2 * (M + 1) by omega]
    ring

private theorem finiteEuler_cut (N M : ℕ) (hNM : N ≤ M) :
    cut N (∏ i ∈ range M, (1 + (X : Series) ^ (i + 1))) =
      cut N (pentagonalSeries (ZMod 2)) := by
  apply cut_eq_iff.mpr
  intro k hk
  simp_rw [← CharTwo.sub_eq_add]
  obtain ⟨s, hs⟩ :=
    Filter.eventually_atTop.mp (coeff_prod_one_sub_X_pow_eventually_eq (ZMod 2) k)
  have h := hs (range M ∪ s) subset_union_right
  rwa [← union_sdiff_self_eq_union, prod_union disjoint_sdiff,
    coeff_mul_prod_one_sub_of_lt_order k] at h
  intro i hi
  have hb := (mem_sdiff.mp hi).2
  simp only [mem_range, not_lt] at hb
  rw [order_X_pow, Nat.cast_lt]
  omega

private theorem prod_optionalParts_factored {R : Type*} [CommRing R] [CharP R 2]
    (x : R) {M j : ℕ} (hj : j ≤ M)
    (htail : (∏ i ∈ Ico j M, (1 + x ^ (2 * (i + 1)))) =
      qPochFin (x ^ 2) M * gaussBinom (x ^ 2) M j) :
    ∏ a ∈ optionalParts M j, (1 + x ^ a) =
      (∏ i ∈ range M, (1 + x ^ (2 * i + 1))) *
        qPochFin (x ^ 2) M ^ 2 * gaussBinom (x ^ 2) M j := by
  let tail := ∏ i ∈ Ico j M, (1 + x ^ (2 * (i + 1)))
  have hsplit : qPochFin (x ^ 2) j * tail = qPochFin (x ^ 2) M := by
    simp only [qPochFin_even, tail]
    exact prod_range_mul_prod_Ico _ hj
  have hsq : (∏ i ∈ Ico j M, (1 + x ^ (4 * (i + 1)))) = tail ^ 2 := by
    change _ = (∏ i ∈ Ico j M, (1 + x ^ (2 * (i + 1)))) ^ 2
    rw [← prod_pow]
    simp only [factor_sq, ← Nat.mul_assoc]
  rw [prod_optionalParts, ← qPochFin_even, hsq]
  calc
    _ = (∏ i ∈ range M, (1 + x ^ (2 * i + 1))) * (qPochFin (x ^ 2) j * tail) * tail := by
      ring
    _ = _ := by
      rw [hsplit, show tail = _ from htail]
      ring

/-- The finite products agree through degree `N` with the sum of Euler's square and cube. -/
private theorem c3_coeff_euler (N : ℕ) : (initialRepetitionsC3 N : ZMod 2) =
    coeff N (pentagonalSeries (ZMod 2) ^ 2 + pentagonalSeries (ZMod 2) ^ 3) := by
  let M := 2 * (N + 1)
  let x := truncatedX N
  let E := ∏ i ∈ range M, (1 + x ^ (i + 1))
  let O := ∏ i ∈ range M, (1 + x ^ (2 * i + 1))
  have hM : 2 * N ≤ M := by omega
  have hP : qPochFin (x ^ 2) M = E ^ 2 := by
    change qPochFin (x ^ 2) M = (∏ i ∈ range M, (1 + x ^ (i + 1))) ^ 2
    rw [qPochFin_even, ← prod_pow]
    simp only [factor_sq]
  -- Splitting Euler’s product by parity gives O times the square of E.
  have hEO : O * E = 1 := by
    have hu : IsUnit E :=
      truncatedProd_isUnit N _ _ (fun i _ => Nat.succ_pos i)
    apply hu.mul_right_cancel
    calc
      (O * E) * E = O * qPochFin (x ^ 2) M := by rw [hP, sq, mul_assoc]
      _ = ∏ i ∈ range (2 * M), (1 + x ^ (i + 1)) := by rw [qPochFin_even, eulerProd_split]
      _ = 1 * E := by
        simpa only [one_mul, E, x] using
          (prod_truncated_stable (N := N) (k := M) (l := 2 * M) (d := 1)
            (by omega) (by omega) (by decide))
  have hterm (j : ℕ) (hj : j ∈ Icc 1 M) :
      x ^ (j ^ 2) * (∏ a ∈ optionalParts M j, (1 + x ^ a)) =
        (O * E ^ 4) * (x ^ (j ^ 2) * gaussBinom (x ^ 2) M j) := by
    by_cases hjN : j ≤ N
    · have h := prod_optionalParts_factored x (mem_Icc.mp hj).2 (evenTail_eq_gaussBinom hjN hM)
      rw [h, hP, ← pow_mul]
      change x ^ (j ^ 2) * (O * E ^ 4 * gaussBinom (x ^ 2) M j) = _
      ac_rfl
    · have hzero : x ^ (j ^ 2) = 0 := truncatedX_pow_eq_zero
        (lt_of_lt_of_le (by omega) (Nat.le_self_pow (by decide : 2 ≠ 0) j))
      simp only [hzero, zero_mul, mul_zero]
  -- The term at j = 0 has no compulsory ones and contributes 1 to the Gaussian sum.
  have hsum : ∑ j ∈ Icc 1 M, x ^ (j ^ 2) * gaussBinom (x ^ 2) M j = O - 1 := by
    have hO := oddProduct_gaussBinom x 1 M
    simp only [one_mul, one_pow] at hO
    have hr : range (M + 1) = insert 0 (Icc 1 M) := by
      ext j
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hr, sum_insert (by simp)] at hO
    simp only [zero_pow (by decide : 2 ≠ 0), pow_zero, gaussBinom_zero_right, one_mul] at hO
    apply eq_sub_of_add_eq
    rw [add_comm]
    exact hO.symm
  rw [c3_coeff (M := M) (by omega) (by omega)]
  apply cut_eq_iff.mp _ N le_rfl
  simp only [map_sum, map_mul, map_pow, map_prod, map_add, map_one]
  change (∑ j ∈ Icc 1 M, x ^ (j ^ 2) * ∏ a ∈ optionalParts M j, (1 + x ^ a)) =
    cut N (pentagonalSeries (ZMod 2)) ^ 2 + cut N (pentagonalSeries (ZMod 2)) ^ 3
  rw [show cut N (pentagonalSeries (ZMod 2)) = E by
    rw [← finiteEuler_cut N M (by omega)]
    simp [E, x, truncatedX]]
  rw [sum_congr rfl hterm, ← mul_sum, hsum]
  calc
    _ = (O * E) ^ 2 * E ^ 2 - (O * E) * E ^ 3 := by ring
    _ = E ^ 2 + E ^ 3 := by simp [hEO, CharTwo.sub_eq_add]

/-! ## Vanishing coefficients on nonsquare residue classes -/

private theorem coeff_euler_sq_eq_zero {p N : ℕ}
    (h : ¬ IsSquare ((12 * N + 1 : ℕ) : ZMod p)) :
    coeff N (pentagonalSeries (ZMod 2) ^ 2) = 0 := by
  rw [← map_frobenius_expand 2 (by decide), ZMod.frobenius_zmod, PowerSeries.map_id]
  simp only [id_eq]
  by_cases hdiv : 2 ∣ N
  · obtain ⟨m, rfl⟩ := hdiv
    rw [coeff_expand_mul]
    apply coeff_pentagonalSeries_eq_zero
    rintro ⟨k, rfl⟩
    have hsq : 12 * (2 * (pentagonal k : ℤ)) + 1 = (6 * k - 1) ^ 2 := by
      linarith [two_mul_natCast_pentagonal k]
    apply h
    refine ⟨((6 * k - 1 : ℤ) : ZMod p), ?_⟩
    simpa [pow_two] using congrArg (fun a : ℤ => (a : ZMod p)) hsq
  · exact coeff_expand_of_not_dvd 2 (by decide) _ hdiv

private theorem map_pentagonalSeries :
    map (Int.castRingHom (ZMod 2)) (pentagonalSeries ℤ) = pentagonalSeries (ZMod 2) := by
  ext k
  rw [coeff_map]
  by_cases hk : k ∈ Set.range pentagonal
  · obtain ⟨t, rfl⟩ := hk
    simp [coeff_pentagonalSeries_pentagonal]
  · simp [coeff_pentagonalSeries_eq_zero _ hk]

private theorem coeff_euler_cube_eq_zero {p N : ℕ}
    (h : ¬ IsSquare ((8 * N + 1 : ℕ) : ZMod p)) :
    coeff N (pentagonalSeries (ZMod 2) ^ 3) = 0 := by
  rw [← map_pentagonalSeries, ← map_pow, pentagonalSeries_pow_three, coeff_map]
  suffices hzero : coeff N jacobiCubeSeries = 0 by rw [hzero, map_zero]
  apply coeff_jacobiCubeSeries_eq_zero
  rintro t rfl
  have hsq : 8 * (t + 1).choose 2 + 1 = (2 * t + 1) ^ 2 := by
    nlinarith [two_mul_choose_two_succ t]
  apply h
  refine ⟨((2 * t + 1 : ℕ) : ZMod p), ?_⟩
  simpa [pow_two] using congrArg (fun a : ℕ => (a : ZMod p)) hsq

end initialRepetitionsC3_prime_mul_add_even

-- The proof uses the two nonsquare hypotheses for any modulus.
set_option linter.unusedVariables false in
/-- **Parity of $c_3$ on residue classes modulo a prime.** Let $c_3$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. Let $p \ge 5$ be a prime and let $r$ be an
integer with $1 \le r \le p - 1$ such that neither $12r + 1$ nor $8r + 1$ is a square modulo $p$.
Then $c_3(pn + r)$ is even for every integer $n \ge 0$.

Here $x$ is a square modulo $p$ when $x \equiv y^2 \pmod{p}$ for some integer $y$, so multiples
of $p$ count as squares.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 7 (`integers-2025-A32-thm-7`). -/
public theorem initialRepetitionsC3_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h12 : ¬ IsSquare ((12 * r + 1 : ℕ) : ZMod p)) (h8 : ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC3 (p * n + r)) := by
  open initialRepetitionsC3_prime_mul_add_even PowerSeries in
  have hN12 : ¬ IsSquare ((12 * (p * n + r) + 1 : ℕ) : ZMod p) := by simpa using h12
  have hN8 : ¬ IsSquare ((8 * (p * n + r) + 1 : ℕ) : ZMod p) := by simpa using h8
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [c3_coeff_euler, map_add, coeff_euler_sq_eq_zero hN12, coeff_euler_cube_eq_zero hN8, add_zero]

end MetaMathlibExt
