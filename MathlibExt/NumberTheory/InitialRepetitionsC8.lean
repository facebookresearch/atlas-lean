/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujan
import MathlibExt.NumberTheory.DivisorCountParity

/-!
# Parity of partitions with initial repetitions

For a fixed largest odd part `2j - 1`, first remove one copy of each of the odd parts up to
`2j - 1`. The remaining parts form a subset of the optional parts. This gives a finite product
for each coefficient of the generating series of `c₈`, including the all-even case `j = 0`.

Modulo two, the generating series is the first Rogers–Ramanujan series times the square of
the Euler product. The pentagonal number theorem expands one Euler factor. The finite
Rogers–Ramanujan identity expands the remaining product. Completing the squares in the resulting
exponents identifies the coefficient at `N` modulo two with the number of representations
`5x² + 3y² = 8(15N + 1)` with `x ≡ 1 mod 6` and `y ≡ 1 mod 10`. Two involutions give the
parity of this count when `15N + 1` is nonsquare.

The generating function follows D. Nyirenda and B. Mugwangwavari, *Modulo 2 congruences for
partitions with initial repetitions*, proof of Theorem 2.9, <https://arxiv.org/abs/2212.12705>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The partition function $c_8$.** For $n \ge 0$, $c_8(n)$ is the number of partitions of $n$
such that either (a) all parts are even and distinct, or (b) for some positive integer $j$, the
largest odd part is $2j - 1$, every positive odd integer $i \le j$ appears once or twice, every
odd integer $i$ with $j < i \le 2j - 1$ appears exactly once, all even parts are distinct, and
every even part greater than $j$ is at least $2j + 2$.

For $j = 1$ the paper's clauses "the largest odd part $2j - 1$ appears once" and "odd integers
$\le j$ appear once or twice" conflict; the second governs, as in the generating function
$(q^2;q^2)_\infty \sum_n q^{n^2}/(q;q)_n$ the paper uses (the other reading gives $c_8(2) = 1$,
contradicting Theorem 11 of the paper since $31$ is not a square).

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₈`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC8 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    (∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1) ∨
      ∃ j ∈ Finset.Icc 1 n, 2 * j - 1 ∈ p.parts ∧ (∀ a ∈ p.parts, Odd a → a ≤ 2 * j - 1) ∧
        (∀ i ∈ Finset.Icc 1 j, Odd i → p.parts.count i = 1 ∨ p.parts.count i = 2) ∧
        (∀ i ∈ Finset.Ioc j (2 * j - 1), Odd i → p.parts.count i = 1) ∧
        (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, Even a → j < a → 2 * j + 2 ≤ a).card

end

namespace initialRepetitionsC8_prime_mul_add_even

open Finset PowerSeries

/-! ## Counting by the largest odd part -/

/-- The compulsory odd parts for the index `j`. -/
private def mandatoryParts (j : ℕ) := (range j).image (fun i => 2 * i + 1)

/-- Possible additional parts of a partition of `N`, each with multiplicity at most one. -/
private def optionalParts (N j : ℕ) := Icc 1 j ∪ (Ioc j N).image (fun i => 2 * i)

private theorem mem_mandatoryParts (a j : ℕ) : a ∈ mandatoryParts j ↔ Odd a ∧ a < 2 * j := by
  simp only [mandatoryParts, mem_image, mem_range, Nat.odd_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨a / 2, by omega, by omega⟩

private theorem mem_optionalParts (a N j : ℕ) :
    a ∈ optionalParts N j ↔ (0 < a ∧ a ≤ j) ∨ (Even a ∧ 2 * j < a ∧ a ≤ 2 * N) := by
  simp only [optionalParts, mem_union, mem_Icc, mem_image, mem_Ioc, Nat.even_iff]
  constructor
  · rintro (h | ⟨i, h, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨a / 2, by omega⟩

private theorem mandatoryParts_sum (j : ℕ) : (mandatoryParts j).val.sum = j ^ 2 := by
  have inj : Function.Injective (fun i : ℕ => 2 * i + 1) := by
    intro i k h
    dsimp at h
    omega
  rw [Finset.sum_val]
  unfold mandatoryParts
  rw [sum_image inj.injOn]
  simp only [id_eq]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih]
    ring

private def partitionCondition {N : ℕ} (p : Nat.Partition N) :=
  (∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1) ∨
    ∃ j ∈ Icc 1 N, 2 * j - 1 ∈ p.parts ∧ (∀ a ∈ p.parts, Odd a → a ≤ 2 * j - 1) ∧
      (∀ i ∈ Icc 1 j, Odd i → p.parts.count i = 1 ∨ p.parts.count i = 2) ∧
      (∀ i ∈ Ioc j (2 * j - 1), Odd i → p.parts.count i = 1) ∧
      (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
      ∀ a ∈ p.parts, Even a → j < a → 2 * j + 2 ≤ a

/-- Bounds on multiplicities after choosing the largest odd part. -/
private def fits {N : ℕ} (p : Nat.Partition N) (j : ℕ) :=
  ∀ a, (if a ∈ mandatoryParts j then 1 else 0) ≤ p.parts.count a ∧
    p.parts.count a ≤ (if a ∈ mandatoryParts j then 1 else 0) +
      (if a ∈ optionalParts N j then 1 else 0)

private theorem condition_iff {N : ℕ} (p : Nat.Partition N) :
    partitionCondition p ↔ ∃ j ≤ N, fits p j := by
  constructor
  · rintro (h | ⟨j, hj, _, hmax, hlo, hhi, he, hgap⟩)
    · refine ⟨0, Nat.zero_le _, fun a => ?_⟩
      by_cases ha : a ∈ p.parts
      · obtain ⟨he, hc⟩ := h a ha
        have hp := p.parts_pos ha
        have hb := p.le_of_mem_parts ha
        simp [mandatoryParts, mem_optionalParts, hc, he, hp, show a ≤ 2 * N by omega]
      · simp [mandatoryParts, Multiset.count_eq_zero.mpr ha]
    · have hj' := mem_Icc.mp hj
      refine ⟨j, hj'.2, fun a => ?_⟩
      simp only [mem_mandatoryParts, mem_optionalParts]
      by_cases ho : Odd a
      · have hp := Nat.odd_iff.mp ho
        have hne : ¬ Even a := by simp [Nat.even_iff, hp]
        simp only [ho, true_and, hne, false_and, or_false]
        by_cases hl : a ≤ j
        · have hh := hlo a (mem_Icc.mpr ⟨by omega, hl⟩) ho
          simp [show 0 < a by omega, hl, show a < 2 * j by omega]
          omega
        · by_cases hm : a < 2 * j
          · have hh := hhi a (mem_Ioc.mpr (by omega)) ho
            simp [hh, hl, hm]
          · have ha : a ∉ p.parts := by
              intro ha
              have := hmax a ha ho
              omega
            simp [Multiset.count_eq_zero.mpr ha, hm]
      · have hev : Even a := Nat.not_odd_iff_even.mp ho
        simp only [ho, false_and, ↓reduceIte, zero_le, zero_add, true_and, hev]
        by_cases ha : a ∈ p.parts
        · have hp := p.parts_pos ha
          have hb := p.le_of_mem_parts ha
          have hg := hgap a ha hev
          simp [he a ha hev, hp, show a ≤ 2 * N by omega, show a ≤ j ∨ 2 * j < a by omega]
        · simp [Multiset.count_eq_zero.mpr ha]
  · rintro ⟨j, hj, h⟩
    have H (a) := h a
    simp only [mem_mandatoryParts, mem_optionalParts] at H
    by_cases hz : j = 0
    · subst j
      left
      intro a ha
      have hc := Multiset.count_pos.mpr ha
      have hb := H a
      simp at hb
      split at hb <;> grind
    · right
      refine ⟨j, mem_Icc.mpr (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply Multiset.count_pos.mp
        have hb := (H (2 * j - 1)).1
        simp [Nat.odd_iff, show (2 * j - 1) % 2 = 1 by omega, show 2 * j - 1 < 2 * j by omega] at hb
        omega
      · intro a ha ho
        have hc := Multiset.count_pos.mpr ha
        have hb := (H a).2
        have he : ¬ Even a := by simpa using ho
        simp only [ho, true_and, he, false_and, or_false] at hb
        split at hb <;> split at hb <;> omega
      · intro a ha ho
        obtain ⟨ha1, ha2⟩ := mem_Icc.mp ha
        have hb := H a
        simp [ho, show 0 < a by omega, ha2, show a < 2 * j by omega] at hb
        omega
      · intro a ha ho
        obtain ⟨ha1, ha2⟩ := mem_Ioc.mp ha
        have hb := H a
        have he : ¬ Even a := by simpa using ho
        simp [ho, he, show a < 2 * j by omega, show ¬ a ≤ j by omega] at hb
        omega
      · intro a ha he
        have hc := Multiset.count_pos.mpr ha
        have hb := (H a).2
        have ho : ¬ Odd a := by simpa using he
        simp only [ho, false_and, ↓reduceIte, zero_add] at hb
        split at hb <;> omega
      · intro a ha he haj
        have hc := Multiset.count_pos.mpr ha
        have hb := (H a).2
        have ho : ¬ Odd a := by simpa using he
        simp [ho, show ¬ a ≤ j by omega, he] at hb
        have := Nat.even_iff.mp he
        split at hb <;> omega

private theorem fits_unique {N j k : ℕ} {p : Nat.Partition N}
    (hj : fits p j) (hk : fits p k) : j = k := by
  wlog hle : j ≤ k
  · exact (this hk hj (by omega)).symm
  by_contra hn
  have hb := (hk (2 * k - 1)).1
  have hc := (hj (2 * k - 1)).2
  have ho : (2 * k - 1) % 2 = 1 := by omega
  have hpos : 1 ≤ p.parts.count (2 * k - 1) := by
    simpa [mem_mandatoryParts, Nat.odd_iff, ho, show 2 * k - 1 < 2 * k by omega] using hb
  have ha : 2 * k - 1 ∉ p.parts := by
    simpa [mem_mandatoryParts, Nat.odd_iff, ho, show ¬ 2 * k - 1 < 2 * j by omega,
      mem_optionalParts, Nat.even_iff, show ¬ 2 * k - 1 ≤ j by omega] using hc
  exact ha (Multiset.count_pos.mp hpos)

/-- A choice of index and optional parts with total weight `N`. -/
private def choices (N : ℕ) :=
  (range (N + 1)).sigma fun j =>
    (optionalParts N j).powerset.filter fun s => j ^ 2 + s.val.sum = N

private theorem mem_choices {N j : ℕ} {s : Finset ℕ} :
    (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N ↔
      j ≤ N ∧ s ⊆ optionalParts N j ∧ j ^ 2 + s.val.sum = N := by
  simp [choices]

private theorem count_val (a : ℕ) (s : Finset ℕ) :
    s.val.count a = if a ∈ s then 1 else 0 := by
  split
  · exact Multiset.nodup_iff_count_eq_one.mp s.nodup a ‹_›
  · exact Multiset.count_eq_zero.mpr ‹_›

private def makePartition {N j : ℕ} {s : Finset ℕ}
    (h : (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N) : Nat.Partition N where
  parts := (mandatoryParts j).val + s.val
  parts_pos := by
    intro a ha
    rcases Multiset.mem_add.mp ha with hb | hs
    · have ho := Nat.odd_iff.mp ((mem_mandatoryParts _ _).mp hb).1
      omega
    · have ho := (mem_optionalParts _ _ _).mp ((mem_choices.mp h).2.1 hs)
      omega
  parts_sum := by simpa only [Multiset.sum_add, mandatoryParts_sum] using (mem_choices.mp h).2.2

private theorem fits_make {N j : ℕ} {s : Finset ℕ}
    (h : (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N) : fits (makePartition h) j := by
  intro a
  simp only [makePartition, Multiset.count_add, count_val, Nat.le_add_right, true_and,
    Nat.add_le_add_iff_left]
  have hs := (mem_choices.mp h).2.1
  split
  · simp [hs ‹_›]
  · exact Nat.zero_le _

/-- Removing the compulsory odd staircase gives a bijection with finite subset choices. -/
private theorem c8_card (N : ℕ) : initialRepetitionsC8 N = (choices N).card := by
  classical
  symm
  unfold initialRepetitionsC8
  apply card_bij (fun z hz => makePartition (j := z.1) (s := z.2) hz)
  · rintro ⟨j, s⟩ hz
    apply mem_filter.mpr
    exact ⟨mem_univ _, (condition_iff _).mpr ⟨j, (mem_choices.mp hz).1, fits_make hz⟩⟩
  · rintro ⟨j, s⟩ h ⟨k, t⟩ h' he
    have hf := fits_make h
    rw [he] at hf
    obtain rfl := fits_unique hf (fits_make h')
    have he' := congrArg Nat.Partition.parts he
    change (mandatoryParts j).val + s.val = (mandatoryParts j).val + t.val at he'
    have heq := Finset.val_inj.mp (add_left_cancel he')
    subst t
    rfl
  · intro p hp
    obtain ⟨j, hj, h⟩ := (condition_iff _).mp (mem_filter.mp hp).2
    let s := (optionalParts N j).filter fun a => (mandatoryParts j).val.count a < p.parts.count a
    have hs : (mandatoryParts j).val + s.val = p.parts := by
      ext a
      have H := h a
      simp only [Multiset.count_add, count_val, s, mem_filter]
      by_cases hb : a ∈ mandatoryParts j <;> by_cases ho : a ∈ optionalParts N j <;>
        simp only [hb, ho, true_and, false_and, ↓reduceIte] at H ⊢ <;>
        (try split) <;> omega
    have hsum := congrArg Multiset.sum hs
    have hc : (⟨j, s⟩ : Σ _ : ℕ, Finset ℕ) ∈ choices N :=
      mem_choices.mpr ⟨hj, filter_subset _ _, by
        simpa only [Multiset.sum_add, mandatoryParts_sum, p.parts_sum] using hsum⟩
    exact ⟨⟨j, s⟩, hc, Nat.Partition.ext hs⟩

private theorem c8_coeff (N : ℕ) : (initialRepetitionsC8 N : ZMod 2) =
    coeff N (∑ j ∈ range (N + 1), X ^ (j ^ 2) * ∏ a ∈ optionalParts N j, (1 + X ^ a)) := by
  rw [c8_card, choices, card_sigma, Nat.cast_sum, map_sum]
  apply sum_congr rfl
  intro j _
  rw [prod_one_add, mul_sum, map_sum, natCast_card_filter]
  apply sum_congr rfl
  intro s _
  rw [prod_pow_eq_pow_sum, ← pow_add, coeff_X_pow, Finset.sum_val]
  simp [eq_comm]

/-- Over the two-element field, a tail factor `1 + X^(2a)` is the square of `1 - X^a`. -/
private theorem c8_factored (N : ℕ) : (initialRepetitionsC8 N : ZMod 2) =
    coeff N ((∏ i ∈ range N, (1 - X ^ (i + 1))) *
      ∑ j ∈ range (N + 1), X ^ (j ^ 2) * ∏ i ∈ range (N - j), (1 - X ^ (j + i + 1))) := by
  rw [c8_coeff, mul_sum]
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

/-! ## Euler and Rogers–Ramanujan coefficients -/

open MathlibExt MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted in
/-- Clear the finite denominators in the truncated first Rogers–Ramanujan identity. -/
private theorem rogersRamanujan_trunc
    (n : ℕ) :
    (X : PowerSeries ℚ) ^ (n + 1) ∣
      (∑ j ∈ range (n + 1), X ^ (j ^ 2) * ∏ i ∈ range (n - j), (1 - X ^ ((j + i) + 1))) -
      ∑ r ∈ range (n + 1), if r = 0 then 1 else
        (-1) ^ r * (X ^ (5 * r.choose 2 + 2 * r) + X ^ (5 * r.choose 2 + 3 * r)) := by
  convert rrTrunc_RR n using 2
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn := Nat.le_of_lt_succ (mem_range.mp hj)
  have hsplit : qPochFin (X : PowerSeries ℚ) n =
      qPochFin X j * ∏ i ∈ range (n - j), (1 - X ^ (j + i + 1)) := by
    simp only [qPochFin, ← prod_range_add, Nat.add_sub_of_le hjn]
  have hunit : qPochFin (X : PowerSeries ℚ) j * (qPochFin X j)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [qPochFin, map_prod])
  rw [hsplit]
  linear_combination -(X ^ (j ^ 2) * ∏ i ∈ range (n - j), (1 - X ^ (j + i + 1))) * hunit

private def tailSum {R : Type*} [CommRing R] (q : R) (n : ℕ) :=
  ∑ j ∈ range (n + 1), q ^ (j ^ 2) * ∏ i ∈ range (n - j), (1 - q ^ (j + i + 1))

private def thetaSum {R : Type*} [CommRing R] (q : R) (n : ℕ) :=
  ∑ r ∈ range (n + 1), if r = 0 then 1 else
    (-1) ^ r * (q ^ (5 * r.choose 2 + 2 * r) + q ^ (5 * r.choose 2 + 3 * r))

private theorem map_tail {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n : ℕ) : f (tailSum q n) = tailSum (f q) n := by
  simp [tailSum]

private theorem map_theta {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : R) (n : ℕ) : f (thetaSum q n) = thetaSum (f q) n := by
  simp [thetaSum, apply_ite f]

/-- Compare integral coefficients over the rationals, then reduce them modulo two. -/
private theorem coeff_tail_eq_theta {n k : ℕ} (hk : k ≤ n) :
    coeff k (tailSum (X : PowerSeries (ZMod 2)) n) = coeff k (thetaSum X n) := by
  have h := (X_pow_dvd_iff.mp (rogersRamanujan_trunc n)) k (by omega)
  rw [map_sub, sub_eq_zero] at h
  change coeff k (tailSum X n) = coeff k (thetaSum X n) at h
  have hi : coeff k (tailSum (X : PowerSeries ℤ) n) = coeff k (thetaSum X n) := by
    apply Int.cast_injective (α := ℚ)
    change coeff k (map (Int.castRingHom ℚ) (tailSum X n)) =
      coeff k (map (Int.castRingHom ℚ) (thetaSum X n))
    simpa only [map_tail, map_theta, map_X] using! h
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

/-- The exponent `k(5k - 1)/2`, split by sign as in the finite Rogers–Ramanujan sum. -/
private def thetaExponent : ℤ → ℕ
  | .ofNat r => 5 * r.choose 2 + 2 * r
  | .negSucc r => 5 * (r + 1).choose 2 + 3 * (r + 1)

private def indices (N : ℕ) :=
  (range (N + 1)).image Int.ofNat ∪ (range N).image Int.negSucc

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
  have hd : Disjoint ((range (N + 1)).image Int.ofNat) ((range N).image Int.negSucc) := by
    simp [disjoint_left]
  rw [indices, sum_union hd, sum_image Int.ofNat_injective.injOn,
    sum_image (fun _ _ _ _ h => Int.negSucc.inj h)]
  unfold thetaSum
  rw [sum_range_succ', sum_range_succ' (fun r => X ^ thetaExponent (.ofNat r))]
  simp [thetaExponent, CharTwo.neg_eq, sum_add_distrib, add_assoc, add_comm]

private theorem thetaExponent_sq (k : ℤ) :
    40 * (thetaExponent k : ℤ) + 1 = (1 - 10 * k) ^ 2 := by
  have hc (r : ℕ) : 2 * (r.choose 2 : ℤ) = (r : ℤ) * (r - 1) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      push_cast
      linarith
  cases k with
  | ofNat r =>
    simp only [thetaExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.ofNat_eq_natCast]
    linarith [hc r]
  | negSucc r =>
    simp only [thetaExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      Int.negSucc_eq]
    have := hc (r + 1)
    push_cast at *
    linarith

private theorem thetaExponent_injective : Function.Injective thetaExponent := by
  intro a b hab
  have H := thetaExponent_sq a
  rw [hab, thetaExponent_sq b] at H
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp H with h | h <;> omega

private def hasRoot (m c d : ℕ) := ∃ x : ℤ, x % m = 1 ∧ x ^ 2 = c * (d:ℤ) + 1

private theorem theta_root (d : ℕ) : hasRoot 10 40 d ↔ ∃ k, thetaExponent k = d := by
  constructor
  · rintro ⟨x, hx, hs⟩
    let k := (1 - x) / 10
    have hk : 1 - 10 * k = x := by dsimp [k]; norm_num at hx; omega
    have H := thetaExponent_sq k
    rw [hk, hs] at H
    exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨1 - 10 * k, by norm_num, (thetaExponent_sq k).symm⟩

private theorem coeff_theta {n d : ℕ} (hd : d ≤ n) :
    letI := Classical.propDecidable
    coeff d (thetaSum (X : PowerSeries (ZMod 2)) n) = if hasRoot 10 40 d then 1 else 0 := by
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
    coeff d (pentagonalSeries (ZMod 2)) = if hasRoot 6 24 d then 1 else 0 := by
  classical
  have hs (k : ℤ) : 24 * (pentagonal k : ℤ) + 1 = (1 - 6 * k) ^ 2 := by
    linarith [two_mul_natCast_pentagonal k]
  have equiv : hasRoot 6 24 d ↔ d ∈ Set.range pentagonal := by
    constructor
    · rintro ⟨x, hx, he⟩
      let k := (1 - x) / 6
      have hk : 1 - 6 * k = x := by dsimp [k]; norm_num at hx; omega
      have h := hs k
      rw [hk, he] at h
      exact ⟨k, by omega⟩
    · rintro ⟨k, rfl⟩
      exact ⟨1 - 6 * k, by norm_num, (hs _).symm⟩
  split
  · rename_i h
    obtain ⟨k, rfl⟩ := equiv.mp h
    rw [coeff_pentagonalSeries_pentagonal]
    rcases Int.even_or_odd k with he | ho
    · simp [Int.negOnePow_even k he]
    · simp [Int.negOnePow_odd k ho, CharTwo.neg_eq]
  · exact coeff_pentagonalSeries_eq_zero _ (fun h => ‹¬ hasRoot 6 24 d› (equiv.mpr h))

/-! ## Parity of the representation count -/

private def box (N : ℕ) : Finset ℤ :=
  Icc (-(8 * (15 * (N : ℤ) + 1))) (8 * (15 * (N : ℤ) + 1))

private def shell (N : ℕ) : Finset (ℤ × ℤ) :=
  ((box N) ×ˢ (box N)).filter fun (x, y) => 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 1)

private theorem mem_shell (N : ℕ) (x y : ℤ) :
    (x, y) ∈ shell N ↔ 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 1) := by
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
      5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 1) ∧ x % 3 = 1 ∧ x % 4 = y % 4 := by
  simp [lattice, mem_shell]

/-- Put `d = (x - y)/4`. The reflection `(x, y) ↦ (x - 3d, x + d)` negates `d`.
Its fixed points have `x = y` and hence `15N + 1 = x²`. -/
private theorem even_lattice {N : ℕ} (hn : ¬ IsSquare (15 * N + 1)) : Even (lattice N).card := by
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
    have H : (15 * N + 1 : ℕ) = x.natAbs * x.natAbs := by
      have hs : (15 * (N : ℤ) + 1) = x * x := by linarith
      exact_mod_cast (show 15 * (N : ℤ) + 1 = (x.natAbs : ℤ) * x.natAbs by
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

private theorem even_odd_lattice {N : ℕ} (hn : ¬ IsSquare (15 * N + 1)) :
    Even ((lattice N).filter fun z => z.1 % 2 ≠ 0).card := by
  have h := Finset.card_filter_add_card_filter_not (s := lattice N) (p := fun z => z.1 % 2 = 0)
  have he := even_even_lattice N
  have hall := even_lattice hn
  rw [← h, Nat.even_add] at hall
  exact hall.mp he

private def thetaPairs (N : ℕ) :=
  (shell N).filter fun (x, y) => x % 6 = 1 ∧ y % 10 = 1

private theorem mem_thetaPairs (N : ℕ) (x y : ℤ) :
    (x, y) ∈ thetaPairs N ↔
      5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 1) ∧ x % 6 = 1 ∧ y % 10 = 1 := by
  simp [thetaPairs, mem_shell]

private theorem y_mod_five {N : ℕ} {x y : ℤ}
    (h : 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 1)) : y % 5 = 1 ∨ y % 5 = 4 := by
  have he := congrArg (fun t : ℤ => (t : ZMod 5)) h
  push_cast at he
  have test : ∀ a b c : ZMod 5,
      5 * a ^ 2 + 3 * b ^ 2 = 8 * (15 * c + 1) → b = 1 ∨ b = 4 := by decide
  rcases test _ _ _ he with hy | hy
  · exact Or.inl ((ZMod.intCast_eq_intCast_iff y 1 5).mp (by simpa using hy))
  · exact Or.inr ((ZMod.intCast_eq_intCast_iff y 4 5).mp (by simpa using hy))

private theorem odd_mod_four {x : ℤ} (h : x % 2 = 1) : x % 4 = 1 ∨ x % 4 = 3 := by
  have he := Int.emod_emod_of_dvd x (by decide : (2 : ℤ) ∣ 4)
  omega

/-- For odd coordinates, precisely one sign of `y` gives the required residue modulo four. -/
private theorem even_thetaPairs {N : ℕ} (hn : ¬ IsSquare (15 * N + 1)) :
    Even (thetaPairs N).card := by
  rw [show (thetaPairs N).card =
      ((lattice N).filter fun z => z.1 % 2 ≠ 0).card from ?_]
  · exact even_odd_lattice hn
  apply Finset.card_nbij'
    (fun (x, y) => (x, if x % 4 = y % 4 then y else -y))
    (fun (x, y) => (x, if y % 10 = 1 then y else -y))
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
  exact (antidiagonal N).filter fun (a, b) => hasRoot 6 24 a ∧ hasRoot 10 40 b

private theorem mem_degreePairs {N a b : ℕ} :
    (a, b) ∈ degreePairs N ↔ a + b = N ∧ hasRoot 6 24 a ∧ hasRoot 10 40 b := by
  classical
  simp [degreePairs]

private theorem c8_degreePairs (N : ℕ) : (initialRepetitionsC8 N : ZMod 2) =
    ((degreePairs N).card : ZMod 2) := by
  classical
  rw [c8_factored, coeff_mul]
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
  let v (y : ℤ) := thetaExponent ((1 - y) / 10)
  have hu (x : ℤ) (hx : x % 6 = 1) : x ^ 2 = 24 * (u x : ℤ) + 1 := by
    have h := two_mul_natCast_pentagonal ((1 - x) / 6)
    have he : x = 1 - 6 * ((1 - x) / 6) := by omega
    unfold u
    calc
      x ^ 2 = (1 - 6 * ((1 - x) / 6)) ^ 2 := congrArg (·^2) he
      _ = _ := by linarith
  have hv (y : ℤ) (hy : y % 10 = 1) : y ^ 2 = 40 * (v y : ℤ) + 1 := by
    have he : 1 - 10 * ((1 - y) / 10) = y := by omega
    simpa only [v, he] using (thetaExponent_sq ((1 - y) / 10)).symm
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
    have ex : x ^ 2 = x'^2 := by rw [hu x hx, ha, ← hu x' hx']
    have ey : y ^ 2 = y'^2 := by rw [hv y hy, hb, ← hv y' hy']
    apply Prod.ext
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp ex with h | h <;> dsimp <;> omega
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp ey with h | h <;> dsimp <;> omega
  · rintro ⟨a, b⟩ h
    obtain ⟨hab, ⟨x, hx, ex⟩, ⟨y, hy, ey⟩⟩ := mem_degreePairs.mp h
    norm_num at hx hy ex ey
    have hQ : 5 * x ^ 2 + 3 * y ^ 2 = 8 * (15 * (N : ℤ) + 1) := by
      rw [ex, ey, ← hab]
      push_cast
      ring
    refine ⟨⟨x, y⟩, (mem_thetaPairs N x y).mpr ⟨hQ, hx, hy⟩, ?_⟩
    have ha := hu x hx
    have hb := hv y hy
    change (u x, v y) = (a, b)
    congr 1 <;> omega

end initialRepetitionsC8_prime_mul_add_even

open initialRepetitionsC8_prime_mul_add_even in
/-- **$c_8(N)$ is even when $15N + 1$ is not a square.** Let $c_8$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. For every integer $N \ge 0$ such that $15N + 1$
is not a perfect square, $c_8(N)$ is even.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 11 (`integers-2025-A32-thm-11`). -/
public theorem initialRepetitionsC8_even_of_not_isSquare (N : ℕ)
    (hN : ¬ IsSquare (15 * N + 1)) :
    Even (initialRepetitionsC8 N) := by
  obtain ⟨k, hk⟩ := even_thetaPairs hN
  have h := c8_degreePairs N
  rw [← thetaPairs_card, hk, Nat.cast_add, CharTwo.add_self_eq_zero] at h
  exact ZMod.natCast_eq_zero_iff_even.mp h

-- The modular reduction also works without the bounds on the prime and residue.
set_option linter.unusedVariables false in
/-- **Parity of $c_8$ on residue classes modulo a prime.** Let $c_8$ be the initial-repetitions
partition function of Nyirenda and Mugwangwavari. Let $p \ge 7$ be a prime and let $r$ be an
integer with $1 \le r \le p - 1$ such that $15r + 1$ is not a square modulo $p$. Then
$c_8(pn + r)$ is even for every integer $n \ge 0$.

Here $x$ is a square modulo $p$ when $x \equiv y^2 \pmod{p}$ for some integer $y$, so multiples
of $p$ count as squares.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 2 (`integers-2025-A32-cor-2`). -/
public theorem initialRepetitionsC8_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h15 : ¬ IsSquare ((15 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC8 (p * n + r)) := by
  apply initialRepetitionsC8_even_of_not_isSquare
  rintro ⟨x, hx⟩
  apply h15
  refine ⟨(x : ZMod p), ?_⟩
  simpa using congrArg (fun a : ℕ => (a : ZMod p)) hx

end MetaMathlibExt
