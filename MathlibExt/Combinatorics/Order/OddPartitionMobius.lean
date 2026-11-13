/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `d42524e2f9c7007fe8cf94a2d60d2cc9916991d6`, where it was
introduced by fairinternal/formal-math#3813. Original formalization by Adam Kiezun (@akiezun),
with the proof found by a metacode agent (internal agent identity).
-/

module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import MathlibExt.Combinatorics.Finpartition.Card
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open Finset

private theorem IncidenceAlgebra.mu_eq_of_sum_Icc_eq_zero
    {𝕜 : Type*} {α : Type*} [AddCommGroup 𝕜] [One 𝕜]
    [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [WellFoundedLT α]
    (a : α) (g : α → 𝕜) (h1 : g a = 1)
    (h0 : ∀ y : α, a < y → ∑ x ∈ Finset.Icc a y, g x = 0)
    (y : α) (hy : a ≤ y) :
    (IncidenceAlgebra.mu 𝕜 : IncidenceAlgebra 𝕜 α) a y = g y := by
  induction y using WellFoundedLT.induction with
  | ind y ih =>
    rcases eq_or_lt_of_le hy with rfl | hlt
    · rw [IncidenceAlgebra.mu_self]; exact h1.symm
    · have hne : a ≠ y := ne_of_lt hlt
      rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
      have hins : insert y (Finset.Ico a y) = Finset.Icc a y := by
        rw [Finset.Ico_insert_right hy]
      have hnot : y ∉ Finset.Ico a y := Finset.right_notMem_Ico
      have hsum : ∑ x ∈ Finset.Ico a y, g x
          = ∑ x ∈ Finset.Ico a y, (IncidenceAlgebra.mu 𝕜 : IncidenceAlgebra 𝕜 α) a x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_Ico] at hx
        exact (ih x hx.2 hx.1).symm
      have hsplit : ∑ x ∈ Finset.Icc a y, g x
          = g y + ∑ x ∈ Finset.Ico a y, g x := by
        conv_lhs => rw [← hins]
        rw [Finset.sum_insert hnot]
      have hzero : g y + ∑ x ∈ Finset.Ico a y, (IncidenceAlgebra.mu 𝕜 : IncidenceAlgebra 𝕜 α) a x =
          0 := by
        rw [← hsum, ← hsplit]; exact h0 y hlt
      exact (eq_neg_of_add_eq_zero_left hzero).symm

namespace MetaMathlibExt

private def oddPartitionMobiusValue (n : ℕ) : ℤ :=
  if Odd n then (-1 : ℤ) ^ ((n - 1) / 2) * (((Nat.doubleFactorial (n - 2)) : ℤ) ^ 2)
  else (-1 : ℤ) ^ (n / 2) * ((n : ℤ) - 1) * (((Nat.doubleFactorial (n - 3)) : ℤ) ^ 2)

private theorem oddPartitionMobiusValue_two_mul_add_three (i : ℕ) :
    oddPartitionMobiusValue (2 * i + 3) = -((2 * (i : ℤ) + 1) ^ 2) * oddPartitionMobiusValue
        (2 * i + 1) := by
  have hodd1 : Odd (2 * i + 3) := ⟨i + 1, by ring⟩
  have hodd2 : Odd (2 * i + 1) := ⟨i, by ring⟩
  have e1 : (2 * i + 3 - 1) / 2 = i + 1 := by omega
  have e2 : (2 * i + 1 - 1) / 2 = i := by omega
  have d1 : 2 * i + 3 - 2 = 2 * i + 1 := by omega
  have d2 : 2 * i + 1 - 2 = 2 * i - 1 := by omega
  have hdf : Nat.doubleFactorial (2 * i + 1) = (2 * i + 1) * Nat.doubleFactorial (2 * i - 1) := by
    have := Nat.doubleFactorial_add_one (2 * i)
    simpa using this
  unfold oddPartitionMobiusValue
  rw [ite_eq_left hodd1, ite_eq_left hodd2, e1, e2, d1, d2, hdf]
  push_cast
  ring

private theorem oddPartitionMobiusValue_one : oddPartitionMobiusValue 1 = 1 := by
  simp [oddPartitionMobiusValue]

private theorem oddPartitionMobiusValue_odd_eq_choose (i : ℕ) :
    ((oddPartitionMobiusValue (2 * i + 1) : ℤ) : ℚ)
      = ((Nat.factorial (2 * i) : ℕ) : ℚ) * Ring.choose (-1 / 2 : ℚ) i := by
  induction i with
  | zero =>
    simp [oddPartitionMobiusValue_one]
  | succ i ih =>
    have hrec : oddPartitionMobiusValue (2 * (i + 1) + 1)
        = -((2 * (i : ℤ) + 1) ^ 2) * oddPartitionMobiusValue (2 * i + 1) := by
      have h : 2 * (i + 1) + 1 = 2 * i + 3 := by ring
      rw [h]
      have h2 : (2 : ℤ) * (i : ℤ) + 1 = 2 * ((i : ℤ) + 1) + 1 - 2 := by ring
      -- massage to match N8 form with (2*(i:ℤ)+1); N8 at i gives F(2i+3) = -(2i+1)^2 F(2i+1)
      have := oddPartitionMobiusValue_two_mul_add_three i
      -- 2*(i+1)+1 = 2i+3 definitionally up to ring; rewrite
      simpa [show 2 * (i + 1) + 1 = 2 * i + 3 from by ring] using
        (oddPartitionMobiusValue_two_mul_add_three i)
    -- key choose relation
    have hle : i ≤ i + 1 := Nat.le_succ i
    have hcs := Ring.choose_smul_choose (-1 / 2 : ℚ) (n := i + 1) (k := i) hle
    rw [Nat.choose_succ_self_right] at hcs
    simp only [nsmul_eq_mul] at hcs
    have hsub : (i + 1) - i = 1 := by omega
    rw [hsub, Ring.choose_one_right] at hcs
    push_cast at hcs
    -- hcs : (↑(i+1)) * choose (-1/2) (i+1) = choose (-1/2) i * (-1/2 - ↑i)
    have hfact1 : Nat.factorial (2 * (i + 1)) = (2 * i + 2) *
        ((2 * i + 1) * Nat.factorial (2 * i)) := by
      have h1 := Nat.factorial_succ (2 * i + 1)
      have h2 := Nat.factorial_succ (2 * i)
      have heq : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
      rw [heq, h1, h2]
    have hcast : ((oddPartitionMobiusValue (2 * (i + 1) + 1) : ℤ) : ℚ)
        = -((2 * (i : ℚ) + 1) ^ 2) * ((oddPartitionMobiusValue (2 * i + 1) : ℤ) : ℚ) := by
      have := congrArg (fun z : ℤ => ((z : ℤ) : ℚ)) hrec
      simpa [push_cast] using this
      -- need push_cast normalization of (2*(i:ℤ)+1)^2 cast
    rw [hcast, ih]
    -- now goal in terms of factorials and choose; use hfact1 and hcs
    -- hcs has (r - ↑k) with k = i as ℕ cast; simplify (-1/2 - (i:ℚ))
    -- goal: -(2i+1)^2 * (2i)! * c_i = (2(i+1))! * c_{i+1}
    -- from hcs: c_{i+1} = c_i * (-1/2 - i)/(i+1)
    -- reduce to linear combination of hcs and factorial relation; finish by linear_combination
    have hfactQ : ((Nat.factorial (2 * (i + 1)) : ℕ) : ℚ)
        = (2 * (i : ℚ) + 2) * ((2 * (i : ℚ) + 1) * ((Nat.factorial (2 * i) : ℕ) : ℚ)) := by
      have := congrArg (fun n : ℕ => ((n : ℕ) : ℚ)) hfact1
      simpa [Nat.cast_mul, push_cast] using this
    rw [hfactQ]
    linear_combination
      (-(2 * (2 * (i : ℚ) + 1) * ((Nat.factorial (2 * i) : ℕ) : ℚ))) * hcs

private theorem oddPartitionMobiusValue_two_mul_add_two (i : ℕ) :
    oddPartitionMobiusValue (2 * i + 2)
      = -((2 * (i : ℤ) + 1)) * oddPartitionMobiusValue (2 * i + 1) := by
  have heven : Even (2 * i + 2) := ⟨i + 1, by ring⟩
  have hnotodd : ¬ Odd (2 * i + 2) := Nat.not_odd_iff_even.mpr heven
  have hodd : Odd (2 * i + 1) := ⟨i, by ring⟩
  have e1 : (2 * i + 2) / 2 = i + 1 := by omega
  have e2 : (2 * i + 1 - 1) / 2 = i := by omega
  have d1 : 2 * i + 2 - 3 = 2 * i - 1 := by omega
  have d2 : 2 * i + 1 - 2 = 2 * i - 1 := by omega
  unfold oddPartitionMobiusValue
  rw [ite_eq_right hnotodd, ite_eq_left hodd, e1, e2, d1, d2]
  push_cast
  ring

/-- FF(m) = F(m) if m odd, else 0. -/
private def oddPartitionMobiusValueOdd (m : ℕ) : ℤ :=
  if Odd m then oddPartitionMobiusValue m else 0

/-- t(m): 1 if m = 0; 1 if m = 1; 0 if m odd; else -F(m). Conditions tested in order. -/
private def oddPartitionSumValue (m : ℕ) : ℤ :=
  if m = 0 then 1 else if m = 1 then 1 else if Odd m then 0 else -oddPartitionMobiusValue m

private theorem oddPartitionMobiusValueOdd_one : oddPartitionMobiusValueOdd 1 = 1 := by
  simp [oddPartitionMobiusValueOdd, oddPartitionMobiusValue_one]

private theorem oddPartitionMobiusValueOdd_of_even {m : ℕ} (h : Even m) :
    oddPartitionMobiusValueOdd m = 0 := by
  simp [oddPartitionMobiusValueOdd, Nat.not_odd_iff_even.mpr h]

private theorem oddPartitionSumValue_even_eq_choose (l : ℕ) :
    ((oddPartitionSumValue (2 * l) : ℤ) : ℚ)
      = ((Nat.factorial (2 * l) : ℕ) : ℚ) * Ring.choose (1 / 2 : ℚ) l := by
  cases l with
  | zero =>
    simp [oddPartitionSumValue]
  | succ j =>
    have hne0 : 2 * (j + 1) ≠ 0 := by omega
    have hne1 : 2 * (j + 1) ≠ 1 := by omega
    have heven : Even (2 * (j + 1)) := ⟨j + 1, by ring⟩
    have hnotodd : ¬ Odd (2 * (j + 1)) := Nat.not_odd_iff_even.mpr heven
    have ht : oddPartitionSumValue (2 * (j + 1)) = -oddPartitionMobiusValue (2 * (j + 1)) := by
      simp [oddPartitionSumValue, hne0, hne1, hnotodd]
    have h2eq : 2 * (j + 1) = 2 * j + 2 := by ring
    have hrec : oddPartitionMobiusValue (2 * (j + 1))
        = -((2 * (j : ℤ) + 1)) * oddPartitionMobiusValue (2 * j + 1) := by
      rw [h2eq]; exact oddPartitionMobiusValue_two_mul_add_two j
    have hle : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
    have hcs := Ring.choose_smul_choose (1 / 2 : ℚ) (n := j + 1) (k := 1) hle
    rw [Nat.choose_one_right] at hcs
    simp only [nsmul_eq_mul] at hcs
    rw [Ring.choose_one_right] at hcs
    have hsub : (j + 1) - 1 = j := by omega
    rw [hsub] at hcs
    have hhalf : (1 / 2 : ℚ) - ((1 : ℕ) : ℚ) = -1 / 2 := by norm_num
    rw [hhalf] at hcs
    push_cast at hcs
    -- hcs : (↑j + 1) * choose(1/2)(j+1) = 1/2 * choose(-1/2)(j)
    have hfact1 : Nat.factorial (2 * (j + 1)) = (2 * j + 2) *
        ((2 * j + 1) * Nat.factorial (2 * j)) := by
      have h1 := Nat.factorial_succ (2 * j + 1)
      have h2 := Nat.factorial_succ (2 * j)
      have heq : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
      rw [heq, h1, h2]
    have hcastT : ((oddPartitionSumValue (2 * (j + 1)) : ℤ) : ℚ)
        = -((oddPartitionMobiusValue (2 * (j + 1)) : ℤ) : ℚ) := by
      rw [ht, Int.cast_neg]
    have hcastF : ((oddPartitionMobiusValue (2 * (j + 1)) : ℤ) : ℚ)
        = -((2 * (j : ℚ) + 1)) * ((oddPartitionMobiusValue (2 * j + 1) : ℤ) : ℚ) := by
      have := congrArg (fun z : ℤ => ((z : ℤ) : ℚ)) hrec
      simpa [push_cast] using this
    have hN9 := oddPartitionMobiusValue_odd_eq_choose j
    rw [hcastT, hcastF, hN9]
    have hfactQ : ((Nat.factorial (2 * (j + 1)) : ℕ) : ℚ)
        = (2 * (j : ℚ) + 2) * ((2 * (j : ℚ) + 1) * ((Nat.factorial (2 * j) : ℕ) : ℚ)) := by
      have := congrArg (fun n : ℕ => ((n : ℕ) : ℚ)) hfact1
      simpa [Nat.cast_mul, push_cast] using this
    rw [hfactQ]
    linear_combination
      (-(2 * (2 * (j : ℚ) + 1) * ((Nat.factorial (2 * j) : ℕ) : ℚ))) * hcs

private theorem sum_range_choose_mul_oddPartitionSumValue_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (k + 1),
      ((Nat.choose (2 * k) (2 * i) : ℕ) : ℤ) * oddPartitionMobiusValue (2 * i + 1)
        * oddPartitionSumValue (2 * k - 2 * i) = 0 := by
  have hQ : (((∑ i ∈ Finset.range (k + 1),
      ((Nat.choose (2 * k) (2 * i) : ℕ) : ℤ) * oddPartitionMobiusValue (2 * i + 1)
        * oddPartitionSumValue (2 * k - 2 * i)) : ℤ) : ℚ) = 0 := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    -- rewrite each summand
    have hterm : ∀ i ∈ Finset.range (k + 1),
        ((Nat.choose (2 * k) (2 * i) : ℕ) : ℚ) * ((oddPartitionMobiusValue (2 * i + 1) : ℤ) : ℚ)
          * ((oddPartitionSumValue (2 * k - 2 * i) : ℤ) : ℚ)
        = ((Nat.factorial (2 * k) : ℕ) : ℚ)
          * (Ring.choose (-1 / 2 : ℚ) i * Ring.choose (1 / 2 : ℚ) (k - i)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h2i_le : 2 * i ≤ 2 * k := by omega
      have hsub : 2 * k - 2 * i = 2 * (k - i) := by omega
      have hN9 := oddPartitionMobiusValue_odd_eq_choose i
      have hN10 : ((oddPartitionSumValue (2 * (k - i)) : ℤ) : ℚ)
          = ((Nat.factorial (2 * (k - i)) : ℕ) : ℚ) * Ring.choose (1 / 2 : ℚ) (k - i) :=
        oddPartitionSumValue_even_eq_choose (k - i)
      have hcm := Nat.choose_mul_factorial_mul_factorial (n := 2 * k) (k := 2 * i) h2i_le
      -- cast hcm to ℚ and massage (2k - 2i) to 2*(k-i)
      have hcmQ : ((Nat.choose (2 * k) (2 * i) : ℕ) : ℚ) * ((Nat.factorial (2 * i) : ℕ) : ℚ)
          * ((Nat.factorial (2 * (k - i)) : ℕ) : ℚ) = ((Nat.factorial (2 * k) : ℕ) : ℚ) := by
        have := congrArg (fun n : ℕ => ((n : ℕ) : ℚ)) hcm
        simpa [Nat.cast_mul, hsub] using this
      rw [hsub]
      rw [hN9, hN10]
      linear_combination hcmQ * (Ring.choose (-1 / 2 : ℚ) i * Ring.choose (1 / 2 : ℚ) (k - i))
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.mul_sum]
    have hanti : (∑ i ∈ Finset.range (k + 1),
          Ring.choose (-1 / 2 : ℚ) i * Ring.choose (1 / 2 : ℚ) (k - i))
        = ∑ ij ∈ HasAntidiagonal.antidiagonal k,
          Ring.choose (-1 / 2 : ℚ) ij.1 * Ring.choose (1 / 2 : ℚ) ij.2 := by
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Ring.choose (-1 / 2 : ℚ) i * Ring.choose (1 / 2 : ℚ) j) k]
    rw [hanti]
    have hadd := Ring.add_choose_eq (R := ℚ) (r := (-1 / 2 : ℚ)) (s := (1 / 2 : ℚ)) k
        (Commute.all _ _)
    rw [← hadd]
    have hzero : (-1 / 2 : ℚ) + 1 / 2 = 0 := by norm_num
    rw [hzero]
    have hcz := Ring.choose_zero_pos (R := ℚ) (k := k) (by omega : 0 < k)
    rw [hcz]
    exact mul_zero _
  apply Int.cast_injective (α := ℚ) (a₁ := _) (a₂ := (0 : ℤ))
  simpa using hQ

private theorem oddPartitionMobiusValueOdd_of_odd {m : ℕ} (h : Odd m) :
    oddPartitionMobiusValueOdd m = oddPartitionMobiusValue m := by
  simp [oddPartitionMobiusValueOdd, h]

private theorem oddPartitionSumValue_zero : oddPartitionSumValue 0 = 1 := by
  simp [oddPartitionSumValue]

private theorem oddPartitionSumValue_one : oddPartitionSumValue 1 = 1 := by
  simp [oddPartitionSumValue]

private theorem oddPartitionSumValue_of_odd_ge3 {m : ℕ} (hodd : Odd m) (h0 : m ≠ 0) (h1 : m ≠ 1) :
    oddPartitionSumValue m = 0 := by
  simp [oddPartitionSumValue, h0, h1, hodd]

private theorem oddPartitionSumValue_of_even {m : ℕ} (heven : Even m) (h0 : m ≠ 0) (h1 : m ≠ 1) :
    oddPartitionSumValue m = -oddPartitionMobiusValue m := by
  simp [oddPartitionSumValue, h0, h1, Nat.not_odd_iff_even.mpr heven]

private theorem oddPartitionSumValue_succ (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
      ((Nat.choose m j : ℕ) : ℤ) * oddPartitionMobiusValueOdd (j + 1)
        * oddPartitionSumValue (m - j) = oddPartitionSumValue (m + 1) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m even: m = k + k
    cases k with
    | zero =>
      -- m = 0
      have hm : m = 0 := by omega
      subst hm
      simp [oddPartitionMobiusValueOdd_one,
        oddPartitionSumValue_zero, oddPartitionSumValue_one]
    | succ j =>
      -- m = 2 * (j+1), use N11
      have hm2 : m = 2 * (j + 1) := by omega
      subst hm2
      have hk1 : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      have hRHS : oddPartitionSumValue (2 * (j + 1) + 1) = 0 := by
        apply oddPartitionSumValue_of_odd_ge3 _ _ _
        · exact ⟨j + 1, rfl⟩
        · omega
        · omega
      rw [hRHS]
      -- reindex even j' = 2i
      have hsub : Finset.image (fun i => 2 * i) (Finset.range (j + 1 + 1))
          ⊆ Finset.range (2 * (j + 1) + 1) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
        obtain ⟨i, hi, rfl⟩ := hx
        omega
      have hvan : ∀ x ∈ Finset.range (2 * (j + 1) + 1),
          x ∉ Finset.image (fun i => 2 * i) (Finset.range (j + 1 + 1)) →
          ((Nat.choose (2 * (j + 1)) x : ℕ) : ℤ) * oddPartitionMobiusValueOdd (x + 1)
            * oddPartitionSumValue (2 * (j + 1) - x) = 0 := by
        intro x hx hxout
        have hxle : x ≤ 2 * (j + 1) := by
          rw [Finset.mem_range] at hx; omega
        have hodd : Odd x := by
          rcases Nat.even_or_odd x with hev | hod
          · obtain ⟨t, ht⟩ := hev
            exfalso
            apply hxout
            have ht2 : x = 2 * t := by omega
            rw [ht2]
            apply Finset.mem_image.mpr
            refine ⟨t, ?_, rfl⟩
            rw [Finset.mem_range]; omega
          · exact hod
        have hFF : oddPartitionMobiusValueOdd (x + 1) = 0 := by
          apply oddPartitionMobiusValueOdd_of_even
          exact Odd.add_one hodd
        rw [hFF, mul_zero, zero_mul]
      have himg : ∑ x ∈ Finset.image (fun i => 2 * i) (Finset.range (j + 1 + 1)),
            ((Nat.choose (2 * (j + 1)) x : ℕ) : ℤ) * oddPartitionMobiusValueOdd (x + 1)
              * oddPartitionSumValue (2 * (j + 1) - x)
          = ∑ x ∈ Finset.range (2 * (j + 1) + 1),
            ((Nat.choose (2 * (j + 1)) x : ℕ) : ℤ) * oddPartitionMobiusValueOdd (x + 1)
              * oddPartitionSumValue (2 * (j + 1) - x) :=
        Finset.sum_subset hsub hvan
      have hinj : Set.InjOn (fun i => 2 * i)
          (↑(Finset.range (j + 1 + 1)) : Set ℕ) := by
        intro a _ b _ h
        have h2 : 2 * a = 2 * b := h
        omega
      have hstep : ∑ x ∈ Finset.image (fun i => 2 * i) (Finset.range (j + 1 + 1)),
            ((Nat.choose (2 * (j + 1)) x : ℕ) : ℤ) * oddPartitionMobiusValueOdd (x + 1)
              * oddPartitionSumValue (2 * (j + 1) - x)
          = ∑ i ∈ Finset.range (j + 1 + 1),
            ((Nat.choose (2 * (j + 1)) (2 * i) : ℕ) : ℤ)
              * oddPartitionMobiusValue (2 * i + 1)
              * oddPartitionSumValue (2 * (j + 1) - 2 * i) := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro i _
        have hFF : oddPartitionMobiusValueOdd (2 * i + 1) = oddPartitionMobiusValue
            (2 * i + 1) := by
          apply oddPartitionMobiusValueOdd_of_odd
          exact ⟨i, rfl⟩
        rw [hFF]
      rw [← himg, hstep]
      exact sum_range_choose_mul_oddPartitionSumValue_eq_zero (j + 1) hk1
  · -- m odd: m = 2 * k + 1, single term j = 2 * k
    subst hk
    have hmem : 2 * k ∈ Finset.range (2 * k + 1 + 1) := by
      rw [Finset.mem_range]; omega
    have hmain : ((Nat.choose (2 * k + 1) (2 * k) : ℕ) : ℤ)
          * oddPartitionMobiusValueOdd (2 * k + 1) * oddPartitionSumValue (2 * k + 1 - 2 * k)
        = oddPartitionSumValue (2 * k + 1 + 1) := by
      have hC : Nat.choose (2 * k + 1) (2 * k) = 2 * k + 1 := Nat.choose_succ_self_right _
      have hFF : oddPartitionMobiusValueOdd (2 * k + 1) = oddPartitionMobiusValue (2 * k + 1) := by
        apply oddPartitionMobiusValueOdd_of_odd
        exact ⟨k, rfl⟩
      have hsub1 : 2 * k + 1 - 2 * k = 1 := by omega
      have ht1 : oddPartitionSumValue (2 * k + 1 - 2 * k) = 1 := by
        rw [hsub1]; exact oddPartitionSumValue_one
      have htR : oddPartitionSumValue (2 * k + 1 + 1) = -oddPartitionMobiusValue
          (2 * k + 1 + 1) := by
        apply oddPartitionSumValue_of_even _ _ _
        · exact ⟨k + 1, by ring⟩
        · omega
        · omega
      have h2eq : 2 * k + 1 + 1 = 2 * k + 2 := by ring
      have hN8 := oddPartitionMobiusValue_two_mul_add_two k
      rw [hC, hFF, ht1, htR, h2eq, hN8]
      push_cast
      ring
    rw [Finset.sum_eq_single (2 * k)]
    · exact hmain
    · intro j hj hjne
      have hjle : j ≤ 2 * k + 1 := by
        rw [Finset.mem_range] at hj; omega
      rcases Nat.even_or_odd j with hev | hod
      · -- j even, j ≠ 2k: t(2k+1-j) = 0
        obtain ⟨t, ht⟩ := hev
        have hodd : Odd (2 * k + 1 - j) := by
          rw [Nat.odd_iff]
          omega
        have hge : 2 ≤ 2 * k + 1 - j := by omega
        have h0 : 2 * k + 1 - j ≠ 0 := by omega
        have h1 : 2 * k + 1 - j ≠ 1 := by omega
        have ht0 := oddPartitionSumValue_of_odd_ge3 hodd h0 h1
        simp [ht0]
      · -- j odd: FF(j+1) = 0
        have hFF : oddPartitionMobiusValueOdd (j + 1) = 0 := by
          apply oddPartitionMobiusValueOdd_of_even
          exact Odd.add_one hod
        simp [hFF]
    · intro hcon
      exact absurd hmem hcon

end MetaMathlibExt

private theorem Finpartition.exists_two_le_card_of_ne_bot {α : Type*} [DecidableEq α]
    {s : Finset α} (y : Finpartition s) (hy : y ≠ ⊥) :
    ∃ c ∈ y.parts, 2 ≤ #c := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  apply hy
  apply le_antisymm _ (bot_le : (⊥ : Finpartition s) ≤ y)
  intro b hb
  have hcard : #b = 1 := by
    have hpos := (y.nonempty_of_mem_parts hb).card_pos
    have hlt := hcon b hb
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have h1 : a ∈ b := by rw [ha]; exact Finset.mem_singleton_self a
  have has : a ∈ s := y.subset hb h1
  refine ⟨{a}, ?_, ?_⟩
  · rw [Finpartition.mem_bot_iff]
    exact ⟨a, has, rfl⟩
  · rw [ha]

private theorem oddCardProd_bind {α : Type*} [DecidableEq α] {s : Finset α}
    (y : Finpartition s) (Q : ∀ c ∈ y.parts, Finpartition c) (w : ℕ → ℤ) :
    (y.bind Q).cardProd w = ∏ c ∈ y.parts.attach, (Q c.1 c.2).cardProd w := by
  have hdisj : (↑(y.parts.attach) : Set {x // x ∈ y.parts}).PairwiseDisjoint
      (fun i => (Q i.1 i.2).parts) := by
    intro x hx z hz hne
    obtain ⟨b, hb⟩ := x
    obtain ⟨c, hc⟩ := z
    have hbc : b ≠ c := fun h => hne (Subtype.mk_eq_mk.mpr h)
    rw [Function.onFun, Finset.disjoint_left]
    intro d hdb hdc
    have hle1 := (Q b hb).le hdb
    have hle2 := (Q c hc).le hdc
    exact (Q b hb).ne_bot hdb
      (eq_bot_iff.2 ((le_inf hle1 hle2).trans (y.disjoint hb hc hbc).le_bot))
  unfold Finpartition.cardProd
  rw [Finpartition.bind_parts]
  exact Finset.prod_biUnion hdisj

private theorem Finpartition.subset_or_disjoint_of_le {α : Type*} [DecidableEq α] {s : Finset α}
    {x y : Finpartition s} (h : x ≤ y) {b c : Finset α}
    (hb : b ∈ x.parts) (hc : c ∈ y.parts) : b ≤ c ∨ Disjoint b c := by
  obtain ⟨c', hc', hle⟩ := h hb
  rcases eq_or_ne c' c with rfl | hne
  · exact Or.inl hle
  · exact Or.inr ((y.disjoint hc' hc hne).mono hle le_rfl)

private theorem Finpartition.bind_le {α : Type*} [DecidableEq α] {s : Finset α}
    (y : Finpartition s) (Q : ∀ c ∈ y.parts, Finpartition c) : y.bind Q ≤ y := by
  intro d hd
  rw [Finpartition.mem_bind] at hd
  obtain ⟨c, hc, hdc⟩ := hd
  exact ⟨c, hc, (Q c hc).le hdc⟩

private theorem Finpartition.restrict_bind {α : Type*} [DecidableEq α] {s : Finset α}
    (y : Finpartition s) (Q : ∀ c ∈ y.parts, Finpartition c) {c : Finset α}
    (hc : c ∈ y.parts) : (y.bind Q).restrict (y.le hc) = Q c hc := by
  apply Finpartition.ext
  rw [Finpartition.parts_restrict]
  ext d
  simp only [Finset.mem_erase, Finset.mem_image, Ne]
  constructor
  · rintro ⟨hne, e, he, hed⟩
    rw [Finpartition.mem_bind] at he
    obtain ⟨c', hc', hec⟩ := he
    rcases eq_or_ne c c' with rfl | hne2
    · have hle : e ≤ c := (Q c hc').le hec
      have heq : e ⊓ c = e := inf_eq_left.mpr hle
      rw [heq] at hed
      rw [← hed]
      exact hec
    · have hle1 := (Q c' hc').le hec
      have hbot : e ⊓ c = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf hle1 le_rfl).trans (y.disjoint hc' hc hne2.symm).le_bot)
      rw [hbot] at hed
      exact absurd hed.symm hne
  · intro hd
    have hle : d ≤ c := (Q c hc).le hd
    refine ⟨(Q c hc).ne_bot hd, d, ?_, inf_eq_left.mpr hle⟩
    rw [Finpartition.mem_bind]
    exact ⟨c, hc, hd⟩

private theorem Finpartition.bind_restrict_of_le {α : Type*} [DecidableEq α] {s : Finset α}
    {x y : Finpartition s} (h : x ≤ y) :
    y.bind (fun _c hc => x.restrict (y.le hc)) = x := by
  apply Finpartition.ext
  rw [Finpartition.bind_parts]
  ext d
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨c, hc⟩, _, hd⟩
    have hd' : d ∈ (x.restrict (y.le hc)).parts := hd
    rw [Finpartition.parts_restrict] at hd'
    obtain ⟨hne, him⟩ := Finset.mem_erase.mp hd'
    obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp him
    have hbc' : b ⊓ c = d := hbc
    rcases Finpartition.subset_or_disjoint_of_le h hb hc with hle | hdisj
    · have heq : b ⊓ c = b := inf_eq_left.mpr hle
      rw [← hbc', heq]
      exact hb
    · have hbot : b ⊓ c = ⊥ := eq_bot_iff.2 (disjoint_iff_inf_le.mp hdisj)
      rw [hbot] at hbc'
      exact absurd hbc'.symm hne
  · intro hd
    obtain ⟨c, hc, hle⟩ := h hd
    refine ⟨⟨c, hc⟩, Finset.mem_attach _ _, ?_⟩
    change d ∈ (x.restrict (y.le hc)).parts
    rw [Finpartition.parts_restrict, Finset.mem_erase]
    refine ⟨x.ne_bot hd, ?_⟩
    rw [Finset.mem_image]
    exact ⟨d, hd, inf_eq_left.mpr hle⟩

private theorem Finpartition.sum_cardProd_of_le_eq_prod {α : Type*} [DecidableEq α] {s : Finset α}
    (y : Finpartition s) (X : Finset (Finpartition s))
    (hX : ∀ x, x ∈ X ↔ x ≤ y) (w : ℕ → ℤ) :
    ∑ x ∈ X, x.cardProd w
      = ∏ c ∈ y.parts, ∑ z : Finpartition c, z.cardProd w := by
  classical
  let e : {x : Finpartition s // x ≤ y} ≃ ((c : ↥y.parts) → Finpartition (c : Finset α)) :=
    { toFun := fun x c => x.1.restrict (y.le c.2),
      invFun := fun φ => ⟨y.bind (fun c hc => φ ⟨c, hc⟩), y.bind_le _⟩,
      left_inv := fun x => Subtype.ext (Finpartition.bind_restrict_of_le x.2),
      right_inv := fun φ => by
        funext c
        obtain ⟨c, hc⟩ := c
        exact Finpartition.restrict_bind y _ hc }
  have step1 : ∑ x ∈ X, x.cardProd w
      = ∑ a : {x : Finpartition s // x ≤ y}, a.1.cardProd w :=
    Finset.sum_subtype X hX _
  have hmap : ∀ x : {x : Finpartition s // x ≤ y},
      x.1.cardProd w
        = (y.bind (fun c hc => x.1.restrict (y.le hc))).cardProd w := by
    intro x
    rw [Finpartition.bind_restrict_of_le x.2]
  have step2 : (∑ a : {x : Finpartition s // x ≤ y}, a.1.cardProd w)
      = ∑ φ : ((c : ↥y.parts) → Finpartition (c : Finset α)),
        (y.bind (fun c hc => φ ⟨c, hc⟩)).cardProd w :=
    Fintype.sum_equiv e _ _ (fun x => hmap x)
  have step3 : (∑ φ : ((c : ↥y.parts) → Finpartition (c : Finset α)),
        (y.bind (fun c hc => φ ⟨c, hc⟩)).cardProd w)
      = ∑ φ : ((c : ↥y.parts) → Finpartition (c : Finset α)),
        ∏ c : ↥y.parts, (φ c).cardProd w := by
    apply Finset.sum_congr rfl
    intro φ _
    rw [oddCardProd_bind, ← Finset.univ_eq_attach y.parts]
  have step4 : (∑ φ : ((c : ↥y.parts) → Finpartition (c : Finset α)),
        ∏ c : ↥y.parts, (φ c).cardProd w)
      = ∏ c : ↥y.parts, ∑ z : Finpartition (c : Finset α), z.cardProd w :=
    (Fintype.prod_sum (fun (c : ↥y.parts) (z : Finpartition (c : Finset α)) =>
      z.cardProd w)).symm
  have step5 : (∏ c : ↥y.parts, ∑ z : Finpartition (c : Finset α), z.cardProd w)
      = ∏ c ∈ y.parts, ∑ z : Finpartition c, z.cardProd w := by
    have h := Finset.prod_coe_sort y.parts
      (fun b : Finset α => ∑ z : Finpartition b, z.cardProd w)
    simpa using h
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))
private theorem Finpartition.sum_cardProd_part_eq {α : Type*} [DecidableEq α] {s D : Finset α}
    {a : α} (haD : a ∈ D) (hDs : D ⊆ s) (w : ℕ → ℤ) :
    ∑ P ∈ Finset.univ.filter (fun P : Finpartition s => P.part a = D),
      P.cardProd w
      = w (#D) * ∑ Q : Finpartition (s \ D), Q.cardProd w := by
  classical
  have has : a ∈ s := hDs haD
  have hDne : D ≠ (⊥ : Finset α) := by
    have hne0 : D.Nonempty := ⟨a, haD⟩
    have hne : D ≠ ∅ := hne0.ne_empty
    rwa [Finset.bot_eq_empty]
  have hab : Disjoint (s \ D) D := disjoint_sdiff_self_left
  have hc : (s \ D) ⊔ D = s := by
    rw [Finset.sup_eq_union, Finset.sdiff_union_of_subset hDs]
  have hDmem : ∀ P : Finpartition s, P.part a = D → D ∈ P.parts := by
    intro P hP
    rw [← hP]
    exact (Finpartition.part_mem P).mpr has
  have havoid : ∀ P : Finpartition s,
      P.part a = D → (P.avoid D).parts = P.parts.erase D := by
    intro P hP
    have hDm := hDmem P hP
    ext c
    rw [Finpartition.mem_avoid]
    constructor
    · rintro ⟨d, hd, hnd, hdd⟩
      by_cases hdd0 : d = D
      · subst hdd0
        exact absurd le_rfl hnd
      · have hdisj := P.disjoint hd hDm hdd0
        have hdeq : d \ D = d := Finset.sdiff_eq_self_of_disjoint hdisj
        rw [hdeq] at hdd
        rw [← hdd]
        exact Finset.mem_erase.mpr ⟨hdd0, hd⟩
    · intro hc0
      rw [Finset.mem_erase] at hc0
      obtain ⟨hne, hcP⟩ := hc0
      refine ⟨c, hcP, ?_, ?_⟩
      · intro hle
        have hdisj := P.disjoint hcP hDm hne
        have hlebot : c ⊓ D ≤ ⊥ := hdisj.le_bot
        rw [inf_eq_left.mpr hle] at hlebot
        exact (P.ne_bot hcP) (eq_bot_iff.mpr hlebot)
      · have hdisj := P.disjoint hcP hDm hne
        exact Finset.sdiff_eq_self_of_disjoint hdisj
  have hDnotQ : ∀ Q : Finpartition (s \ D), D ∉ Q.parts := by
    intro Q hQ
    have hsub := Q.subset hQ
    have hmem := hsub haD
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 haD
  have hextend : ∀ Q : Finpartition (s \ D), (Q.extend hDne hab hc).part a = D := by
    intro Q
    have hmem : D ∈ (Q.extend hDne hab hc).parts := by
      rw [Finpartition.extend_parts]
      exact Finset.mem_insert_self D _
    exact Finpartition.part_eq_of_mem _ hmem haD
  have hleft : ∀ P : Finpartition s,
      ∀ _ : P ∈ Finset.univ.filter (fun P : Finpartition s => P.part a = D),
      ((P.avoid D).extend hDne hab hc) = P := by
    intro P hP
    rw [Finset.mem_filter] at hP
    apply Finpartition.ext
    rw [Finpartition.extend_parts, havoid P hP.2, Finset.insert_erase (hDmem P hP.2)]
  have hright : ∀ Q : Finpartition (s \ D),
      ∀ _ : Q ∈ (Finset.univ : Finset (Finpartition (s \ D))),
      ((Q.extend hDne hab hc).avoid D) = Q := by
    intro Q _
    apply Finpartition.ext
    rw [havoid _ (hextend Q), Finpartition.extend_parts, Finset.erase_insert (hDnotQ Q)]
  have hweight : ∀ P : Finpartition s, ∀ _ : P.part a = D,
      P.cardProd w = w (#D) * (P.avoid D).cardProd w := by
    intro P hP
    have hDm := hDmem P hP
    have hpartsP : P.parts = insert D (P.avoid D).parts := by
      rw [havoid P hP, Finset.insert_erase hDm]
    have hDnot : D ∉ (P.avoid D).parts := by
      rw [havoid P hP]
      exact Finset.notMem_erase D _
    unfold Finpartition.cardProd
    rw [hpartsP, Finset.prod_insert hDnot]
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun P => P.avoid D) (fun Q => Q.extend hDne hab hc)
  · intro P _
    exact Finset.mem_univ _
  · intro Q _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hextend Q⟩
  · intro P hP
    exact hleft P hP
  · intro Q hQ
    exact hright Q hQ
  · intro P hP
    rw [Finset.mem_filter] at hP
    exact hweight P hP.2
private theorem Finpartition.sum_cardProd_eq_sum_powerset_erase {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (has : a ∈ s) (w : ℕ → ℤ) :
    ∑ P : Finpartition s, P.cardProd w
      = ∑ B ∈ (s.erase a).powerset,
        w (#B + 1) * ∑ Q : Finpartition (s \ insert a B), Q.cardProd w := by
  classical
  have hland : ∀ P : Finpartition s, P ∈ (Finset.univ : Finset (Finpartition s)) →
      (P.part a).erase a ∈ (s.erase a).powerset := by
    intro P _
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_erase] at hx ⊢
    obtain ⟨hne, hmem⟩ := hx
    exact ⟨hne, P.part_subset a hmem⟩
  -- fiber identification
  have hfiber : ∀ B ∈ (s.erase a).powerset,
      Finset.univ.filter (fun P : Finpartition s => (P.part a).erase a = B)
        = Finset.univ.filter (fun P : Finpartition s => P.part a = insert a B) := by
    intro B hB
    apply Finset.filter_congr
    intro P _
    constructor
    · intro hPB
      have hmem : a ∈ P.part a := (Finpartition.mem_part_self P).mpr has
      have hins : insert a ((P.part a).erase a) = P.part a :=
        Finset.insert_erase hmem
      rw [← hins, hPB]
    · intro hPB
      have hsub := Finset.mem_powerset.mp hB
      have haB : a ∉ B := fun ha => Finset.notMem_erase a s (hsub ha)
      rw [hPB, Finset.erase_insert haB]
  have hbase : (∑ P : Finpartition s, P.cardProd w)
      = ∑ B ∈ (s.erase a).powerset,
        ∑ P ∈ Finset.univ.filter (fun P : Finpartition s => (P.part a).erase a = B),
          P.cardProd w := by
    have h := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finpartition s)))
      (t := (s.erase a).powerset) (g := fun P : Finpartition s => (P.part a).erase a)
      (fun P hP => hland P hP) (fun P => P.cardProd w)
    -- h : ∑ j ∈ powerset, ∑ i ∈ univ with g i = j, ... = ∑ i ∈ univ, ...
    rw [← h]
  rw [hbase]
  apply Finset.sum_congr rfl
  intro B hB
  rw [hfiber B hB]
  have hsub : B ⊆ s := Finset.Subset.trans (Finset.mem_powerset.mp hB) (Finset.erase_subset a s)
  have haB : a ∉ B := fun ha => Finset.notMem_erase a s ((Finset.mem_powerset.mp hB) ha)
  have hBs : insert a B ⊆ s := Finset.insert_subset_iff.mpr ⟨has, hsub⟩
  have hN5 := Finpartition.sum_cardProd_part_eq (Finset.mem_insert_self a B) hBs w
  rw [Finset.card_insert_of_notMem haB] at hN5
  exact hN5
namespace MetaMathlibExt

private theorem sum_cardProd_oddPartitionMobiusValueOdd {α : Type*} [DecidableEq α]
    (s : Finset α) :
    ∑ P : Finpartition s, P.cardProd oddPartitionMobiusValueOdd
      = oddPartitionSumValue (#s) := by
  refine Finset.strongInduction
    (p := fun s => ∑ P : Finpartition s, P.cardProd oddPartitionMobiusValueOdd
      = oddPartitionSumValue #s) (fun s ih => ?_) s
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · have hU : Unique (Finpartition (∅ : Finset α)) :=
      @Finpartition.instUniqueBot (Finset α) _ _
    rw [@Fintype.sum_unique _ _ _ _ hU _]
    rw [Finpartition.cardProd_empty, Finset.card_empty, oddPartitionSumValue_zero]
  · obtain ⟨a, has⟩ := hne
    rw [Finpartition.sum_cardProd_eq_sum_powerset_erase has _]
    have hinner : ∀ B ∈ (s.erase a).powerset,
        (∑ Q : Finpartition (s \ insert a B), Q.cardProd oddPartitionMobiusValueOdd)
          = oddPartitionSumValue (#(s \ insert a B)) := by
      intro B hB
      apply ih
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro hcon
      have h1 : a ∈ s \ insert a B := by rw [hcon]; exact has
      rw [Finset.mem_sdiff] at h1
      exact h1.2 (Finset.mem_insert_self a B)
    have hcard : ∀ B ∈ (s.erase a).powerset,
        #(s \ insert a B) = #s - (#B + 1) := by
      intro B hB
      have hBs : insert a B ⊆ s :=
        Finset.insert_subset_iff.mpr
          ⟨has, Finset.Subset.trans (Finset.mem_powerset.mp hB) (Finset.erase_subset a s)⟩
      have haB : a ∉ B := fun ha =>
        Finset.notMem_erase a s ((Finset.mem_powerset.mp hB) ha)
      rw [Finset.card_sdiff_of_subset hBs, Finset.card_insert_of_notMem haB]
    trans ∑ B ∈ (s.erase a).powerset,
      oddPartitionMobiusValueOdd (#B + 1) * oddPartitionSumValue (#s - (#B + 1))
    · apply Finset.sum_congr rfl
      intro B hB
      rw [hinner B hB, hcard B hB]
    · rw [Finset.sum_powerset_apply_card
          (fun C => oddPartitionMobiusValueOdd (C + 1) * oddPartitionSumValue (#s - (C + 1))),
        Finset.card_erase_of_mem has]
      simp only [nsmul_eq_mul]
      have hs1 : 1 ≤ #s := Finset.card_pos.mpr ⟨a, has⟩
      have hN12 := oddPartitionSumValue_succ (#s - 1)
      rw [Nat.sub_add_cancel hs1] at hN12
      rw [Nat.sub_add_cancel hs1, ← hN12]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      have heq : #s - (m + 1) = #s - 1 - m := by omega
      rw [heq, mul_assoc]

end MetaMathlibExt
namespace MetaMathlibExt

/-- The guessed Möbius values: F(n) at ⊤, product of FF over blocks elsewhere. -/
private def oddPartitionGuess (n : ℕ) (P : Finpartition (Finset.univ : Finset (Fin n))) : ℤ :=
  if P = ⊤ then oddPartitionMobiusValue n else P.cardProd oddPartitionMobiusValueOdd

private theorem oddPartition_sum_Icc_guess_eq_zero (n : ℕ) (hn : 0 < n)
    [LocallyFiniteOrder {P : Finpartition (Finset.univ : Finset (Fin n)) //
      P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}]
    (hb : (⊥ : Finpartition (Finset.univ : Finset (Fin n))) = ⊤
      ∨ ∀ b ∈ (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts, Odd b.card)
    (y : {P : Finpartition (Finset.univ : Finset (Fin n)) //
      P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card})
    (hy : (⟨⊥, hb⟩ :
      {P : Finpartition (Finset.univ : Finset (Fin n)) //
        P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) < y) :
    ∑ x ∈ Finset.Icc (⟨⊥, hb⟩ :
      {P : Finpartition (Finset.univ : Finset (Fin n)) //
        P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y,
      oddPartitionGuess n x.val = 0 := by
  classical
  -- Step 1: reindex to X = univ.filter (· ≤ y.val)
  have hIcc : ∀ x :
      {P : Finpartition (Finset.univ : Finset (Fin n)) //
        P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card},
      x ∈ Finset.Icc (⟨⊥, hb⟩ :
        {P : Finpartition (Finset.univ : Finset (Fin n)) //
          P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y ↔ x.val ≤ y.val := by
    intro x
    rw [Finset.mem_Icc]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨(bot_le : (⊥ : Finpartition (Finset.univ : Finset (Fin n))) ≤ x.val), h⟩
  have himg : Finset.image Subtype.val
      (Finset.Icc (⟨⊥, hb⟩ :
        {P : Finpartition (Finset.univ : Finset (Fin n)) //
          P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y)
      ⊆ Finset.univ.filter (fun P => P ≤ y.val) := by
    intro P hP
    rw [Finset.mem_image] at hP
    obtain ⟨x, hx, rfl⟩ := hP
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hIcc x).mp hx⟩
  have hinj : Set.InjOn Subtype.val
      (↑(Finset.Icc (⟨⊥, hb⟩ :
        {P : Finpartition (Finset.univ : Finset (Fin n)) //
          P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y) :
        Set {P : Finpartition (Finset.univ : Finset (Fin n)) //
          P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) :=
    fun a _ b _ h => Subtype.val_injective h
  have h1 : ∑ x ∈ Finset.Icc (⟨⊥, hb⟩ :
      {P : Finpartition (Finset.univ : Finset (Fin n)) //
        P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y, oddPartitionGuess n x.val
      = ∑ P ∈ Finset.image Subtype.val (Finset.Icc (⟨⊥, hb⟩ :
        {P : Finpartition (Finset.univ : Finset (Fin n)) //
          P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y), oddPartitionGuess n P :=
    (Finset.sum_image hinj).symm
  have hvan : ∀ P ∈ Finset.univ.filter
      (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val),
      P ∉ Finset.image Subtype.val (Finset.Icc (⟨⊥, hb⟩ :
        {P : Finpartition (Finset.univ : Finset (Fin n)) //
          P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y) →
      oddPartitionGuess n P = 0 := by
    intro P hPX hPnot
    by_cases hPS : P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card
    · exfalso
      apply hPnot
      apply Finset.mem_image.mpr
      refine ⟨⟨P, hPS⟩, ?_, rfl⟩
      rw [hIcc]
      exact (Finset.mem_filter.mp hPX).2
    · rw [not_or] at hPS
      obtain ⟨hneT, hneO⟩ := hPS
      simp only [not_forall] at hneO
      obtain ⟨b, hbP, hnb⟩ := hneO
      have hbeven : Even b.card := Nat.not_odd_iff_even.mp hnb
      unfold oddPartitionGuess
      rw [ite_eq_right hneT]
      unfold Finpartition.cardProd
      apply Finset.prod_eq_zero hbP
      exact oddPartitionMobiusValueOdd_of_even hbeven
  have hstep1 : ∑ x ∈ Finset.Icc (⟨⊥, hb⟩ :
      {P : Finpartition (Finset.univ : Finset (Fin n)) //
        P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) y, oddPartitionGuess n x.val
      = ∑ P ∈ Finset.univ.filter (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val),
        oddPartitionGuess n P :=
    h1.trans (Finset.sum_subset himg hvan)
  rw [hstep1]
  by_cases hyT : y.val = ⊤
  · -- Step 3: y.val = ⊤
    have hn1 : n ≠ 1 := by
      intro h1
      subst h1
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (Finset.card_fin 1)
      have hbot_top : (⊥ : Finpartition (Finset.univ : Finset (Fin 1))) = ⊤ := by
        apply Finpartition.ext
        have hbot : (⊥ : Finpartition (Finset.univ : Finset (Fin 1))).parts = {{u}} := by
          rw [Finpartition.parts_bot, hu, Finset.map_singleton]
          rfl
        have hune : (Finset.univ : Finset (Fin 1)) ≠ ⊥ := by
          rw [hu, Finset.bot_eq_empty]
          exact Finset.singleton_ne_empty u
        have hsub2 : (⊤ : Finpartition (Finset.univ : Finset (Fin 1))).parts ⊆ {{u}} := by
          have hsub := Finpartition.parts_top_subset (Finset.univ : Finset (Fin 1))
          intro c hc
          have h1 := Finset.mem_singleton.mp (hsub hc)
          rw [Finset.mem_singleton, h1, hu]
        have htop : (⊤ : Finpartition (Finset.univ : Finset (Fin 1))).parts = {{u}} := by
          obtain ⟨b, hbT⟩ := (⊤ : Finpartition (Finset.univ : Finset (Fin 1))).parts_nonempty hune
          have hbeq : b = {u} := Finset.mem_singleton.mp (hsub2 hbT)
          ext c
          simp only [Finset.mem_singleton]
          constructor
          · intro hc
            exact Finset.mem_singleton.mp (hsub2 hc)
          · intro hc
            rw [hc, ← hbeq]
            exact hbT
        rw [hbot, htop]
      have hybot : (⟨⊥, hb⟩ :
          {P : Finpartition (Finset.univ : Finset (Fin 1)) //
            P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) = y :=
        Subtype.ext (hbot_top.trans hyT.symm)
      exact (ne_of_lt hy) hybot
    have hXuniv : Finset.univ.filter
        (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val) = Finset.univ := by
      rw [hyT]
      exact Finset.filter_true_of_mem (fun _ _ => le_top)
    have htop : (⊤ : Finpartition (Finset.univ : Finset (Fin n))) ∈
        (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n)))) :=
      Finset.mem_univ _
    have hsplit := Finset.add_sum_erase (Finset.univ :
      Finset (Finpartition (Finset.univ : Finset (Fin n))))
      (fun P => oddPartitionGuess n P) htop
    have hgT : oddPartitionGuess n (⊤ : Finpartition (Finset.univ : Finset (Fin n)))
        = oddPartitionMobiusValue n := by
      simp [oddPartitionGuess]
    have herase : ∑ P ∈ Finset.univ.erase
        (⊤ : Finpartition (Finset.univ : Finset (Fin n))), oddPartitionGuess n P
        = ∑ P ∈ Finset.univ.erase
          (⊤ : Finpartition (Finset.univ : Finset (Fin n))),
          P.cardProd oddPartitionMobiusValueOdd := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.mem_erase] at hP
      simp [oddPartitionGuess, hP.1]
    have hsplit2 := Finset.add_sum_erase (Finset.univ :
      Finset (Finpartition (Finset.univ : Finset (Fin n))))
      (fun P => P.cardProd oddPartitionMobiusValueOdd) htop
    have htot := sum_cardProd_oddPartitionMobiusValueOdd
      (Finset.univ : Finset (Fin n))
    have hbridge : (∑ P : Finpartition (Finset.univ : Finset (Fin n)),
          P.cardProd oddPartitionMobiusValueOdd)
        = ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n)))),
          P.cardProd oddPartitionMobiusValueOdd := rfl
    have hcard : #(Finset.univ : Finset (Fin n)) = n := Finset.card_fin n
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hneU : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
    have htopC : (⊤ : Finpartition (Finset.univ : Finset (Fin n))).cardProd
        oddPartitionMobiusValueOdd
        = oddPartitionMobiusValueOdd (#(Finset.univ : Finset (Fin n))) :=
      Finpartition.cardProd_top hneU _
    have hTuniv : ∑ P ∈ (Finset.univ :
        Finset (Finpartition (Finset.univ : Finset (Fin n)))),
        P.cardProd oddPartitionMobiusValueOdd = oddPartitionSumValue n := by
      rw [← hbridge, htot, hcard]
    have hC : (⊤ : Finpartition (Finset.univ : Finset (Fin n))).cardProd
        oddPartitionMobiusValueOdd = oddPartitionMobiusValueOdd n := by
      rw [htopC, hcard]
    have hE : ∑ P ∈ Finset.univ.erase
        (⊤ : Finpartition (Finset.univ : Finset (Fin n))),
        P.cardProd oddPartitionMobiusValueOdd
        = oddPartitionSumValue n - oddPartitionMobiusValueOdd n := by
      linear_combination hsplit2 + hTuniv - hC
    have hfin : ∑ P ∈ Finset.univ.filter
        (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val),
        oddPartitionGuess n P
        = oddPartitionMobiusValue n
          + (oddPartitionSumValue n - oddPartitionMobiusValueOdd n) := by
      rw [hXuniv, ← hsplit, hgT, herase, hE]
    rw [hfin]
    rcases Nat.even_or_odd n with hev | hod
    · have ht := oddPartitionSumValue_of_even hev (by omega) hn1
      have hFF := oddPartitionMobiusValueOdd_of_even hev
      rw [ht, hFF]
      ring
    · have ht := oddPartitionSumValue_of_odd_ge3 hod (by omega) hn1
      have hFF := oddPartitionMobiusValueOdd_of_odd hod
      rw [ht, hFF]
      ring
  · -- Step 2: y.val ≠ ⊤
    have hg : ∀ P ∈ Finset.univ.filter
        (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val),
        oddPartitionGuess n P = P.cardProd oddPartitionMobiusValueOdd := by
      intro P hP
      have hle := (Finset.mem_filter.mp hP).2
      have hPT : P ≠ ⊤ := by
        intro hPT
        apply hyT
        rw [hPT] at hle
        exact top_le_iff.mp hle
      simp [oddPartitionGuess, hPT]
    have hN4 := Finpartition.sum_cardProd_of_le_eq_prod y.val
      (Finset.univ.filter (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val))
      (fun x => ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
      oddPartitionMobiusValueOdd
    have hyne : y.val ≠ (⊥ : Finpartition (Finset.univ : Finset (Fin n))) := by
      intro hcon
      have hboty : (⟨⊥, hb⟩ :
          {P : Finpartition (Finset.univ : Finset (Fin n)) //
            P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card}) = y :=
        Subtype.ext hcon.symm
      exact (ne_of_lt hy) hboty
    obtain ⟨c, hcP, h2⟩ := Finpartition.exists_two_le_card_of_ne_bot y.val hyne
    have hodd : Odd (#c) := by
      rcases y.2 with hT | hO
      · exact absurd hT hyT
      · exact hO c hcP
    have h0 : #c ≠ 0 := by
      intro hcon
      rw [hcon] at hodd
      exact Nat.not_odd_zero hodd
    have h1ne : #c ≠ 1 := by
      intro hcon
      omega
    have ht0 : oddPartitionSumValue (#c) = 0 :=
      oddPartitionSumValue_of_odd_ge3 hodd h0 h1ne
    have hT : ∀ cc ∈ y.val.parts,
        (∑ z : Finpartition cc, z.cardProd oddPartitionMobiusValueOdd)
          = oddPartitionSumValue (#cc) :=
      fun cc _ => sum_cardProd_oddPartitionMobiusValueOdd cc
    calc ∑ P ∈ Finset.univ.filter
          (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val),
          oddPartitionGuess n P
        = ∑ P ∈ Finset.univ.filter
          (fun P : Finpartition (Finset.univ : Finset (Fin n)) => P ≤ y.val),
          P.cardProd oddPartitionMobiusValueOdd :=
        Finset.sum_congr rfl (fun P hP => hg P hP)
      _ = ∏ cc ∈ y.val.parts,
          ∑ z : Finpartition cc, z.cardProd oddPartitionMobiusValueOdd := hN4
      _ = ∏ cc ∈ y.val.parts, oddPartitionSumValue (#cc) :=
        Finset.prod_congr rfl (fun cc hcc => hT cc hcc)
      _ = 0 := Finset.prod_eq_zero hcP ht0

end MetaMathlibExt
section
namespace MetaMathlibExt

/-! # Odd partition Möbius number -/

/--
Stanley's odd-partition Möbius number formula: the Möbius number of the poset
of partitions of an `n`-element set using only odd part sizes (plus the
maximum element) equals `(-1)^((n-1)/2) * ((n-2)!!)^2` for odd `n` and
`(-1)^(n/2) * (n-1) * ((n-3)!!)^2` for even `n`. The poset is encoded as a
subtype of `Finpartition`, with `⊥` the discrete partition and `⊤` the
indiscrete one.

Source: Kenneth M. Monks, "An Elementary Proof of the Explicit Formula for
the Möbius Number of the Odd Partition Poset", Journal of Integer Sequences
21 (2018), Article 18.9.6, Theorem [Stanley] (label main), lines 122–131,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Monks/monks12.tex
(first stated as known by Stanley; proved by Sundaram and by Wachs).
-/
theorem oddPartitionPoset_mobiusNumber (n : ℕ) (hn : 0 < n) :
  let S : Type := { P : Finpartition (Finset.univ : Finset (Fin n)) //
    P = ⊤ ∨ ∀ b ∈ P.parts, Odd b.card };
  letI _ : DecidableLE S := Classical.decRel _;
  letI _ : DecidableLT S := Classical.decRel _;
  letI _ : LocallyFiniteOrder S := Fintype.toLocallyFiniteOrder;
  let botOdd : S := ⟨⊥, Or.inr (by simp [Finpartition.parts_bot])⟩;
  let topOdd : S := ⟨⊤, Or.inl rfl⟩;
  ((IncidenceAlgebra.mu ℤ : IncidenceAlgebra ℤ S) botOdd topOdd =
    if Odd n then (-1 : ℤ) ^ ((n - 1) / 2) * (((Nat.doubleFactorial (n - 2)) : ℤ) ^ 2)
    else (-1 : ℤ) ^ (n / 2) * ((n : ℤ) - 1) * (((Nat.doubleFactorial (n - 3)) : ℤ) ^ 2)) := by
  intro S botOdd topOdd
  let : DecidableLE S := Classical.decRel _
  let : DecidableLT S := Classical.decRel _
  let : LocallyFiniteOrder S := Fintype.toLocallyFiniteOrder
  have hg0 : ∀ y : S, botOdd < y →
      ∑ x ∈ Finset.Icc botOdd y, (fun x : S => oddPartitionGuess n x.val) x = 0 := by
    intro y hy
    exact oddPartition_sum_Icc_guess_eq_zero n hn botOdd.2 y hy
  have hPO : Preorder S := inferInstance
  have hW : @WellFoundedLT S (@Preorder.toLT S hPO) :=
    @Finite.to_wellFoundedLT S (Finite.of_fintype S) hPO
  have := hW
  have hle : botOdd ≤ topOdd := Subtype.mk_le_mk.mpr
    (bot_le : (⊥ : Finpartition (Finset.univ : Finset (Fin n)))
      ≤ (⊤ : Finpartition (Finset.univ : Finset (Fin n))))
  have hg1 : (fun x : S => oddPartitionGuess n x.val) botOdd = 1 := by
    change oddPartitionGuess n (⊥ : Finpartition (Finset.univ : Finset (Fin n))) = 1
    by_cases hBT : (⊥ : Finpartition (Finset.univ : Finset (Fin n))) = ⊤
    · have hn1 : n = 1 := by
        have hcb : #((⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts) = n := by
          rw [Finpartition.card_bot, Finset.card_fin]
        have hct : #((⊤ : Finpartition (Finset.univ : Finset (Fin n))).parts) ≤ 1 := by
          classical
          have hsub := Finpartition.parts_top_subset (Finset.univ : Finset (Fin n))
          calc #((⊤ : Finpartition (Finset.univ : Finset (Fin n))).parts)
              ≤ #({(Finset.univ : Finset (Fin n))} : Finset (Finset (Fin n))) :=
                Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton _
        rw [hBT] at hcb
        omega
      subst hn1
      simp [oddPartitionGuess, hBT, oddPartitionMobiusValue_one]
    · simp only [oddPartitionGuess, hBT, ↓reduceIte]
      rw [Finpartition.cardProd_bot, oddPartitionMobiusValueOdd_one, one_pow]
  have hN1 := IncidenceAlgebra.mu_eq_of_sum_Icc_eq_zero (α := S) botOdd
    (fun x => oddPartitionGuess n x.val) hg1 hg0 topOdd hle
  have hbeta : (fun x : S => oddPartitionGuess n x.val) topOdd
      = oddPartitionGuess n topOdd.val := rfl
  have hfinal : oddPartitionGuess n topOdd.val
      = (if Odd n then (-1 : ℤ) ^ ((n - 1) / 2) * (((Nat.doubleFactorial (n - 2)) : ℤ) ^ 2)
        else (-1 : ℤ) ^ (n / 2) * ((n : ℤ) - 1) * (((Nat.doubleFactorial (n - 3)) : ℤ) ^ 2)) := by
    have htop : topOdd.val
        = (⊤ : Finpartition (Finset.univ : Finset (Fin n))) := rfl
    rw [htop]
    simp [oddPartitionGuess, oddPartitionMobiusValue]
  exact hN1.trans (hbeta.trans hfinal)

end MetaMathlibExt
end
