/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensions
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Ring

/-!
# Further extensions of Sury's identity

Offset step extension of Sury's identity, Lucas form:
`lucas_step_offset_sury_fib_sum` states that for `|k| < j`,
`F_{j(n+1)}` equals `(F_j/L_k)` times a weighted sum of `L_{ji+k}`.
Binet's formulas give the identities for the induction step.

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity",
*Journal of Integer Sequences* 29 (2026), Article 26.3.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dresden/dresden34.html>),
Theorem 5, formula (54).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

private theorem lucasNumber_pos (n : ℕ) : 0 < MetaMathlibExt.lucasNumber n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    simp only [MetaMathlibExt.lucasNumber]
    omega

private theorem binetA (a k m : ℕ) :
    (MetaMathlibExt.lucasNumber k : ℚ) * (Nat.fib (m + a + k) : ℚ)
      - (-1 : ℚ) ^ k * (MetaMathlibExt.lucasNumber a : ℚ) * (Nat.fib m : ℚ) =
      (Nat.fib (a + k) : ℚ) * (MetaMathlibExt.lucasNumber (m + k) : ℚ) := by
  rify
  simp only [← MetaMathlibExt.cb_lucas_binet, Real.coe_fib_eq,
    ← Real.goldenRatio_mul_goldenConj, pow_add, mul_pow]
  ring

private theorem binetB (b t j : ℕ) :
    (MetaMathlibExt.lucasNumber t : ℚ) * (Nat.fib (b + t + j) : ℚ)
      - (MetaMathlibExt.lucasNumber (j + t) : ℚ) * (Nat.fib (b + t) : ℚ) =
      (-1 : ℚ) ^ t * (Nat.fib j : ℚ) * (MetaMathlibExt.lucasNumber b : ℚ) := by
  rify
  simp only [← MetaMathlibExt.cb_lucas_binet, Real.coe_fib_eq,
    ← Real.goldenRatio_mul_goldenConj, pow_add, mul_pow]
  ring

private theorem neg_one_pow_mul_self (t : ℕ) : (-1 : ℚ) ^ t * (-1 : ℚ) ^ t = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow (Even.add_self t)

private theorem fibAtInt_nat (n : ℕ) : fibAtInt (n : ℤ) = (Nat.fib n : ℚ) := by
  simp only [fibAtInt, Int.fib_natCast, Int.cast_natCast]

private theorem lucasAtInt_nat (n : ℕ) :
    lucasAtInt (n : ℤ) = (MetaMathlibExt.lucasNumber n : ℚ) := by
  unfold lucasAtInt
  simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]

private theorem lucasAtInt_neg (t : ℕ) :
    lucasAtInt (-(t : ℤ)) = (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ) := by
  unfold lucasAtInt
  by_cases h : t = 0
  · subst h
    simp only [Nat.cast_zero, neg_zero, Int.le_refl, ↓reduceIte, Int.toNat_zero, pow_zero, one_mul]
  · have hpos : 0 < (t : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hneg : ¬ (0 : ℤ) ≤ (-(t : ℤ)) := by omega
    simp only [hneg, ↓reduceIte]
    have h1 : (-(-(t : ℤ))).toNat = t := by simp only [neg_neg, Int.toNat_natCast]
    rw [h1]

private theorem neg_one_zpow_neg (t : ℕ) : (-1 : ℚ) ^ (-(t : ℤ)) = (-1 : ℚ) ^ t := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one]

private theorem hr_simp (j t : ℕ) :
    (-1 : ℚ) ^ (-(t : ℤ)) * lucasAtInt ((j : ℤ) - (-(t : ℤ))) / lucasAtInt (-(t : ℤ)) =
      (MetaMathlibExt.lucasNumber (j + t) : ℚ) / (MetaMathlibExt.lucasNumber t : ℚ) := by
  have hLt : (MetaMathlibExt.lucasNumber t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (lucasNumber_pos t))
  have hNeg : (-1 : ℚ) ^ t ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hjt : (j : ℤ) - (-(t : ℤ)) = ((j + t : ℕ) : ℤ) := by
    rw [sub_neg_eq_add, Nat.cast_add]
  rw [neg_one_zpow_neg, hjt, lucasAtInt_nat, lucasAtInt_neg]
  field_simp

private theorem nat_case_pos (j t n : ℕ) (htj : t < j) :
    (Nat.fib (j * (n + 1)) : ℚ) =
      ((Nat.fib j : ℚ) / (MetaMathlibExt.lucasNumber t : ℚ)) *
        ∑ i ∈ Finset.range (n + 1),
          (((-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j - t) : ℚ) /
            (MetaMathlibExt.lucasNumber t : ℚ)) ^ (n - i) *
            (MetaMathlibExt.lucasNumber (j * i + t) : ℚ)) := by
  have hLt : (MetaMathlibExt.lucasNumber t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (lucasNumber_pos t))
  have htj' : t ≤ j := Nat.le_of_lt htj
  have haj : j - t + t = j := Nat.sub_add_cancel htj'
  let r : ℚ := (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j - t) : ℚ) /
    (MetaMathlibExt.lucasNumber t : ℚ)
  let S : ℕ → ℚ := fun k => ∑ i ∈ Finset.range (k + 1),
    (r ^ (k - i) * (MetaMathlibExt.lucasNumber (j * i + t) : ℚ))
  change (Nat.fib (j * (n + 1)) : ℚ) = (Nat.fib j : ℚ) / _ * S n
  induction n with
  | zero => simp [S, hLt]
  | succ n ih =>
    have hSstep : S (n + 1) = r * S n +
        (MetaMathlibExt.lucasNumber (j * (n + 1) + t) : ℚ) := by
      simp only [S]
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ', mul_assoc]
    have hbin := binetA (j - t) t (j * (n + 1))
    rw [haj] at hbin
    have hsum : j * (n + 1) + (j - t) + t = j * (n + 1 + 1) := by
      calc j * (n + 1) + (j - t) + t = j * (n + 1) + (j - t + t) := by
            rw [Nat.add_assoc]
        _ = j * (n + 1) + j := by rw [haj]
        _ = j * (n + 1 + 1) := by ring
    have hbin2 : (MetaMathlibExt.lucasNumber t : ℚ) *
          (Nat.fib (j * (n + 1 + 1)) : ℚ) -
          (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j - t) : ℚ) *
            (Nat.fib (j * (n + 1)) : ℚ) =
          (Nat.fib j : ℚ) *
            (MetaMathlibExt.lucasNumber (j * (n + 1) + t) : ℚ) := by
      rw [← hsum]
      exact hbin
    have ih2 : (MetaMathlibExt.lucasNumber t : ℚ) * (Nat.fib (j * (n + 1)) : ℚ) =
        (Nat.fib j : ℚ) * S n := by
      rw [ih]
      field_simp
    rw [hSstep]
    simp only [r]
    field_simp
    linear_combination (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j - t) : ℚ) * ih2 +
      (MetaMathlibExt.lucasNumber t : ℚ) * hbin2

private theorem case_pos_of_nat (j t n : ℕ) (htj : t < j) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / lucasAtInt (t : ℤ)) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ ((t : ℤ)) * lucasAtInt ((j : ℤ) - (t : ℤ)) / lucasAtInt (t : ℤ)) ^
              (n - i) *
            lucasAtInt ((j : ℤ) * (i : ℤ) + (t : ℤ)) := by
  have htj' : t ≤ j := Nat.le_of_lt htj
  have h1 : (j : ℤ) * ((n : ℤ) + 1) = ((j * (n + 1) : ℕ) : ℤ) := by
    rw [Int.natCast_mul, Nat.cast_add, Nat.cast_one]
  have h2 : (j : ℤ) - (t : ℤ) = ((j - t : ℕ) : ℤ) := by
    rw [Nat.cast_sub htj']
  have h3 : ∀ i : ℕ, (j : ℤ) * (i : ℤ) + (t : ℤ) = ((j * i + t : ℕ) : ℤ) := by
    intro i
    rw [Nat.cast_add, Int.natCast_mul]
  have hz : (-1 : ℚ) ^ ((t : ℤ)) = (-1 : ℚ) ^ t := zpow_natCast _ _
  rw [h1, fibAtInt_nat, fibAtInt_nat, lucasAtInt_nat, hz, h2, lucasAtInt_nat]
  have hsum : (∑ i ∈ Finset.range (n + 1),
      ((-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j - t) : ℚ) /
        (MetaMathlibExt.lucasNumber t : ℚ)) ^ (n - i) *
        lucasAtInt ((j : ℤ) * (i : ℤ) + (t : ℤ))) =
      ∑ i ∈ Finset.range (n + 1),
        (((-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j - t) : ℚ) /
          (MetaMathlibExt.lucasNumber t : ℚ)) ^ (n - i) *
          (MetaMathlibExt.lucasNumber (j * i + t) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h3 i, lucasAtInt_nat]
  rw [hsum]
  exact nat_case_pos j t n htj

private theorem case_neg_of_nat (j t n : ℕ) (htj : t < j) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / lucasAtInt (-(t : ℤ))) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ (-(t : ℤ)) * lucasAtInt ((j : ℤ) - (-(t : ℤ))) / lucasAtInt (-(t : ℤ))) ^
              (n - i) *
            lucasAtInt ((j : ℤ) * (i : ℤ) + (-(t : ℤ))) := by
  have hLt : (MetaMathlibExt.lucasNumber t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (lucasNumber_pos t))
  have hNeg : (-1 : ℚ) ^ t ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hX : (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ) ≠ 0 :=
    mul_ne_zero hNeg hLt
  have hFj : fibAtInt (j : ℤ) = (Nat.fib j : ℚ) := fibAtInt_nat j
  have hLk : lucasAtInt (-(t : ℤ)) = (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ) :=
    lucasAtInt_neg t
  rw [hr_simp, hFj, hLk]
  let r : ℚ := (MetaMathlibExt.lucasNumber (j + t) : ℚ) /
    (MetaMathlibExt.lucasNumber t : ℚ)
  let S : ℕ → ℚ := fun k => ∑ i ∈ Finset.range (k + 1),
    (r ^ (k - i) * lucasAtInt ((j : ℤ) * (i : ℤ) + (-(t : ℤ))))
  change fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) = (Nat.fib j : ℚ) / _ * S n
  induction n with
  | zero =>
    have h0 : (j : ℤ) * (((0 : ℕ) : ℤ) + 1) = (j : ℤ) := by simp
    rw [h0, hFj]
    simp [S, hLk, hX]
  | succ n ih =>
    have hSstep : S (n + 1) = r * S n +
        lucasAtInt ((j : ℤ) * (((n + 1 : ℕ) : ℤ)) + (-(t : ℤ))) := by
      simp only [S]
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ', mul_assoc]
    have hpos : 0 < n + 1 := Nat.succ_pos n
    have hle : t ≤ j * (n + 1) :=
      le_of_lt (lt_of_lt_of_le htj (Nat.le_mul_of_pos_right j hpos))
    have hsub : j * (n + 1) - t + t = j * (n + 1) := Nat.sub_add_cancel hle
    have hNewEq : (j : ℤ) * (((n + 1 : ℕ) : ℤ)) + (-(t : ℤ)) =
        ((j * (n + 1) - t : ℕ) : ℤ) := by
      have hcast : ((j * (n + 1) : ℕ) : ℤ) = (j : ℤ) * (((n + 1 : ℕ) : ℤ)) := by
        rw [Int.natCast_mul]
      have hsub2 : ((j * (n + 1) - t : ℕ) : ℤ) =
          ((j * (n + 1) : ℕ) : ℤ) - (t : ℤ) := Nat.cast_sub hle
      rw [hsub2, hcast]
      ring
    have hNew : lucasAtInt ((j : ℤ) * (((n + 1 : ℕ) : ℤ)) + (-(t : ℤ))) =
        (MetaMathlibExt.lucasNumber (j * (n + 1) - t) : ℚ) := by
      rw [hNewEq, lucasAtInt_nat]
    have hFib_n : fibAtInt ((j : ℤ) * (((n : ℕ) : ℤ) + 1)) =
        (Nat.fib (j * (n + 1)) : ℚ) := by
      have hcast : (j : ℤ) * (((n : ℕ) : ℤ) + 1) = ((j * (n + 1) : ℕ) : ℤ) := by
        rw [Int.natCast_mul, Nat.cast_add, Nat.cast_one]
      rw [hcast, fibAtInt_nat]
    have hFib_succ : fibAtInt ((j : ℤ) * ((((n + 1 : ℕ) : ℤ)) + 1)) =
        (Nat.fib (j * (n + 1 + 1)) : ℚ) := by
      have hcast : (j : ℤ) * ((((n + 1 : ℕ) : ℤ)) + 1) =
          ((j * (n + 1 + 1) : ℕ) : ℤ) := by
        simp [Nat.cast_add, Nat.cast_one]
      rw [hcast, fibAtInt_nat]
    have hB := binetB (j * (n + 1) - t) t j
    have hbt : j * (n + 1) - t + t = j * (n + 1) := hsub
    have hbtj : j * (n + 1) - t + t + j = j * (n + 1 + 1) := by
      calc j * (n + 1) - t + t + j = j * (n + 1) + j := by rw [hsub]
        _ = j * (n + 1 + 1) := by ring
    have hsq := neg_one_pow_mul_self t
    have hNat : (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ) *
          (Nat.fib (j * (n + 1 + 1)) : ℚ) -
          (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j + t) : ℚ) *
            (Nat.fib (j * (n + 1)) : ℚ) =
          (Nat.fib j : ℚ) *
            (MetaMathlibExt.lucasNumber (j * (n + 1) - t) : ℚ) := by
      have hB2 : (MetaMathlibExt.lucasNumber t : ℚ) *
            (Nat.fib (j * (n + 1 + 1)) : ℚ) -
            (MetaMathlibExt.lucasNumber (j + t) : ℚ) *
              (Nat.fib (j * (n + 1)) : ℚ) =
            (-1 : ℚ) ^ t * (Nat.fib j : ℚ) *
              (MetaMathlibExt.lucasNumber (j * (n + 1) - t) : ℚ) := by
        rw [hbtj, hbt] at hB
        exact hB
      linear_combination (-1 : ℚ) ^ t * hB2 +
        (Nat.fib j : ℚ) * (MetaMathlibExt.lucasNumber (j * (n + 1) - t) : ℚ) * hsq
    have hbin2 : (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ) *
          (Nat.fib (j * (n + 1 + 1)) : ℚ) -
          (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber (j + t) : ℚ) *
            (Nat.fib (j * (n + 1)) : ℚ) =
          (Nat.fib j : ℚ) *
            lucasAtInt ((j : ℤ) * (((n + 1 : ℕ) : ℤ)) + (-(t : ℤ))) := by
      rw [hNew]
      exact hNat
    have ih_nat : (Nat.fib (j * (n + 1)) : ℚ) =
        (Nat.fib j : ℚ) / ((-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ)) * S n := by
      rw [← hFib_n]
      exact ih
    have ih2 : (-1 : ℚ) ^ t * (MetaMathlibExt.lucasNumber t : ℚ) *
          (Nat.fib (j * (n + 1)) : ℚ) =
          (Nat.fib j : ℚ) * S n := by
      rw [ih_nat]
      field_simp
    rw [hFib_succ, hSstep]
    simp only [r]
    field_simp
    linear_combination (MetaMathlibExt.lucasNumber (j + t) : ℚ) * ih2 +
      (MetaMathlibExt.lucasNumber t : ℚ) * hbin2

/-- **Offset step extension of Sury's identity, Lucas form.** Let $F_n$ and $L_n$ be the
Fibonacci and Lucas numbers at integer indices. For all natural numbers $j$ and $n$ and every
integer $k$ with $|k| < j$,
$$F_{j(n+1)} = \frac{F_j}{L_k} \sum_{i=0}^{n}
\left(\frac{(-1)^k L_{j-k}}{L_k}\right)^{n-i} L_{ji+k}.$$

Source: Gregory Dresden and Xiaoya Gao, "Further Extensions of Sury's Identity", Theorem 5, formula
(54). -/
public theorem lucas_step_offset_sury_fib_sum
    (j : ℕ) (k : ℤ) (n : ℕ)
    (hjk : |k| < (j : ℤ)) :
    fibAtInt ((j : ℤ) * ((n : ℤ) + 1)) =
      (fibAtInt (j : ℤ) / lucasAtInt k) *
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℚ) ^ k * lucasAtInt ((j : ℤ) - k) / lucasAtInt k) ^
              (n - i) *
            lucasAtInt ((j : ℤ) * (i : ℤ) + k) := by
  by_cases h : 0 ≤ k
  · set t := k.toNat with ht
    have hk : k = (t : ℤ) := (Int.toNat_of_nonneg h).symm
    have habs : |k| = k := abs_of_nonneg h
    have hlt : (t : ℤ) < (j : ℤ) := by
      rw [← hk, ← habs]
      exact hjk
    have htj : t < j := Nat.cast_lt.mp hlt
    rw [hk]
    exact case_pos_of_nat j t n htj
  · have hlt : k < 0 := lt_of_not_ge h
    have hneg : 0 ≤ -k := le_of_lt (neg_pos.mpr hlt)
    set t := (-k).toNat with ht
    have htk : (t : ℤ) = -k := Int.toNat_of_nonneg hneg
    have hk : k = -(t : ℤ) := by
      have h1 : -((t : ℤ)) = k := by
        rw [htk, neg_neg]
      exact h1.symm
    have habs : |k| = -k := abs_of_neg hlt
    have hlt2 : (t : ℤ) < (j : ℤ) := by
      rw [htk, ← habs]
      exact hjk
    have htj : t < j := Nat.cast_lt.mp hlt2
    rw [hk]
    exact case_neg_of_nat j t n htj

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
