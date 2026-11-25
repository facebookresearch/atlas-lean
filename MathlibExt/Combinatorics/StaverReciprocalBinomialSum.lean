/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

/-- Pointwise splitting identity behind the left-hand recurrence. Writing
`Nat.choose (n + 1)` at `k` and `k + 1` through `Nat.choose_mul_succ_eq` and
`Nat.choose_succ_right_eq` exhibits both children as multiples of
`Nat.choose n k`; since the two cofactors `(n + 1 - k)` and `(k + 1)` add up
to `n + 2`, clearing denominators gives the stated reciprocal identity. -/
private theorem recip_choose_split (n k : ℕ) (hk : k ≤ n) :
    ((Nat.choose n k : Rat))⁻¹
      = (((n : Rat) + 1) / ((n : Rat) + 2))
        * (((Nat.choose (n + 1) k : Rat))⁻¹
            + ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹) := by
  have hE1 : (Nat.choose n k : Rat) * ((n : Rat) + 1)
      = (Nat.choose (n + 1) k : Rat) * ((n + 1 - k : ℕ) : Rat) := by
    have hR := congrArg (Nat.cast : ℕ → Rat) (Nat.choose_mul_succ_eq n k)
    simpa using hR
  have hE2 : (Nat.choose (n + 1) (k + 1) : Rat) * ((k : Rat) + 1)
      = ((n : Rat) + 1) * (Nat.choose n k : Rat) := by
    have h : Nat.choose (n + 1) (k + 1) * (k + 1)
        = (n + 1) * Nat.choose n k :=
      calc Nat.choose (n + 1) (k + 1) * (k + 1)
          = Nat.choose (n + 1) k * (n + 1 - k) :=
            Nat.choose_succ_right_eq (n + 1) k
        _ = Nat.choose n k * (n + 1) := (Nat.choose_mul_succ_eq n k).symm
        _ = (n + 1) * Nat.choose n k := Nat.mul_comm _ _
    have hR := congrArg (Nat.cast : ℕ → Rat) h
    simpa using hR
  have hUV : ((n + 1 - k : ℕ) : Rat) + ((k : Rat) + 1) = (n : Rat) + 2 := by
    have h : (n + 1 - k) + (k + 1) = n + 2 := by omega
    have hR := congrArg (Nat.cast : ℕ → Rat) h
    simpa using hR
  have : (Nat.choose n k : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have : (Nat.choose (n + 1) k : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_succ_of_le hk)).ne'
  have : (Nat.choose (n + 1) (k + 1) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.succ_le_succ hk)).ne'
  have : ((n : Rat) + 2) ≠ 0 := by
    have h : ((n + 2 : ℕ) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  field_simp
  linear_combination (-((Nat.choose (n + 1) (k + 1) : Rat))) * hE1
    + ((Nat.choose (n + 1) k : Rat)) * hE2
    - (((Nat.choose (n + 1) k : Rat))
        * ((Nat.choose (n + 1) (k + 1) : Rat))) * hUV

/-- Left-hand recurrence: summing `recip_choose_split` over `k` expresses the
`n`-sum through two shifted copies of the `(n + 1)`-sum, each equal to that
sum minus its endpoint value `1`, and solving for the `(n + 1)`-sum gives the
recurrence. -/
private theorem lhs_recurrence (n : ℕ) :
    (Finset.range (n + 1 + 1)).sum (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
      = 1 + ((((n : Rat) + 2) / (2 * ((n : Rat) + 1)))
        * ((Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹))) := by
  have hsum : (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹)
      = (((n : Rat) + 1) / ((n : Rat) + 2))
        * ((Finset.range (n + 1)).sum
            (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹
              + ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    exact recip_choose_split n k hkn
  have hfirst : (Finset.range (n + 1)).sum
        (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
      = (Finset.range (n + 1 + 1)).sum
          (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) - 1 := by
    have hsucc : (Finset.range (n + 1 + 1)).sum
          (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
        = (Finset.range (n + 1)).sum (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
          + ((Nat.choose (n + 1) (n + 1) : Rat))⁻¹ :=
      Finset.sum_range_succ (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) (n + 1)
    have hlast : ((Nat.choose (n + 1) (n + 1) : Rat))⁻¹ = 1 := by
      rw [Nat.choose_self]
      simp
    rw [hlast] at hsucc
    linear_combination -1 * hsucc
  have hsecond : (Finset.range (n + 1)).sum
        (fun k => ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)
      = (Finset.range (n + 1 + 1)).sum
          (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) - 1 := by
    have hsucc : (Finset.range (n + 1 + 1)).sum
          (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
        = (Finset.range (n + 1)).sum
            (fun k => ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)
          + ((Nat.choose (n + 1) 0 : Rat))⁻¹ :=
      Finset.sum_range_succ' (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹) (n + 1)
    have hfirst0 : ((Nat.choose (n + 1) 0 : Rat))⁻¹ = 1 := by
      rw [Nat.choose_zero_right]
      simp
    rw [hfirst0] at hsucc
    linear_combination -1 * hsucc
  have hsplit : (Finset.range (n + 1)).sum
        (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹
          + ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹)
      = (Finset.range (n + 1)).sum (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)
        + (Finset.range (n + 1)).sum
          (fun k => ((Nat.choose (n + 1) (k + 1) : Rat))⁻¹) :=
    Finset.sum_add_distrib
  have : ((n : Rat) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : ((n : Rat) + 2) ≠ 0 := by
    have h : ((n + 2 : ℕ) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : (2 : Rat) ≠ 0 := by decide
  have heq : (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹)
      = (((n : Rat) + 1) / ((n : Rat) + 2))
        * (2 * ((Finset.range (n + 1 + 1)).sum
            (fun k => ((Nat.choose (n + 1) k : Rat))⁻¹)) - 2) := by
    rw [hsum, hsplit, hfirst, hsecond]
    ring
  field_simp at heq ⊢
  linear_combination -1 * heq

/-- Right-hand recurrence: peeling the top term off the `Icc` sum writes the
`(n + 1)`-side through the `n`-side, and the new top term cancels the leading
prefactor to leave exactly `1` plus the expected multiple. -/
private theorem rhs_recurrence (n : ℕ) :
    (((n : Rat) + 2) / (2 : Rat) ^ (n + 1 + 1))
        * ((Finset.Icc 1 (n + 1 + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat)))
      = 1 + ((((n : Rat) + 2) / (2 * ((n : Rat) + 1)))
        * ((((n : Rat) + 1) / (2 : Rat) ^ (n + 1))
          * ((Finset.Icc 1 (n + 1)).sum
            (fun k => (2 : Rat) ^ k / (k : Rat))))) := by
  have hU : (Finset.Icc 1 (n + 1 + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat))
      = (Finset.Icc 1 (n + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat))
        + (2 : Rat) ^ (n + 1 + 1) / ((((n + 1 + 1 : ℕ))) : Rat) :=
    Finset.sum_Icc_succ_top (by omega) (fun k => (2 : Rat) ^ k / (k : Rat))
  have hcast : ((((n + 1 + 1 : ℕ))) : Rat) = (n : Rat) + 2 := by
    have h : (n + 1 + 1) = n + 2 := by omega
    have hR := congrArg (Nat.cast : ℕ → Rat) h
    simpa using hR
  have hpow_eq : (2 : Rat) ^ (n + 1 + 1) = 2 * (2 : Rat) ^ (n + 1) := by
    rw [pow_succ]
    ring
  have : ((n : Rat) + 1) ≠ 0 := by
    have h : ((((n + 1 : ℕ))) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : ((n : Rat) + 2) ≠ 0 := by
    have h : ((((n + 2 : ℕ))) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have : (2 : Rat) ≠ 0 := by decide
  have : (2 : Rat) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by decide)
  rw [hU, hcast, hpow_eq]
  field_simp
  ring

/-- **Staver's identity for reciprocal binomial sums.** For every natural number $n$, the
following identity between rational numbers holds:

$$\sum_{k=0}^{n} \binom{n}{k}^{-1} = \frac{n+1}{2^{n+1}} \sum_{k=1}^{n+1} \frac{2^k}{k}.$$

Both sides satisfy the recurrence $F(n+1) = 1 + \frac{n+2}{2(n+1)} F(n)$ and both equal $1$ at
$n = 0$, so the identity follows by induction on $n$.

Source: stable record `jis_grounded_c6a8cb740924fc3bd0e3537c`, concept
`jis_dep_885d07be0a43a0e708255663`.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Sprugnoli/sprugnoli4.tex>.
Source SHA-256: `ae40930a75b3cf8f936a17aa41ee135b01fca41ec402a441f0cf3b0ffdc50111`.
Definition lines 115-125, span SHA
`32e139d381bbe240e14ebcd608096af53038b9b0943d71ed20ce5a97e2cb32ab`.
Formula lines 231-236, span SHA
`b302dbad07d413045e3022c045503c521bbcfeeec710cc24ff4950d9825da66d`.
The left side expands `S_n^(0)`, the sum of reciprocal binomial coefficients.
All arithmetic is rational (`Rat` division and inverses); the statement holds for
all `n : Nat`, so the edge case `n = 0` is included. -/
public theorem staver_reciprocal_binomial_sum (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹) =
      ((n + 1 : Rat) / (2 : Rat) ^ (n + 1)) *
        (Finset.Icc 1 (n + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL := lhs_recurrence n
    have hR := rhs_recurrence n
    simp only [Nat.cast_succ] at ih ⊢
    have h2 : ((n : Rat) + 1) + 1 = (n : Rat) + 2 := by ring
    rw [h2] at ⊢
    rw [hL, hR, ih]

end

end MetaMathlibExt
