/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.CentralTrinomialRecurrence

@[expose] public section

/-!
# Central trinomial coefficients and Legendre polynomials

This file proves that each central trinomial coefficient is a special value of a Legendre
polynomial.
-/

section
namespace MetaMathlibExt

/-- Evaluation point for the Legendre side: `(1 + i/√3)/2`. -/
private noncomputable def legPt : ℂ := (1 + Complex.I / (Real.sqrt 3 : ℂ)) / 2

/-- The shifted Legendre value at `legPt`. -/
private noncomputable def legVal (n : ℕ) : ℂ :=
  Polynomial.aeval legPt (Polynomial.shiftedLegendre n)

/-- The Legendre side of the identity as a sequence. -/
private noncomputable def legSeq (n : ℕ) : ℂ :=
  Complex.I ^ n * (Real.sqrt ((3 : ℝ) ^ n) : ℂ) * legVal n

/-- The central trinomial coefficient as a complex sequence. -/
private noncomputable def triSeq (n : ℕ) : ℂ :=
  (trinomialCoefficient n n : ℂ)

private lemma sqrt3_ne_zero : (Real.sqrt 3 : ℂ) ≠ 0 := by
  have h3r : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  exact_mod_cast h3r

private lemma sqrt_pow_succ (n : ℕ) :
    Real.sqrt ((3 : ℝ) ^ (n + 1))
      = Real.sqrt 3 * Real.sqrt ((3 : ℝ) ^ n) := by
  rw [pow_succ, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 ^ n)]
  ring

private lemma sqrt_pow_succ' (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((3 : ℝ) ^ (n + 1)) = 3 * Real.sqrt ((3 : ℝ) ^ (n - 1)) := by
  have hexp : (3 : ℝ) ^ (n + 1) = 9 * (3 : ℝ) ^ (n - 1) := by
    have hn2 : n + 1 = 2 + (n - 1) := by omega
    rw [hn2, pow_add]
    have h9 : (3 : ℝ) ^ (2 : ℕ) = 9 := by norm_num
    rw [h9]
  rw [hexp, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
  have h9 : Real.sqrt 9 = 3 := by
    have h93 : (9 : ℝ) = 3 ^ 2 := by norm_num
    rw [h93, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  rw [h9]

private lemma powI_succ (n : ℕ) :
    Complex.I ^ (n + 1) = Complex.I * Complex.I ^ n :=
  pow_succ' Complex.I n

private lemma powI_succ' (n : ℕ) (hn : 1 ≤ n) :
    Complex.I ^ (n + 1) = -Complex.I ^ (n - 1) := by
  have hn2 : n + 1 = (n - 1) + 2 := by omega
  rw [hn2, pow_add, pow_two, Complex.I_mul_I]
  ring

/-- `1 - 2·legPt` is `-i/√3`. -/
private lemma one_sub_two_legPt :
    1 - 2 * legPt = -(Complex.I / (Real.sqrt 3 : ℂ)) := by
  have h3 := sqrt3_ne_zero
  simp only [legPt]
  field_simp
  ring

/-- Key scalar identity `i·√3·(-t) = 1`. -/
private lemma leg_scalar :
    Complex.I * (Real.sqrt 3 : ℂ) * (-(Complex.I / (Real.sqrt 3 : ℂ))) = 1 := by
  have hI := Complex.I_mul_I
  have hinv : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ sqrt3_ne_zero
  rw [div_eq_mul_inv]
  calc Complex.I * (Real.sqrt 3 : ℂ) * (-(Complex.I * (Real.sqrt 3 : ℂ)⁻¹))
      = (Complex.I * Complex.I) * ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹)
          * (-1) := by ring
    _ = (-1) * 1 * (-1) := by rw [hI, hinv]
    _ = 1 := by ring

/-- Binomial identity for the recurrence, case `n = 0`. -/
private lemma bonnet_n0 (j : ℕ) :
    ((0 + 1 : ℕ) : ℤ) * (((0 + 1).choose (j + 1) : ℕ) : ℤ)
        * ((((0 + 1) + (j + 1)).choose (0 + 1) : ℕ) : ℤ)
      = ((2 * 0 + 1 : ℕ) : ℤ)
          * (((((0).choose (j + 1) : ℕ) : ℤ)
              * (((0 + (j + 1)).choose 0 : ℕ) : ℤ))
            + 2 * ((((0).choose j : ℕ) : ℤ) * (((0 + j).choose 0 : ℕ) : ℤ)))
        - ((0 : ℕ) : ℤ) * ((((0 - 1).choose (j + 1) : ℕ) : ℤ)
          * (((((0 - 1) + (j + 1)).choose (0 - 1)) : ℕ) : ℤ)) := by
  cases j with
  | zero => decide
  | succ j =>
    have e01 : (0 : ℕ) - 1 = 0 := by omega
    rw [e01]
    have w1 : ((((0 + 1).choose (j + 1 + 1)) : ℕ) : ℤ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : 0 + 1 < j + 1 + 1)
    have w2 : ((((0).choose (j + 1 + 1)) : ℕ) : ℤ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1 + 1)
    have w3 : ((((0).choose (j + 1)) : ℕ) : ℤ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1)
    rw [w1, w2, w3]
    simp only [mul_zero, zero_mul, add_zero, sub_self]

/-- Binomial identity for the recurrence, case `j + 1 > n + 1` (all zero). -/
private lemma bonnet_key_d (n j : ℕ) (hgt : n + 1 < j + 1) :
    ((n + 1 : ℕ) : ℤ) * (((n + 1).choose (j + 1) : ℕ) : ℤ)
        * ((((n + 1) + (j + 1)).choose (n + 1) : ℕ) : ℤ)
      = ((2 * n + 1 : ℕ) : ℤ)
          * ((((n.choose (j + 1) : ℕ) : ℤ) * (((n + (j + 1)).choose n : ℕ) : ℤ))
            + 2 * ((((n.choose j : ℕ) : ℤ) * (((n + j).choose n : ℕ) : ℤ))))
        - (n : ℤ) * ((((n - 1).choose (j + 1) : ℕ) : ℤ)
          * (((((n - 1) + (j + 1)).choose (n - 1)) : ℕ) : ℤ)) := by
  have w1 : ((((n + 1).choose (j + 1) : ℕ)) : ℤ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt hgt
  have w2 : (((n.choose (j + 1) : ℕ)) : ℤ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n < j + 1)
  have w3 : (((n.choose j : ℕ)) : ℤ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n < j)
  have w4 : ((((n - 1).choose (j + 1) : ℕ)) : ℤ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n - 1 < j + 1)
  rw [w1, w2, w3, w4]
  simp only [mul_zero, zero_mul, add_zero, sub_self]

/-- Binomial identity for the recurrence, boundary case `j + 1 = n + 1`. -/
private lemma bonnet_case_c (n j : ℕ) (h : j + 1 = n + 1) :
    ((n + 1 : ℕ) : ℤ) * (((n + 1).choose (j + 1) : ℕ) : ℤ)
        * ((((n + 1) + (j + 1)).choose (n + 1) : ℕ) : ℤ)
      = ((2 * n + 1 : ℕ) : ℤ)
          * ((((n.choose (j + 1) : ℕ) : ℤ) * (((n + (j + 1)).choose n : ℕ) : ℤ))
            + 2 * ((((n.choose j : ℕ) : ℤ) * (((n + j).choose n : ℕ) : ℤ))))
        - (n : ℤ) * ((((n - 1).choose (j + 1) : ℕ) : ℤ)
          * (((((n - 1) + (j + 1)).choose (n - 1)) : ℕ) : ℤ)) := by
  have hjn : j = n := by omega
  rw [hjn]
  have z1 : (((n.choose (n + 1) : ℕ)) : ℤ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n < n + 1)
  have z2 : ((((n - 1).choose (n + 1) : ℕ)) : ℤ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n - 1 < n + 1)
  have o1 : ((((n + 1).choose (n + 1) : ℕ)) : ℤ) = 1 := by
    exact_mod_cast Nat.choose_self (n + 1)
  have o2 : (((n.choose n : ℕ)) : ℤ) = 1 := by
    exact_mod_cast Nat.choose_self n
  have eidx1 : (n + 1) + (n + 1) = 2 * n + 2 := by omega
  have eidx2 : n + n = 2 * n := by omega
  rw [z1, z2, o1, o2, eidx1, eidx2]
  simp only [mul_zero, zero_mul, mul_one, one_mul, zero_add, sub_zero]
  have s1 : ((((2 * n + 1).choose (n + 1) : ℕ)) : ℤ) * ((2 * n + 2 : ℕ) : ℤ)
      = ((((2 * n + 2).choose (n + 1) : ℕ)) : ℤ) * ((n + 1 : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq (2 * n + 1) (n + 1)
    have e1 : 2 * n + 1 + 1 = 2 * n + 2 := by omega
    rw [e1] at h
    have e2 : 2 * n + 2 - (n + 1) = n + 1 := by omega
    rw [e2] at h
    exact_mod_cast h
  have s2 : ((((2 * n).choose n : ℕ)) : ℤ) * ((2 * n + 1 : ℕ) : ℤ)
      = ((((2 * n + 1).choose (n + 1) : ℕ)) : ℤ) * ((n + 1 : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq (2 * n) n
    have e1 : 2 * n + 1 - n = n + 1 := by omega
    rw [e1] at h
    have s : (2 * n + 1).choose n = (2 * n + 1).choose (n + 1) :=
      Nat.choose_symm_of_eq_add (by omega : 2 * n + 1 = n + (n + 1))
    rw [s] at h
    exact_mod_cast h
  have hkey : ((n + 1 : ℕ) : ℤ) * ((((2 * n + 2).choose (n + 1) : ℕ)) : ℤ)
      = 2 * ((2 * n + 1 : ℕ) : ℤ) * ((((2 * n).choose n : ℕ)) : ℤ) := by
    have hpos : 0 < n + 1 := by omega
    have hM0 : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by exact_mod_cast hpos
    have key : ((n + 1 : ℕ) : ℤ)
          * (((n + 1 : ℕ) : ℤ) * ((((2 * n + 2).choose (n + 1) : ℕ)) : ℤ))
        = ((n + 1 : ℕ) : ℤ)
          * (2 * ((2 * n + 1 : ℕ) : ℤ) * ((((2 * n).choose n : ℕ)) : ℤ)) := by
      push_cast at s1 s2 ⊢
      linear_combination (-((n : ℤ) + 1)) * s1 + (-(2 * (n : ℤ) + 2)) * s2
    exact mul_left_cancel₀ (ne_of_gt hM0) key
  linear_combination hkey

/-- Main binomial identity for the recurrence, case `j + 1 ≤ n`. -/
private lemma bonnet_key (n j v : ℕ) (hnav : n = j + 1 + v) :
    ((n + 1 : ℕ) : ℤ) * (((n + 1).choose (j + 1) : ℕ) : ℤ)
        * ((((n + 1) + (j + 1)).choose (n + 1) : ℕ) : ℤ)
      = ((2 * n + 1 : ℕ) : ℤ)
          * ((((n.choose (j + 1) : ℕ) : ℤ) * (((n + (j + 1)).choose n : ℕ) : ℤ))
            + 2 * ((((n.choose j : ℕ) : ℤ) * (((n + j).choose n : ℕ) : ℤ))))
        - (n : ℤ) * ((((n - 1).choose (j + 1) : ℕ) : ℤ)
          * (((((n - 1) + (j + 1)).choose (n - 1)) : ℕ) : ℤ)) := by
  subst hnav
  have e_nm1 : j + 1 + v - 1 = j + v := by omega
  rw [e_nm1]
  have h1Z : ((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ) * ((j + 1 + v + 1 : ℕ) : ℤ)
      = ((((j + 1 + v + 1).choose (j + 1) : ℕ)) : ℤ) * ((v + 1 : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq (j + 1 + v) (j + 1)
    have e : j + 1 + v + 1 - (j + 1) = v + 1 := by omega
    rw [e] at h
    exact_mod_cast h
  have h2Z : ((((j + 1 + v) + (j + 1)).choose (j + 1 + v) : ℕ) : ℤ)
        * (((j + 1 + v + 1) + (j + 1) : ℕ) : ℤ)
      = ((((j + 1 + v + 1) + (j + 1)).choose (j + 1 + v + 1) : ℕ) : ℤ)
        * ((j + 1 + v + 1 : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq ((j + 1 + v) + (j + 1)) (j + 1)
    have eA2 : ((j + 1 + v) + (j + 1)) + 1 = (j + 1 + v + 1) + (j + 1) := by omega
    rw [eA2] at h
    have eA2' : (j + 1 + v + 1) + (j + 1) - (j + 1) = j + 1 + v + 1 := by omega
    rw [eA2'] at h
    have sA2 : ((j + 1 + v + 1) + (j + 1)).choose (j + 1)
        = ((j + 1 + v + 1) + (j + 1)).choose (j + 1 + v + 1) :=
      Nat.choose_symm_of_eq_add
        (by omega : (j + 1 + v + 1) + (j + 1) = (j + 1) + (j + 1 + v + 1))
    rw [sA2] at h
    have sB2 : ((j + 1 + v) + (j + 1)).choose (j + 1)
        = ((j + 1 + v) + (j + 1)).choose (j + 1 + v) :=
      Nat.choose_symm_of_eq_add
        (by omega : (j + 1 + v) + (j + 1) = (j + 1) + (j + 1 + v))
    rw [sB2] at h
    exact_mod_cast h
  have h3Z : ((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ) * ((j + 1 : ℕ) : ℤ)
      = ((((j + 1 + v).choose j : ℕ)) : ℤ) * ((v + 1 : ℕ) : ℤ) := by
    have h := Nat.choose_succ_right_eq (j + 1 + v) j
    have e3 : j + 1 + v - j = v + 1 := by omega
    rw [e3] at h
    exact_mod_cast h
  have h4Z : ((((j + 1 + v) + j).choose (j + 1 + v) : ℕ) : ℤ)
        * (((j + 1 + v) + (j + 1) : ℕ) : ℤ)
      = ((((j + 1 + v) + (j + 1)).choose (j + 1 + v) : ℕ) : ℤ)
        * ((j + 1 : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq ((j + 1 + v) + (j + 1) - 1) (j + 1 + v)
    have eN : (j + 1 + v) + (j + 1) - 1 + 1 = (j + 1 + v) + (j + 1) := by omega
    rw [eN] at h
    have eK : (j + 1 + v) + (j + 1) - (j + 1 + v) = j + 1 := by omega
    rw [eK] at h
    have eC : (j + 1 + v) + (j + 1) - 1 = (j + 1 + v) + j := by omega
    rw [eC] at h
    exact_mod_cast h
  have h5Z : ((((j + v).choose (j + 1) : ℕ)) : ℤ) * ((j + 1 + v : ℕ) : ℤ)
      = ((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ) * ((v : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq (j + v) (j + 1)
    have e5a : j + v + 1 = j + 1 + v := by omega
    rw [e5a] at h
    have e5b : j + 1 + v - (j + 1) = v := by omega
    rw [e5b] at h
    exact_mod_cast h
  have h6Z : ((((j + v) + (j + 1)).choose (j + v) : ℕ) : ℤ)
        * (((j + 1 + v) + (j + 1) : ℕ) : ℤ)
      = ((((j + 1 + v) + (j + 1)).choose (j + 1 + v) : ℕ) : ℤ)
        * ((j + 1 + v : ℕ) : ℤ) := by
    have h := Nat.choose_mul_succ_eq ((j + v) + (j + 1)) (j + 1)
    have eN6 : ((j + v) + (j + 1)) + 1 = (j + 1 + v) + (j + 1) := by omega
    rw [eN6] at h
    have eK6 : (j + 1 + v) + (j + 1) - (j + 1) = j + 1 + v := by omega
    rw [eK6] at h
    have sD2 : ((j + v) + (j + 1)).choose (j + 1)
        = ((j + v) + (j + 1)).choose (j + v) :=
      Nat.choose_symm_of_eq_add (by omega : (j + v) + (j + 1) = (j + 1) + (j + v))
    rw [sD2] at h
    have sB2 : ((j + 1 + v) + (j + 1)).choose (j + 1)
        = ((j + 1 + v) + (j + 1)).choose (j + 1 + v) :=
      Nat.choose_symm_of_eq_add
        (by omega : (j + 1 + v) + (j + 1) = (j + 1) + (j + 1 + v))
    rw [sB2] at h
    exact_mod_cast h
  have eA : ((v + 1 : ℕ) : ℤ) * ((j + 1 + v + 1 : ℕ) : ℤ)
        * (((((j + 1 + v + 1).choose (j + 1) : ℕ)) : ℤ)
          * ((((j + 1 + v + 1) + (j + 1)).choose (j + 1 + v + 1) : ℕ) : ℤ))
      = ((j + 1 + v + 1 : ℕ) : ℤ) * (((j + 1 + v + 1) + (j + 1) : ℕ) : ℤ)
        * (((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ)
          * ((((j + 1 + v) + (j + 1)).choose (j + 1 + v) : ℕ) : ℤ)) := by
    linear_combination
      (-((j + 1 + v + 1 : ℕ) : ℤ)
        * ((((j + 1 + v + 1) + (j + 1)).choose (j + 1 + v + 1) : ℕ) : ℤ)) * h1Z
      + (-((j + 1 + v + 1 : ℕ) : ℤ)
        * ((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ)) * h2Z
  have eC : ((v + 1 : ℕ) : ℤ) * (((j + 1 + v) + (j + 1) : ℕ) : ℤ)
        * (((((j + 1 + v).choose j : ℕ)) : ℤ)
          * ((((j + 1 + v) + j).choose (j + 1 + v) : ℕ) : ℤ))
      = ((j + 1 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ)
        * (((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ)
          * ((((j + 1 + v) + (j + 1)).choose (j + 1 + v) : ℕ) : ℤ)) := by
    linear_combination
      (-(((j + 1 + v) + (j + 1) : ℕ) : ℤ)
        * ((((j + 1 + v) + j).choose (j + 1 + v) : ℕ) : ℤ)) * h3Z
      + (((j + 1 : ℕ) : ℤ) * ((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ)) * h4Z
  have eD : ((j + 1 + v : ℕ) : ℤ) * (((j + 1 + v) + (j + 1) : ℕ) : ℤ)
        * (((((j + v).choose (j + 1) : ℕ)) : ℤ)
          * ((((j + v) + (j + 1)).choose (j + v) : ℕ) : ℤ))
      = ((v : ℕ) : ℤ) * ((j + 1 + v : ℕ) : ℤ)
        * (((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ)
          * ((((j + 1 + v) + (j + 1)).choose (j + 1 + v) : ℕ) : ℤ)) := by
    linear_combination
      ((((j + 1 + v) + (j + 1) : ℕ) : ℤ)
        * ((((j + v) + (j + 1)).choose (j + v) : ℕ) : ℤ)) * h5Z
      + (((v : ℕ) : ℤ) * ((((j + 1 + v).choose (j + 1) : ℕ)) : ℤ)) * h6Z
  push_cast at eA eC eD
  have hM0 : (v + 1) * (j + 1 + v + 1) * ((j + 1 + v) + (j + 1)) * (j + 1 + v)
      ≠ 0 := by
    have hpos : 0
        < (v + 1) * (j + 1 + v + 1) * ((j + 1 + v) + (j + 1)) * (j + 1 + v) := by
      positivity
    exact ne_of_gt hpos
  have hM0Z : ((((v + 1) * (j + 1 + v + 1) * ((j + 1 + v) + (j + 1))
      * (j + 1 + v) : ℕ)) : ℤ) ≠ 0 := by
    exact_mod_cast hM0
  refine mul_left_cancel₀ hM0Z ?_
  push_cast
  linear_combination
    (((j : ℤ) + 1 + (v : ℤ) + 1) * (((j : ℤ) + 1 + (v : ℤ) + (j : ℤ) + 1))
      * ((j : ℤ) + 1 + (v : ℤ))) * eA
    + (((j : ℤ) + 1 + (v : ℤ)) * ((v : ℤ) + 1) * ((j : ℤ) + 1 + (v : ℤ) + 1)) * eD
    + (-(2 * (2 * ((j : ℤ) + 1 + (v : ℤ)) + 1) * ((j : ℤ) + 1 + (v : ℤ) + 1)
      * ((j : ℤ) + 1 + (v : ℤ)))) * eC

/-- Three-term recurrence for the shifted Legendre polynomials. -/
private lemma bl_bonnet (n : ℕ) :
    Polynomial.C ((n + 1 : ℕ) : ℤ) * Polynomial.shiftedLegendre (n + 1)
      = Polynomial.C ((2 * n + 1 : ℕ) : ℤ)
          * ((1 - 2 * Polynomial.X) * Polynomial.shiftedLegendre n)
        - Polynomial.C ((n : ℕ) : ℤ) * Polynomial.shiftedLegendre (n - 1) := by
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  have hexp : (1 - 2 * Polynomial.X) * Polynomial.shiftedLegendre n
      = Polynomial.shiftedLegendre n
        - 2 * (Polynomial.X * Polynomial.shiftedLegendre n) := by
    ring
  rw [hexp]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_ofNat_mul]
  cases j with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero]
    have h0 : ∀ a : ℕ, (Polynomial.shiftedLegendre a).coeff 0 = 1 := by
      intro a
      rw [Polynomial.coeff_shiftedLegendre]
      simp
    simp only [h0]
    push_cast
    ring
  | succ j =>
    rw [Polynomial.coeff_X_mul]
    simp only [Polynomial.coeff_shiftedLegendre]
    have hp : ((-1 : ℤ) ^ (j + 1)) = (-1 : ℤ) ^ j * (-1) := pow_succ (-1 : ℤ) j
    rw [hp]
    by_cases hn0 : n = 0
    · subst hn0
      have hB := bonnet_n0 j
      linear_combination ((-1 : ℤ) ^ j * -1) * hB
    · rcases lt_trichotomy (j + 1) (n + 1) with hlt | heq | hgt
      · have hle : j + 1 ≤ n := by omega
        obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hle
        have hB := bonnet_key n j v hv
        linear_combination ((-1 : ℤ) ^ j * -1) * hB
      · have hB := bonnet_case_c n j heq
        linear_combination ((-1 : ℤ) ^ j * -1) * hB
      · have hB := bonnet_key_d n j hgt
        linear_combination ((-1 : ℤ) ^ j * -1) * hB

/-- Evaluated three-term recurrence for `legVal`. -/
private lemma bl_bonnet_eval (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * legVal (n + 1)
      = ((2 * n + 1 : ℕ) : ℂ) * (-(Complex.I / (Real.sqrt 3 : ℂ))) * legVal n
        - (n : ℂ) * legVal (n - 1) := by
  have h := congrArg (Polynomial.aeval legPt) (bl_bonnet n)
  simp only [map_sub, map_mul, map_natCast, map_one, map_ofNat,
    Polynomial.aeval_X] at h
  rw [one_sub_two_legPt] at h
  simp only [legVal] at ⊢
  linear_combination h

private lemma legSeq_zero : legSeq 0 = 1 := by
  have hleg0 : Polynomial.shiftedLegendre 0 = 1 := by simp [Polynomial.shiftedLegendre]
  simp only [legSeq, legVal, hleg0, map_one, pow_zero, Real.sqrt_one,
    Complex.ofReal_one, mul_one]

private lemma legSeq_one : legSeq 1 = 1 := by
  have hleg1 : Polynomial.shiftedLegendre 1 = 1 - 2 * Polynomial.X := by
    simp [Polynomial.shiftedLegendre, Finset.sum_range_succ]
    ring
  have g1 : legVal 1 = -(Complex.I / (Real.sqrt 3 : ℂ)) := by
    simp only [legVal, hleg1, map_sub, map_one, map_mul, map_ofNat,
      Polynomial.aeval_X]
    exact one_sub_two_legPt
  have s1 : (Real.sqrt ((3 : ℝ) ^ 1) : ℂ) = (Real.sqrt 3 : ℂ) := by rw [pow_one]
  have hI1 : Complex.I ^ 1 = Complex.I := pow_one Complex.I
  simp only [legSeq, hI1, s1, g1]
  exact leg_scalar

private lemma tri_zero_legendre : trinomialCoefficient 0 0 = 1 := by
  simp [trinomialCoefficient]

private lemma tri_one : trinomialCoefficient 1 1 = 1 := by
  unfold trinomialCoefficient
  simp [pow_one, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

private lemma base0 : triSeq 0 = legSeq 0 := by simp [triSeq, tri_zero_legendre, legSeq_zero]

private lemma base1 : triSeq 1 = legSeq 1 := by simp [triSeq, tri_one, legSeq_one]

/-- The Legendre sequence satisfies the central trinomial recurrence. -/
private lemma f_rec (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * legSeq (n + 1)
      = ((2 * n + 1 : ℕ) : ℂ) * legSeq n + 3 * (n : ℂ) * legSeq (n - 1) := by
  by_cases hn0 : n = 0
  · subst hn0
    change ((1 : ℕ) : ℂ) * legSeq 1
      = ((1 : ℕ) : ℂ) * legSeq 0 + 3 * ((0 : ℕ) : ℂ) * legSeq 0
    rw [legSeq_zero, legSeq_one]
    simp
  · have hn1 : 1 ≤ n := by omega
    have hB := bl_bonnet_eval n
    have hI1 := powI_succ n
    have hs1 : (Real.sqrt ((3 : ℝ) ^ (n + 1)) : ℂ)
        = (Real.sqrt 3 : ℂ) * (Real.sqrt ((3 : ℝ) ^ n) : ℂ) := by
      exact_mod_cast sqrt_pow_succ n
    have ht := leg_scalar
    have hI2 := powI_succ' n hn1
    have hs2 : (Real.sqrt ((3 : ℝ) ^ (n + 1)) : ℂ)
        = 3 * (Real.sqrt ((3 : ℝ) ^ (n - 1)) : ℂ) := by
      exact_mod_cast sqrt_pow_succ' n hn1
    simp only [legSeq]
    linear_combination
      (Complex.I ^ (n + 1) * (Real.sqrt ((3 : ℝ) ^ (n + 1)) : ℂ)) * hB
      + (((2 * n + 1 : ℕ) : ℂ) * legVal n * (-(Complex.I / (Real.sqrt 3 : ℂ)))
        * (Real.sqrt ((3 : ℝ) ^ (n + 1)) : ℂ)) * hI1
      + (((2 * n + 1 : ℕ) : ℂ) * legVal n * (-(Complex.I / (Real.sqrt 3 : ℂ)))
        * Complex.I * Complex.I ^ n) * hs1
      + (((2 * n + 1 : ℕ) : ℂ) * legVal n * Complex.I ^ n
        * (Real.sqrt ((3 : ℝ) ^ n) : ℂ)) * ht
      + (-(n : ℂ) * legVal (n - 1) * 3
        * (Real.sqrt ((3 : ℝ) ^ (n - 1)) : ℂ)) * hI2
      + (-(n : ℂ) * legVal (n - 1) * Complex.I ^ (n + 1)) * hs2

/-- The central trinomial recurrence over `ℂ`. -/
private lemma h_tri (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * triSeq (n + 1)
      = ((2 * n + 1 : ℕ) : ℂ) * triSeq n + 3 * (n : ℂ) * triSeq (n - 1) := by
  have h := centralTrinomialCoeff_three_term_recurrence n
  unfold triSeq
  exact_mod_cast h

private lemma tri_eq_leg (n : ℕ) : triSeq n = legSeq n := by
  have key : ∀ m : ℕ,
      triSeq m = legSeq m ∧ triSeq (m + 1) = legSeq (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨base0, base1⟩
    | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have ht := h_tri (m + 1)
      have hf := f_rec (m + 1)
      have e : m + 1 - 1 = m := by omega
      rw [e] at ht hf
      rw [h0, h1] at ht
      have hpos : 0 < m + 1 + 1 := by omega
      have hC : (((m + 1 + 1 : ℕ)) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hpos)
      rw [← hf] at ht
      exact mul_left_cancel₀ hC ht
  exact (key n).1

/--
**Central trinomial coefficients as Legendre values.** For a natural number $n$, let $c_n$ be the
central trinomial coefficient, the coefficient of $X^n$ in $(1 + X + X^2)^n$, and let $P_n$ be the
$n$th Legendre polynomial. Then, in the complex numbers,
$$
c_n = i^n \sqrt{3^n}\, P_n\Bigl(-\frac{i}{\sqrt{3}}\Bigr).
$$

Here $P_n(-i/\sqrt{3})$ is computed through the shifted Legendre polynomial
$\tilde{P}_n(y) = \sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{n+k}{n} y^k$, which satisfies
$\tilde{P}_n(y) = P_n(1 - 2y)$, evaluated at $y = (1 + i/\sqrt{3})/2$.

Proof: Bonnet's recurrence $(n+1) P_{n+1}(x) = (2n+1) x P_n(x) - n P_{n-1}(x)$, evaluated at
$x = -i/\sqrt{3}$ and rescaled by $i^n \sqrt{3^n}$, becomes the central trinomial recurrence
$(n+1) c_{n+1} = (2n+1) c_n + 3n c_{n-1}$ (OEIS A002426); both sides agree at $n = 0, 1$.

Proves `Wanted` entry `centralTrinomialCoeff_eq_legendre_specialValue`.

Source: P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky,
"Motzkin Numbers, Central Trinomial Coefficients and Hybrid Polynomials,"
Journal of Integer Sequences 11 (2008), Article 08.1.1, Proposition with
equation `eq20`, lines 337-343,
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Penson/penson131.tex>.
-/
public theorem centralTrinomialCoeff_eq_legendre_specialValue
    (n : ℕ) :
    (trinomialCoefficient n n : ℂ) =
      Complex.I ^ n * (Real.sqrt ((3 : ℝ) ^ n) : ℂ) *
        Polynomial.aeval ((1 + Complex.I / (Real.sqrt 3 : ℂ)) / 2)
          (Polynomial.shiftedLegendre n) := by
  change triSeq n = legSeq n
  exact tri_eq_leg n

end MetaMathlibExt
end
