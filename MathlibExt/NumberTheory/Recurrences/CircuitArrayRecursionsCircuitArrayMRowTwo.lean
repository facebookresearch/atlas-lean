/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Basic
public import MathlibExt.NumberTheory.Recurrences.CircuitArray
public import MathlibExt.NumberTheory.Recurrences.CircuitArrayM
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Row two of the multivariable circuit array

We prove the closed form for row two of the multivariable circuit array `C^M`: for `s ≥ 2`,
`C^M_{2,s}` is a quadratic polynomial in `X_1` with coefficients linear in `X_2` over the
squared denominator `(3 * 9 ^ (s - 2) - 1 + X_1)^2`, and the shifted coefficient sequences are
annihilated by the polynomials of Table 4.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.12 (`fq-2024-hendel08232024rev2-cor-4.12`) and Table 4.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial
open circuitArrayM_row_one

private theorem arrayM_two (bdry : ℕ → Option (FractionRing (MvPolynomial ℕ ℚ))) (k : ℕ) :
    circuitArrayOf bdry 2 (k + 2) =
      circuitGrid bdry ((k + 1) + 1) (2 * k + 3) (k + 1) .left := by
  rw [circuitArrayOf, show 2 * (k + 2) - 1 = 2 * k + 3 by omega,
    show k + 2 - (2 + 1) / 2 = k + 1 by omega, show k + 2 = (k + 1) + 1 by omega]
  simp only [even_two, ite_true]

private theorem rf_num_ne (j : ℕ) :
    (9 * 9 ^ j - 1 + circuitVar 1 : FractionRing (MvPolynomial ℕ ℚ)) ≠ 0 := by
  intro h
  have hp : 9 * 9 ^ j - 1 + MvPolynomial.X 1 = (0 : MvPolynomial ℕ ℚ) := by
    apply IsFractionRing.injective (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
    simpa only [map_zero, map_one, map_add, map_sub, map_mul, map_pow, map_ofNat,
      circuitVar] using h
  have he := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) hp
  simp at he

private theorem rf_ne (j : ℕ) :
    (9 * 9 ^ j - 1 + circuitVar 1 : FractionRing (MvPolynomial ℕ ℚ)) /
        (3 * (3 * 9 ^ j - 1 + circuitVar 1)) ≠ 0 := by
  have hDj : (3 : FractionRing (MvPolynomial ℕ ℚ)) * 9 ^ j - 1 + circuitVar 1 ≠ 0 := by
    have hns := front_nonsingular j
    intro hcon
    apply hns
    linear_combination -hcon
  exact div_ne_zero (rf_num_ne j) (mul_ne_zero (by norm_num) hDj)

private theorem arm_combined (j : ℕ) :
    ((9 * 9 ^ j - 1 + circuitVar 1) / (3 * (3 * 9 ^ j - 1 + circuitVar 1)) +
        (9 * 9 ^ j - 1 + circuitVar 1) / (3 * (3 * 9 ^ j - 1 + circuitVar 1)) +
        (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
          9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
            16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ)))) /
          (9 * (3 * 9 ^ j - 1 + circuitVar 1) ^ 2) :
        FractionRing (MvPolynomial ℕ ℚ)) =
      (6 * (9 * 9 ^ j - 1 + circuitVar 1) * (3 * 9 ^ j - 1 + circuitVar 1) +
        (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
          9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
            16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ))))) /
        (9 * (3 * 9 ^ j - 1 + circuitVar 1) ^ 2) := by
  have hDj : (3 : FractionRing (MvPolynomial ℕ ℚ)) * 9 ^ j - 1 + circuitVar 1 ≠ 0 := by
    have hns := front_nonsingular j
    intro hcon
    apply hns
    linear_combination -hcon
  have h3D : (3 : FractionRing (MvPolynomial ℕ ℚ)) * (3 * 9 ^ j - 1 + circuitVar 1) ≠ 0 :=
    mul_ne_zero (by norm_num) hDj
  have h9D2 : (9 : FractionRing (MvPolynomial ℕ ℚ)) * (3 * 9 ^ j - 1 + circuitVar 1) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hDj)
  field_simp
  ring

private theorem arm_num_ne (j : ℕ) :
    6 * (9 * 9 ^ j - 1 + circuitVar 1) * (3 * 9 ^ j - 1 + circuitVar 1) +
        (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
          9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
            16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ)))) ≠ 0 := by
  intro h
  have hp : 6 * (9 * 9 ^ j - 1 + MvPolynomial.X 1) * (3 * 9 ^ j - 1 + MvPolynomial.X 1) +
      (81 ^ (j + 1) - 9 * (1 - MvPolynomial.X 1) ^ 2 +
        9 ^ (j + 1) * ((2 + MvPolynomial.X 1) ^ 2 * MvPolynomial.X 2 +
          (1 - MvPolynomial.X 1) ^ 2 - 9 -
          16 * (1 - MvPolynomial.X 1) * (j : MvPolynomial ℕ ℚ))) =
      (0 : MvPolynomial ℕ ℚ) := by
    apply IsFractionRing.injective (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
    simpa only [map_zero, map_one, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
      circuitVar] using h
  have he := congrArg (MvPolynomial.eval (fun _ => (1 : ℚ))) hp
  suffices he' : (6 : ℚ) * (9 * 9 ^ j) * (3 * 9 ^ j) +
      (81 ^ (j + 1) + 9 ^ (j + 1) * ((2 + 1) ^ 2 - 9)) = 0 by
    have hpos : (0:ℚ) < 6 * (9 * 9 ^ j) * (3 * 9 ^ j) +
        (81 ^ (j + 1) + 9 ^ (j + 1) * ((2 + 1) ^ 2 - 9)) := by
      have h0 : ((2:ℚ) + 1) ^ 2 - 9 = 0 := by norm_num
      rw [h0, mul_zero, add_zero]
      positivity
    exact (ne_of_gt hpos) he'
  simpa using he

private theorem arm_single_aux {K : Type*} [Field K] [CharZero K] (Rn D N : K) (hN : N ≠ 0)
    (hD : D ≠ 0) (h9D2 : 9 * D ^ 2 ≠ 0) :
    (Rn / (3 * D)) * (Rn / (3 * D)) / (N / (9 * D ^ 2)) = Rn ^ 2 / N := by
  have hNdiv := div_ne_zero hN h9D2
  have h9 : (9 : K) ≠ 0 := by norm_num
  field_simp
  ring

private theorem arm_single (j : ℕ) :
    ((9 * 9 ^ j - 1 + circuitVar 1) / (3 * (3 * 9 ^ j - 1 + circuitVar 1))) *
        ((9 * 9 ^ j - 1 + circuitVar 1) / (3 * (3 * 9 ^ j - 1 + circuitVar 1))) /
        ((6 * (9 * 9 ^ j - 1 + circuitVar 1) * (3 * 9 ^ j - 1 + circuitVar 1) +
          (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
            9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
              16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ))))) /
          (9 * (3 * 9 ^ j - 1 + circuitVar 1) ^ 2)) =
      (9 * 9 ^ j - 1 + circuitVar 1) ^ 2 /
        (6 * (9 * 9 ^ j - 1 + circuitVar 1) * (3 * 9 ^ j - 1 + circuitVar 1) +
          (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
            9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
              16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ))))) := by
  have hDj : (3 : FractionRing (MvPolynomial ℕ ℚ)) * 9 ^ j - 1 + circuitVar 1 ≠ 0 := by
    have hns := front_nonsingular j
    intro hcon
    apply hns
    linear_combination -hcon
  have h9D2 : (9 : FractionRing (MvPolynomial ℕ ℚ)) * (3 * 9 ^ j - 1 + circuitVar 1) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hDj)
  exact arm_single_aux _ _ _ (arm_num_ne j) hDj h9D2

private theorem delta_single1 {K : Type*} [Field K] (x q : K) (hq : q ≠ 0)
    (_h2f : 1 + (1 - (1 - x) / q) + 1 ≠ 0) (_hDf : x + 3 * q - 1 ≠ 0) :
    1 * (1 - (1 - x) / q) / (1 + (1 - (1 - x) / q) + 1) = (q - 1 + x) / (x + 3 * q - 1) := by
  field_simp
  ring

private theorem delta_single2 {K : Type*} [Field K] (x q : K) (hq : q ≠ 0)
    (_h3f : (1 - (1 - x) / q) + 1 + 1 ≠ 0) (_hDf : x + 3 * q - 1 ≠ 0) :
    (1 - (1 - x) / q) * 1 / ((1 - (1 - x) / q) + 1 + 1) = (q - 1 + x) / (x + 3 * q - 1) := by
  field_simp
  ring

private theorem second_front (bdry : ℕ → Option (FractionRing (MvPolynomial ℕ ℚ)))
    (h1 : bdry 1 = some (circuitVar 1)) (h2 : bdry 2 = some (circuitVar 2)) (j : ℕ) (r : ℕ)
    (hr : 2 * j + 3 ≤ r) :
    circuitGrid bdry ((j + 1) + 1) r (j + 1) .left =
        (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
          9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
            16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ)))) /
          (9 * (3 * 9 ^ j - 1 + circuitVar 1) ^ 2) ∧
      circuitGrid bdry ((j + 1) + 1) r (j + 1) .right =
        (9 * 9 ^ j - 1 + circuitVar 1) / (3 * (3 * 9 ^ j - 1 + circuitVar 1)) ∧
      circuitGrid bdry ((j + 1) + 1) r (j + 1) .base =
        (9 * 9 ^ j - 1 + circuitVar 1) / (3 * (3 * 9 ^ j - 1 + circuitVar 1)) := by
  have h1front : (bdry 1).getD (2 / 3) = 1 - (1 - circuitVar 1) := by
    rw [h1, Option.getD_some]
    ring
  revert hr
  induction j with
  | zero =>
    intro hr
    refine ⟨?_, ?_, ?_⟩
    · have hgrid : circuitGrid bdry ((0 + 1) + 1) r (0 + 1) .left = circuitVar 2 := by
        simp [circuitGrid, h2]
      rw [hgrid]
      have hD0 : (3 : FractionRing (MvPolynomial ℕ ℚ)) * 9 ^ (0:ℕ) - 1 + circuitVar 1 ≠ 0 := by
        have hns := front_nonsingular 0
        intro hcon
        apply hns
        linear_combination -hcon
      have hden : (9 : FractionRing (MvPolynomial ℕ ℚ)) *
        (3 * 9 ^ (0:ℕ) - 1 + circuitVar 1) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hD0)
      rw [eq_div_iff hden]
      simp only [zero_add, pow_zero, pow_one, Nat.cast_zero, mul_zero, sub_zero]
      ring
    · rw [circuitGrid_succ_right bdry (0 + 1) r (0 + 1) (by omega)]
      have hfront :=
        circuitGrid_front bdry (1 - circuitVar 1) h1front front_nonsingular 0 r (by omega)
      obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry 1
      rw [circuitGrid_eq_one_fun bdry (0 + 1) r ((0 + 1) + 1) le_rfl (by omega),
        circuitGrid_eq_one_fun bdry (0 + 1) (r + 1) ((0 + 1) + 1) le_rfl (by omega)]
      simp only [circuitRightEdge, circuitLeftArm, circuitRightArm, circuitTopArm]
      rw [hfront, hR r (0 + 1) (by omega) (by omega), hB r (0 + 1) (by omega) (by omega)]
      have hd : circuitVar 1 + 3 * 9 ^ (0:ℕ) - 1 ≠ 0 := by
        have hns := front_nonsingular 0
        intro hcon
        apply hns
        linear_combination -hcon
      exact (rightEdge_value _ _ (pow_ne_zero _ (by norm_num)) hd).trans (by ring)
    · rw [circuitGrid_succ_base bdry (0 + 1) r (0 + 1)]
      have hfront := circuitGrid_front bdry (1 - circuitVar 1) h1front front_nonsingular 0
        (r + 1) (by omega)
      obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry 1
      rw [circuitGrid_eq_one_fun bdry (0 + 1) (r + 2) ((0 + 1) + 1) le_rfl (by omega),
        circuitGrid_eq_one_fun bdry (0 + 1) (r + 1) ((0 + 1) + 1) le_rfl (by omega)]
      simp only [circuitBaseEdge, circuitLeftArm, circuitRightArm, circuitTopArm]
      rw [hfront, hR (r + 1) (0 + 1) (by omega) (by omega),
        hB (r + 1) (0 + 1) (by omega) (by omega)]
      have hd : circuitVar 1 + 3 * 9 ^ (0:ℕ) - 1 ≠ 0 := by
        have hns := front_nonsingular 0
        intro hcon
        apply hns
        linear_combination -hcon
      exact (rightEdge_value _ _ (pow_ne_zero _ (by norm_num)) hd).trans (by ring)
  | succ j ih =>
    intro hr
    have ih' := ih (by omega)
    obtain ⟨ihL, ihR, ihB⟩ := ih'
    refine ⟨?_, ?_, ?_⟩
    · rw [circuitGrid_succ_left bdry ((j + 1) + 1) r ((j + 1) + 1) (by omega),
        show ((j + 1) + 1) - 1 = j + 1 by omega]
      simp only [circuitLeftEdge, circuitRightArm, circuitLeftArm, circuitTopArm]
      have hfrontB := circuitGrid_front bdry (1 - circuitVar 1) h1front front_nonsingular
        (j + 1) r (by omega)
      have hfrontC := circuitGrid_front bdry (1 - circuitVar 1) h1front front_nonsingular
        (j + 1) (r + 1) (by omega)
      obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry ((j + 1) + 1)
      rw [ihL, ihR, ihB, hfrontB, hfrontC, hR r ((j + 1) + 1) le_rfl (by omega),
        hB r ((j + 1) + 1) le_rfl (by omega), hR (r + 1) ((j + 1) + 1) le_rfl (by omega),
        hB (r + 1) ((j + 1) + 1) le_rfl (by omega)]
      have h9 : (9 : FractionRing (MvPolynomial ℕ ℚ)) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hDf : circuitVar 1 + 3 * 9 ^ (j + 1) - 1 ≠ 0 := by
        have hns := front_nonsingular (j + 1)
        intro hcon
        apply hns
        linear_combination -hcon
      have h2f : (1 : FractionRing (MvPolynomial ℕ ℚ)) +
        (1 - (1 - circuitVar 1) / 9 ^ (j + 1)) + 1 ≠ 0 := by
        have e : (1 : FractionRing (MvPolynomial ℕ ℚ)) +
          (1 - (1 - circuitVar 1) / 9 ^ (j + 1)) + 1 =
            (circuitVar 1 + 3 * 9 ^ (j + 1) - 1) / 9 ^ (j + 1) := by
          field_simp
          ring
        rw [e]
        exact div_ne_zero hDf h9
      have h3f : (1 - (1 - circuitVar 1) / 9 ^ (j + 1)) + 1 + 1 ≠ 0 := by
        have e : (1 - (1 - circuitVar 1) / 9 ^ (j + 1)) + 1 + 1 =
            (circuitVar 1 + 3 * 9 ^ (j + 1) - 1) / 9 ^ (j + 1) := by
          field_simp
          ring
        rw [e]
        exact div_ne_zero hDf h9
      have hDj1 : (3 : FractionRing (MvPolynomial ℕ ℚ)) * 9 ^ (j + 1) - 1 + circuitVar 1 ≠ 0 := by
        have hns := front_nonsingular (j + 1)
        intro hcon
        apply hns
        linear_combination -hcon
      have h9D2' : (9 : FractionRing (MvPolynomial ℕ ℚ)) *
        (3 * 9 ^ (j + 1) - 1 + circuitVar 1) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hDj1)
      have h81 : (81 : FractionRing (MvPolynomial ℕ ℚ)) ^ j =
        ((9 : FractionRing (MvPolynomial ℕ ℚ)) ^ j) ^ 2 := by
        rw [show (81 : FractionRing (MvPolynomial ℕ ℚ)) = 9 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
      rw [circuitDelta, circuitDelta, circuitDelta, arm_combined j, arm_single j,
        delta_single1 (circuitVar 1) (9 ^ (j + 1)) h9 h2f hDf,
        delta_single2 (circuitVar 1) (9 ^ (j + 1)) h9 h3f hDf, circuitY]
      generalize hNdef : (6 * (9 * 9 ^ j - 1 + circuitVar 1) * (3 * 9 ^ j - 1 + circuitVar 1) +
        (81 ^ (j + 1) - 9 * (1 - circuitVar 1) ^ 2 +
          9 ^ (j + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
            16 * (1 - circuitVar 1) * (j : FractionRing (MvPolynomial ℕ ℚ))))) = N
      generalize hFdef : (circuitVar 1 + 3 * 9 ^ (j + 1) - 1) = F
      generalize hDdef : (3 * 9 ^ (j + 1) - 1 + circuitVar 1) = D'
      generalize hRdef : (9 * 9 ^ j - 1 + circuitVar 1) = R
      have hN : N ≠ 0 := by rw [← hNdef]; exact arm_num_ne j
      have hF : F ≠ 0 := by rw [← hFdef]; exact hDf
      have hD' : D' ≠ 0 := by rw [← hDdef]; exact hDj1
      have hR : R ≠ 0 := by rw [← hRdef]; exact rf_num_ne j
      have ha := div_ne_zero (pow_ne_zero 2 hR) hN
      have h9D'2 : (9 : FractionRing (MvPolynomial ℕ ℚ)) * D' ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hD')
      field_simp
      rw [← hNdef, ← hFdef, ← hDdef, ← hRdef]
      simp only [pow_succ']
      rw [h81]
      push_cast
      ring
    · rw [circuitGrid_succ_right bdry ((j + 1) + 1) r ((j + 1) + 1) (by omega)]
      have hfront := circuitGrid_front bdry (1 - circuitVar 1) h1front front_nonsingular
        (j + 1) r (by omega)
      obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry ((j + 1) + 1)
      rw [circuitGrid_eq_one_fun bdry ((j + 1) + 1) r (((j + 1) + 1) + 1) le_rfl (by omega),
        circuitGrid_eq_one_fun bdry ((j + 1) + 1) (r + 1) (((j + 1) + 1) + 1) le_rfl (by omega)]
      simp only [circuitRightEdge, circuitLeftArm, circuitRightArm, circuitTopArm]
      rw [hfront, hR r ((j + 1) + 1) le_rfl (by omega), hB r ((j + 1) + 1) le_rfl (by omega)]
      have hd : circuitVar 1 + 3 * 9 ^ (j + 1) - 1 ≠ 0 := by
        have hns := front_nonsingular (j + 1)
        intro hcon
        apply hns
        linear_combination -hcon
      exact (rightEdge_value _ _ (pow_ne_zero _ (by norm_num)) hd).trans (by ring)
    · rw [circuitGrid_succ_base bdry ((j + 1) + 1) r ((j + 1) + 1)]
      have hfront := circuitGrid_front bdry (1 - circuitVar 1) h1front front_nonsingular
        (j + 1) (r + 1) (by omega)
      obtain ⟨_, hR, hB⟩ := circuitGrid_eq_one bdry ((j + 1) + 1)
      rw [circuitGrid_eq_one_fun bdry ((j + 1) + 1) (r + 2) (((j + 1) + 1) + 1) le_rfl (by omega),
        circuitGrid_eq_one_fun bdry ((j + 1) + 1) (r + 1) (((j + 1) + 1) + 1) le_rfl (by omega)]
      simp only [circuitBaseEdge, circuitLeftArm, circuitRightArm, circuitTopArm]
      rw [hfront, hR (r + 1) ((j + 1) + 1) le_rfl (by omega),
        hB (r + 1) ((j + 1) + 1) le_rfl (by omega)]
      have hd : circuitVar 1 + 3 * 9 ^ (j + 1) - 1 ≠ 0 := by
        have hns := front_nonsingular (j + 1)
        intro hcon
        apply hns
        linear_combination -hcon
      exact (rightEdge_value _ _ (pow_ne_zero _ (by norm_num)) hd).trans (by ring)

private theorem sum_add_G (s : ℕ) (G : ℕ → ℚ) (p q : ℚ[X]) :
    (p + q).sum (fun i b => b * G (s + i)) =
      p.sum (fun i b => b * G (s + i)) + q.sum (fun i b => b * G (s + i)) :=
  sum_add_index p q _ (by simp) (by simp [add_mul])

private theorem sum_monomial_G (s : ℕ) (G : ℕ → ℚ) (n : ℕ) (a : ℚ) :
    (monomial n a).sum (fun i b => b * G (s + i)) = a * G (s + n) :=
  sum_monomial_index a _ (by simp)

/-- **Row 2 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 2$,
$$C^M_{2,s} = \frac{\sum_{i,j} c_{i,j}(s) X_1^i X_2^j}{(3 \cdot 9^{s-2} - 1 + X_1)^2},$$
where the sum runs over the six coefficients $c_{2,1}(s) = 9^{s-2}$, $c_{2,0}(s) = 9^{s-2} - 1$,
$c_{1,1}(s) = 4 \cdot 9^{s-2}$, $c_{1,0}(s) = 2 + (16(s-2) - 2) \cdot 9^{s-2}$,
$c_{0,1}(s) = 4 \cdot 9^{s-2}$ and
$c_{0,0}(s) = -1 + 9 \cdot 81^{s-2} - (8 + 16(s-2)) \cdot 9^{s-2}$.
Moreover, writing $E$ for the translation operator on rational sequences, the shifted coefficient
sequences $s \mapsto c_{i,j}(s+2)$, $s \ge 0$, are annihilated as in Table 4: $c_{0,0}$ by
$(E-81)(E-9)^2(E-1)$, $c_{0,1}$ by $(E-1)(E-9)$, $c_{1,0}$ by $(E-9)^2(E-1)$, $c_{1,1}$ by
$E-9$, $c_{2,0}$ by $(E-1)(E-9)$ and $c_{2,1}$ by $E-9$.

The paper's base case is $s = 3$; the identity also holds at $s = 2$. The recursions column of
Table 4 is omitted (its $X_1^0 X_2^1$ entry $G_s = 10G_{s-1} - G_{s-2}$ is misprinted for
$-9G_{s-2}$).

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.12 (`fq-2024-hendel08232024rev2-cor-4.12`) and Table 4. -/
public theorem circuitArrayM_row_two :
    (∀ s : ℕ, 2 ≤ s →
      circuitArrayM 2 s =
        (9 ^ (s - 2) * circuitVar 1 ^ 2 * circuitVar 2 + (9 ^ (s - 2) - 1) * circuitVar 1 ^ 2 +
            4 * 9 ^ (s - 2) * circuitVar 1 * circuitVar 2 +
            (2 + (16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2) - 2) * 9 ^ (s - 2)) *
              circuitVar 1 +
            4 * 9 ^ (s - 2) * circuitVar 2 +
            (-1 + 9 * 81 ^ (s - 2) - (8 + 16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2)) *
              9 ^ (s - 2))) /
          (3 * 9 ^ (s - 2) - 1 + circuitVar 1) ^ 2) ∧
      AnnihilatesSeq ((X - C 81) * (X - C 9) ^ 2 * (X - C 1))
        (fun s : ℕ => -1 + 9 * (81 : ℚ) ^ s - (8 + 16 * (s : ℚ)) * 9 ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 9) ^ 2 * (X - C 1)) (fun s : ℕ => 2 + (16 * (s : ℚ) - 2) * 9 ^ s) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => (9 : ℚ) ^ s - 1) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => (9 : ℚ) ^ s)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
    rw [circuitArrayM, arrayM_two]
    have h1M : (fun m => if m = 0 then none else some (circuitVar m)) 1 = some (circuitVar 1) := by
      simp
    have h2M : (fun m => if m = 0 then none else some (circuitVar m)) 2 = some (circuitVar 2) := by
      simp
    rw [(second_front _ h1M h2M k (2 * k + 3) (by omega)).1]
    have hNe : (81 ^ (k + 1) - 9 * (1 - circuitVar 1) ^ 2 +
          9 ^ (k + 1) * ((2 + circuitVar 1) ^ 2 * circuitVar 2 + (1 - circuitVar 1) ^ 2 - 9 -
            16 * (1 - circuitVar 1) * (k : FractionRing (MvPolynomial ℕ ℚ)))) =
        9 * (9 ^ ((k + 2) - 2) * circuitVar 1 ^ 2 * circuitVar 2 +
          (9 ^ ((k + 2) - 2) - 1) * circuitVar 1 ^ 2 +
          4 * 9 ^ ((k + 2) - 2) * circuitVar 1 * circuitVar 2 +
          (2 + (16 * (((k + 2 : ℕ) : FractionRing (MvPolynomial ℕ ℚ)) - 2) - 2) *
            9 ^ ((k + 2) - 2)) *
            circuitVar 1 +
          4 * 9 ^ ((k + 2) - 2) * circuitVar 2 +
          (-1 + 9 * 81 ^ ((k + 2) - 2) -
            (8 + 16 * (((k + 2 : ℕ) : FractionRing (MvPolynomial ℕ ℚ)) - 2)) *
              9 ^ ((k + 2) - 2))) := by
      simp only [Nat.add_sub_cancel, pow_succ']
      push_cast
      ring
    rw [hNe]
    exact mul_div_mul_left _ _ (by norm_num)
  · intro s
    have hP : ((((X - C 81) * (X - C 9) ^ 2 * (X - C 1) : ℚ[X])))
        = C 1 * X ^ 4 + C (-100) * X ^ 3 + C 1638 * X ^ 2 + C (-8100) * X ^ 1 +
          monomial 0 6561 := by
      simp only [C_1, C_neg, C_ofNat, monomial_zero_left]
      ring
    rw [hP]
    simp only [sum_add_G s (fun s : ℕ => -1 + 9 * (81 : ℚ) ^ s - (8 + 16 * (s : ℚ)) * 9 ^ s),
      C_mul_X_pow_eq_monomial,
      sum_monomial_G s (fun s : ℕ => -1 + 9 * (81 : ℚ) ^ s - (8 + 16 * (s : ℚ)) * 9 ^ s)]
    simp only [add_zero, pow_add]
    push_cast
    ring
  · intro s
    have hP : (((X - C 1) * (X - C 9) : ℚ[X])) = C 1 * X ^ 2 + C (-10) * X ^ 1 + monomial 0 9 := by
      simp only [C_1, C_neg, C_ofNat, monomial_zero_left]
      ring
    rw [hP]
    simp only [sum_add_G s (fun s : ℕ => 4 * (9 : ℚ) ^ s), C_mul_X_pow_eq_monomial,
      sum_monomial_G s (fun s : ℕ => 4 * (9 : ℚ) ^ s)]
    simp only [add_zero, pow_add]
    ring
  · intro s
    have hP : ((((X - C 9) ^ 2 * (X - C 1) : ℚ[X]))) =
      C 1 * X ^ 3 + C (-19) * X ^ 2 + C 99 * X ^ 1 + monomial 0 (-81) := by
      simp only [C_1, C_neg, C_ofNat, monomial_zero_left]
      ring
    rw [hP]
    simp only [sum_add_G s (fun s : ℕ => 2 + (16 * (s : ℚ) - 2) * 9 ^ s), C_mul_X_pow_eq_monomial,
      sum_monomial_G s (fun s : ℕ => 2 + (16 * (s : ℚ) - 2) * 9 ^ s)]
    simp only [add_zero, pow_add]
    push_cast
    ring
  · intro s
    have hP : ((X - C 9 : ℚ[X])) = C 1 * X ^ 1 + monomial 0 (-9) := by
      simp only [C_1, C_neg, C_ofNat, monomial_zero_left]
      ring
    rw [hP]
    simp only [sum_add_G s (fun s : ℕ => 4 * (9 : ℚ) ^ s), C_mul_X_pow_eq_monomial,
      sum_monomial_G s (fun s : ℕ => 4 * (9 : ℚ) ^ s)]
    simp only [add_zero, pow_succ]
    ring
  · intro s
    have hP : (((X - C 1) * (X - C 9) : ℚ[X])) = C 1 * X ^ 2 + C (-10) * X ^ 1 + monomial 0 9 := by
      simp only [C_1, C_neg, C_ofNat, monomial_zero_left]
      ring
    rw [hP]
    simp only [sum_add_G s (fun s : ℕ => (9 : ℚ) ^ s - 1), C_mul_X_pow_eq_monomial,
      sum_monomial_G s (fun s : ℕ => (9 : ℚ) ^ s - 1)]
    simp only [add_zero, pow_add]
    ring
  · intro s
    have hP : ((X - C 9 : ℚ[X])) = C 1 * X ^ 1 + monomial 0 (-9) := by
      simp only [C_1, C_neg, C_ofNat, monomial_zero_left]
      ring
    rw [hP]
    simp only [sum_add_G s (fun s : ℕ => (9 : ℚ) ^ s), C_mul_X_pow_eq_monomial,
      sum_monomial_G s (fun s : ℕ => (9 : ℚ) ^ s)]
    simp only [add_zero, pow_succ]
    ring

end

end MetaMathlibExt
