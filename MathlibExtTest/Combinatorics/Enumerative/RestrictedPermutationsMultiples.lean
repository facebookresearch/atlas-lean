/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.RestrictedPermutationsMultiples

open MetaMathlibExt

-- The empty board has one permutation, including when there are several residue classes.
example : Nat.card {π : Equiv.Perm (Fin 0) //
    ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-3, 0, 6} : Finset ℤ)} = 1 :=
  (card_strongPerms_multiples_eq_fibonacciP 3 2 0 0 (by decide) (by decide)).trans (by
    rw [show 0 + 1 = 1 by rfl, fibonacciP_eq_one 2 1 (by decide) (by decide)]
    simp)

-- For displacements −2, 0, and 4, the five positions split into classes of lengths
-- three and two. Only the longer class can have a nontrivial cycle.
example : Nat.card {π : Equiv.Perm (Fin 5) //
    ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-2, 0, 4} : Finset ℤ)} = 2 :=
  (card_strongPerms_multiples_eq_fibonacciP 2 2 2 1 (by decide) (by decide)).trans (by
    have h₁ := fibonacciP_eq_one 2 1 (by decide) (by decide)
    have h₂ := fibonacciP_eq_one 2 2 (by decide) (by decide)
    have h₃ : fibonacciP 2 3 = 1 := by
      rw [fibonacciP_rec 2 3 (by decide)]
      change fibonacciP 2 2 + fibonacciP 2 0 = 1
      simp [h₂]
    have h₄ : fibonacciP 2 4 = 2 := by
      rw [fibonacciP_rec 2 4 (by decide)]
      change fibonacciP 2 3 + fibonacciP 2 1 = 2
      rw [h₃, h₁]
    change fibonacciP 2 3 ^ 1 * fibonacciP 2 4 ^ 1 = 2
    simp [h₃, h₄])

-- With displacements −1, 0, and 1 there are eight permutations given by disjoint adjacent swaps.
example : Nat.card {π : Equiv.Perm (Fin 5) //
    ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-1, 0, 1} : Finset ℤ)} = 8 :=
  (card_strongPerms_multiples_eq_fibonacciP 1 1 5 0 (by decide) (by decide)).trans (by
    rw [fibonacciP_one, fibonacciP_one]
    decide)

private abbrev HasRestrictedExcedances {n : ℕ} (m j k : ℕ) (π : Equiv.Perm (Fin n)) : Prop :=
  (∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-(m : ℤ), 0, ((j * m : ℕ) : ℤ)} : Finset ℤ)) ∧
    excedanceCount n π = k

-- Enumerate the permutations directly. The two residue classes have lengths three and two.
example : (List.range 4).map (fun k => Nat.card {π : Equiv.Perm (Fin 5) //
    HasRestrictedExcedances 2 1 k π}) = [1, 3, 2, 0] := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

-- Independently compute the coefficients from the two small recurrence polynomials.
example : (List.range 4).map (fun k => (oneTBonacciPolynomial 1 2 *
    oneTBonacciPolynomial 1 3).coeff k) = [1, 3, 2, 0] := by
  let X : Polynomial ℕ := Polynomial.X
  have h₀ := oneTBonacciPolynomial_zero 1
  have h₁ := oneTBonacciPolynomial_succ_of_lt 1 0 (by decide)
  have h₂ := oneTBonacciPolynomial_succ_of_le 1 1 (by decide)
  have h₃ := oneTBonacciPolynomial_succ_of_le 1 2 (by decide)
  have h : oneTBonacciPolynomial 1 2 * oneTBonacciPolynomial 1 3 =
      1 + Polynomial.C 3 * X + Polynomial.C 2 * X ^ 2 := by
    rw [h₃, h₂]
    simp only [Nat.reduceSub, h₀, h₁, mul_one, Polynomial.C_ofNat, X]
    ring
  rw [h]
  norm_num [X, List.range_succ, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]

-- With jump size four on three positions there can be no excedance.
example : (List.range 2).map (fun k => Nat.card {π : Equiv.Perm (Fin 3) //
    HasRestrictedExcedances 2 2 k π}) = [1, 0] := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

example : (List.range 2).map (fun k => (oneTBonacciPolynomial 2 1 *
    oneTBonacciPolynomial 2 2).coeff k) = [1, 0] := by
  rw [oneTBonacciPolynomial_succ_of_lt 2 1 (by decide),
    oneTBonacciPolynomial_succ_of_lt 2 0 (by decide), oneTBonacciPolynomial_zero]
  simp [List.range_succ, Polynomial.coeff_one]

-- At the threshold the only nonidentity permutation is a three-cycle with one excedance.
example : (List.range 3).map (fun k => Nat.card {π : Equiv.Perm (Fin 3) //
    HasRestrictedExcedances 1 2 k π}) = [1, 1, 0] := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

example : (List.range 3).map (fun k => (oneTBonacciPolynomial 2 3).coeff k) = [1, 1, 0] := by
  rw [oneTBonacciPolynomial_succ_of_le 2 2 (by decide),
    oneTBonacciPolynomial_succ_of_lt 2 1 (by decide),
    oneTBonacciPolynomial_succ_of_lt 2 0 (by decide)]
  norm_num [List.range_succ, oneTBonacciPolynomial_zero, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_X]

-- The public theorem at board length five and excedance count two.
example : Nat.card {π : Equiv.Perm (Fin 5) // HasRestrictedExcedances 2 1 2 π} =
    (oneTBonacciPolynomial 1 2 * oneTBonacciPolynomial 1 3).coeff 2 := by
  simpa only [Nat.reduceSub, pow_one] using
    card_strongPerms_multiples_excedance_eq_coeff 2 1 2 1 2 (by decide) (by decide)

-- Count both distributions directly, without using the coefficient formula.
example :
    ((List.range 4).map (fun k => Nat.card {π : Equiv.Perm (Fin 5) //
      HasRestrictedExcedances 3 1 k π}) = [1, 2, 1, 0]) ∧
    ((List.range 4).map (fun k => Nat.card {π : Equiv.Perm (Fin 4) //
      HasRestrictedExcedances 2 1 k π}) = [1, 2, 1, 0]) := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

private theorem bonacciOne : oneTBonacciPolynomial 1 1 = 1 :=
  (oneTBonacciPolynomial_succ_of_lt 1 0 (by decide)).trans (oneTBonacciPolynomial_zero 1)

private theorem coeffs_bonacciTwo_sq :
    (List.range 4).map (fun k => (oneTBonacciPolynomial 1 2 ^ 2).coeff k) = [1, 2, 1, 0] := by
  have h : oneTBonacciPolynomial 1 2 = 1 + Polynomial.X := by
    rw [oneTBonacciPolynomial_succ_of_le 1 1 (by decide), bonacciOne]
    simp [oneTBonacciPolynomial_zero]
  rw [h, show ((1 + Polynomial.X) ^ 2 : Polynomial ℕ) =
      1 + Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2 by
    rw [Polynomial.C_ofNat]
    ring]
  norm_num [List.range_succ, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]

-- Two longer classes of size two contribute the square; the size-one class contributes one.
example : (List.range 4).map (fun k => Nat.card {π : Equiv.Perm (Fin 5) //
    HasRestrictedExcedances 3 1 k π}) = [1, 2, 1, 0] := by
  have h (k : ℕ) :=
    card_strongPerms_multiples_excedance_eq_coeff 3 1 1 2 k (by decide) (by decide)
  simpa only [h, Nat.reduceSub, pow_one, bonacciOne, one_mul] using coeffs_bonacciTwo_sq

-- With no longer classes, only the two shorter classes of size two contribute factors.
example : (List.range 4).map (fun k => Nat.card {π : Equiv.Perm (Fin 4) //
    HasRestrictedExcedances 2 1 k π}) = [1, 2, 1, 0] := by
  have h (k : ℕ) :=
    card_strongPerms_multiples_excedance_eq_coeff 2 1 2 0 k (by decide) (by decide)
  simpa only [h, Nat.sub_zero, pow_zero, mul_one] using coeffs_bonacciTwo_sq
