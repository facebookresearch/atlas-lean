/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Convergents of polynomial continued fractions form a Farey path

We define the numerator and denominator recurrences for finite continued fractions
with polynomial partial quotients and prove
`MetaMathlibExt.polyContFract_convergents_farey_path`: every convergent is a polynomial
fraction in lowest terms, and consecutive convergents have unit determinant.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 4.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

private noncomputable def convNum {F : Type*} [Field F] (a : ℕ → F[X]) : ℕ → F[X]
  | 0 => a 0
  | 1 => a 1 * a 0 + 1
  | i + 2 => a (i + 2) * convNum a (i + 1) + convNum a i

private noncomputable def convDen {F : Type*} [Field F] (a : ℕ → F[X]) : ℕ → F[X]
  | 0 => 1
  | 1 => a 1
  | i + 2 => a (i + 2) * convDen a (i + 1) + convDen a i

private theorem convNum_add_two {F : Type*} [Field F] (a : ℕ → F[X]) (i : ℕ) :
    convNum a (i + 2) = a (i + 2) * convNum a (i + 1) + convNum a i := rfl

private theorem convDen_add_two {F : Type*} [Field F] (a : ℕ → F[X]) (i : ℕ) :
    convDen a (i + 2) = a (i + 2) * convDen a (i + 1) + convDen a i := rfl

private theorem isCoprime_of_isUnit_det {F : Type*} [Field F] (A A' B B' : F[X])
    (h : IsUnit (A * B' - A' * B)) : IsCoprime A B := by
  obtain ⟨u, hu⟩ := h
  have hinv : (u : F[X]) * ((u⁻¹ : F[X]ˣ) : F[X]) = 1 := Units.mul_inv u
  refine ⟨B' * ((u⁻¹ : F[X]ˣ) : F[X]), -(A' * ((u⁻¹ : F[X]ˣ) : F[X])), ?_⟩
  linear_combination (-((u⁻¹ : F[X]ˣ) : F[X])) * hu + hinv

private theorem conv_farey_aux {F : Type*} [Field F] (a : ℕ → F[X]) (n : ℕ)
    (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) (i : ℕ) (hi : i ≤ n) :
    (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (convNum a i) ∧
    (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (convDen a i) ∧
    convDen a i ≠ 0 ∧ IsCoprime (convNum a i) (convDen a i) ∧
    (1 ≤ i → IsUnit (convNum a i * convDen a (i - 1) -
      convNum a (i - 1) * convDen a i)) ∧
    (1 ≤ i → (convDen a (i - 1)).degree < (convDen a i).degree) := by
  induction i using Nat.twoStepInduction with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact polyContFract_nums_zero a n
    · simpa only [convDen, map_one] using polyContFract_dens_zero a n
    · change (1 : F[X]) ≠ 0
      exact one_ne_zero
    · change IsCoprime (a 0) 1
      exact isCoprime_one_right
    · intro h
      exact absurd h (by decide)
    · intro h
      exact absurd h (by decide)
  | one =>
    have hn0 : 0 < n := by omega
    have hpos1 : 0 < (a 1).natDegree := ha 1 le_rfl hi
    have hne1 : a 1 ≠ 0 := ne_zero_of_natDegree_gt hpos1
    have hdet1 : convNum a 1 * convDen a (1 - 1) - convNum a (1 - 1) * convDen a 1 = 1 := by
      change (a 1 * a 0 + 1) * 1 - a 0 * a 1 = 1
      ring
    have hU1 : IsUnit (convNum a 1 * convDen a (1 - 1) -
        convNum a (1 - 1) * convDen a 1) := by
      rw [hdet1]
      exact isUnit_one
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact polyContFract_nums_one a hn0
    · exact polyContFract_dens_one a hn0
    · change a 1 ≠ 0
      exact hne1
    · exact isCoprime_of_isUnit_det _ _ _ _ hU1
    · intro _
      exact hU1
    · intro _
      change (1 : F[X]).degree < (a 1).degree
      rw [degree_one]
      exact natDegree_pos_iff_degree_pos.mp hpos1
  | more i ih₀ ih₁ =>
    obtain ⟨hN₀, hD₀, hB₀, -, -, -⟩ := ih₀ (by omega)
    obtain ⟨hN₁, hD₁, hB₁, -, hU₁, hdeg₁⟩ := ih₁ (by omega)
    have hs : (polyContFract a n).s.get? (i + 1) =
        some ⟨1, algebraMap F[X] (RatFunc F) (a (i + 2))⟩ := by
      simp [polyContFract_s_get?, show i + 1 < n by omega]
    have hN₂ : (polyContFract a n).nums (i + 2) =
        algebraMap F[X] (RatFunc F) (convNum a (i + 2)) := by
      rw [GenContFract.nums_recurrence hs hN₀ hN₁]
      simpa only [map_add, map_mul, one_mul] using
        congrArg (algebraMap F[X] (RatFunc F)) (convNum_add_two a i).symm
    have hD₂ : (polyContFract a n).dens (i + 2) =
        algebraMap F[X] (RatFunc F) (convDen a (i + 2)) := by
      rw [GenContFract.dens_recurrence hs hD₀ hD₁]
      simpa only [map_add, map_mul, one_mul] using
        congrArg (algebraMap F[X] (RatFunc F)) (convDen_add_two a i).symm
    have hnpos : 0 < (a (i + 2)).natDegree := ha (i + 2) (by omega) hi
    have hane : a (i + 2) ≠ 0 := ne_zero_of_natDegree_gt hnpos
    have hdeg01 : (convDen a i).degree < (convDen a (i + 1)).degree := hdeg₁ (by omega)
    have hnat_lt : (convDen a i).natDegree < (convDen a (i + 1)).natDegree :=
      natDegree_lt_natDegree hB₀ hdeg01
    have hmul_ne : a (i + 2) * convDen a (i + 1) ≠ 0 := mul_ne_zero hane hB₁
    have hdom : (convDen a i).degree < (a (i + 2) * convDen a (i + 1)).degree := by
      rw [degree_eq_natDegree hB₀, degree_eq_natDegree hmul_ne, natDegree_mul hane hB₁]
      have hlt : (convDen a i).natDegree
          < (a (i + 2)).natDegree + (convDen a (i + 1)).natDegree := by omega
      exact_mod_cast hlt
    have hB2nat : (convDen a (i + 2)).natDegree =
        (a (i + 2)).natDegree + (convDen a (i + 1)).natDegree := by
      rw [convDen_add_two, natDegree_add_eq_left_of_degree_lt hdom, natDegree_mul hane hB₁]
    have hB2pos : 0 < (convDen a (i + 2)).natDegree := by omega
    have hB2ne : convDen a (i + 2) ≠ 0 := ne_zero_of_natDegree_gt hB2pos
    have hsub : i + 2 - 1 = i + 1 := by omega
    have hneg : convNum a (i + 2) * convDen a (i + 2 - 1) -
        convNum a (i + 2 - 1) * convDen a (i + 2)
        = -(convNum a (i + 1) * convDen a i - convNum a i * convDen a (i + 1)) := by
      rw [hsub, convNum_add_two, convDen_add_two]
      ring
    have hU2 : IsUnit (convNum a (i + 2) * convDen a (i + 2 - 1) -
        convNum a (i + 2 - 1) * convDen a (i + 2)) := by
      rw [hneg]
      exact (hU₁ (by omega)).neg
    have hC2 : IsCoprime (convNum a (i + 2)) (convDen a (i + 2)) :=
      isCoprime_of_isUnit_det _ _ _ _ hU2
    have hdeg2 : (convDen a (i + 1)).degree < (convDen a (i + 2)).degree := by
      rw [degree_eq_natDegree hB₁, degree_eq_natDegree hB2ne]
      have hlt : (convDen a (i + 1)).natDegree < (convDen a (i + 2)).natDegree := by omega
      exact_mod_cast hlt
    have hdeg2' : (convDen a (i + 2 - 1)).degree < (convDen a (i + 2)).degree := by
      rw [hsub]
      exact hdeg2
    exact ⟨hN₂, hD₂, hB2ne, hC2, fun _ => hU2, fun _ => hdeg2'⟩

/-- **Convergents of a polynomial continued fraction form a Farey path.** Let $F$ be a field, let
$n \in \mathbb N$, and let $a_0, a_1, \dots, a_n \in F[X]$ with $a_i$ nonconstant for
$1 \le i \le n$. Write $A_i$ and $B_i$ for the numerator and the denominator of the $i$th
convergent $A_i / B_i$ of the continued fraction $[a_0, a_1, \dots, a_n]$ over $F(X)$. Then for
every $i \le n$, $A_i$ and $B_i$ are polynomials in $F[X]$, $B_i \ne 0$, and $A_i$ and $B_i$ are
coprime in $F[X]$; and for $1 \le i \le n$, the polynomial $A_i B_{i-1} - A_{i-1} B_i$ is a unit
of $F[X]$, that is, a nonzero constant.

In the language of the paper, each convergent $A_i / B_i$ is a vertex of the Farey graph over $F$
and consecutive convergents are adjacent in it.

Source: Tuangrat Chaichana, Arlisa Janjing and Teeraphong Phongpattanacharoen,
*An Interpretation of Continued Fractions and Farey Graphs in the Field of
Rational Functions*, INTEGERS 26 (2026), Article A3, Theorem 4. -/
public theorem polyContFract_convergents_farey_path {F : Type*} [Field F] (a : ℕ → F[X]) (n : ℕ)
    (ha : ∀ i, 1 ≤ i → i ≤ n → 0 < (a i).natDegree) :
    ∃ A B : ℕ → F[X], ∀ i ≤ n,
      (polyContFract a n).nums i = algebraMap F[X] (RatFunc F) (A i) ∧
      (polyContFract a n).dens i = algebraMap F[X] (RatFunc F) (B i) ∧
      B i ≠ 0 ∧ IsCoprime (A i) (B i) ∧
      (1 ≤ i → IsUnit (A i * B (i - 1) - A (i - 1) * B i)) := by
  refine ⟨convNum a, convDen a, fun i hi => ?_⟩
  obtain ⟨hN, hD, hB, hC, hU, -⟩ := conv_farey_aux a n ha i hi
  exact ⟨hN, hD, hB, hC, hU⟩

end

end MetaMathlibExt
