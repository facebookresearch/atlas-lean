/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Portions modified by Meta Platforms, Inc. and affiliates.

The modifications replace the source-local inner product with Mathlib's
`dotProduct`, make proof-only helpers private, and expose only the reusable
finite-field counting statements.
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Matrix.Mul

import Mathlib.Algebra.Polynomial.Roots

/-!
# Parity counts from binary coordinates on a finite field

Let a finite field `F` be identified linearly with `s` binary coordinates.
For a nonempty set `V` of exponents below `m`, this file bounds the number of
pairs `(a, b)` for which an odd number of the binary dot products

`dotProduct (bits (a ^ E)) (bits b)`

equal one.  The main estimate follows because `∑ E ∈ V, X ^ E` is a
nonzero polynomial of degree at most `m - 1`; all but at most `m - 1` values
of `a` therefore give a nonzero vector, whose binary linear form takes the
value one on exactly half of the values of `b`.

The cleared-denominator bounds are adapted from
`eth/proof/variables/VariableBound/Family/SmallBias.lean` in Anthropic's
`formal-math` repository, commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.  They give a one-sided lower
bound on odd parity, not an absolute-bias estimate.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace FiniteField

section BinaryVectors

variable {s : ℕ}

private theorem binary_dotProduct_half (x : Fin s → ZMod 2) (hx : x ≠ 0) :
    2 * #{y : Fin s → ZMod 2 | dotProduct x y = 1} =
      Fintype.card (Fin s → ZMod 2) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi1 : x i = 1 := by
    have h : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    exact h _ hi
  have hswap :
      #{y : Fin s → ZMod 2 | dotProduct x y = 1} =
        #{y : Fin s → ZMod 2 | ¬ dotProduct x y = 1} := by
    refine Finset.card_equiv (Equiv.addRight (Pi.single i 1)) fun y ↦ ?_
    have h : ∀ c : ZMod 2, c = 1 ↔ ¬ c + 1 = 1 := by decide
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight,
      dotProduct_add, dotProduct_single_one, hi1]
    exact h _
  have hsum := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin s → ZMod 2))) (fun y ↦ dotProduct x y = 1)
  rw [card_univ] at hsum
  omega

end BinaryVectors

private theorem odd_card_filter_iff_sum_eq_one {I : Type*}
    (T : Finset I) (f : I → ZMod 2) :
    Odd #{i ∈ T | f i = 1} ↔ ∑ i ∈ T, f i = 1 := by
  have h : ∀ c : ZMod 2, c = if c = 1 then 1 else 0 := by decide
  rw [← ZMod.natCast_eq_one_iff_odd, natCast_card_filter]
  rw [sum_congr rfl fun i _ ↦ h (f i)]

private theorem card_pairs {A : Type*} [Fintype A]
    (Q : A × A → Prop) [DecidablePred Q] :
    #{p : A × A | Q p} = ∑ a : A, #{b : A | Q (a, b)} := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _

section ParityBridge

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {m s : ℕ}

private theorem sum_dotProduct_bits
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (V : Finset (Fin m)) (a b : F) :
    ∑ E ∈ V, dotProduct (bits (a ^ E.val)) (bits b) =
      dotProduct (bits (∑ E ∈ V, a ^ E.val)) (bits b) := by
  rw [map_sum, sum_dotProduct]

private theorem odd_power_dotProducts_iff
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (V : Finset (Fin m)) (a b : F) :
    Odd #{E ∈ V | dotProduct (bits (a ^ E.val)) (bits b) = 1} ↔
      dotProduct (bits (∑ E ∈ V, a ^ E.val)) (bits b) = 1 := by
  rw [odd_card_filter_iff_sum_eq_one, sum_dotProduct_bits]

end ParityBridge

section Polynomial

variable {F : Type*} [Field F] {m : ℕ}

private noncomputable def exponentPolynomial
    (V : Finset (Fin m)) : Polynomial F :=
  ∑ E ∈ V, Polynomial.X ^ E.val

private theorem eval_exponentPolynomial (V : Finset (Fin m)) (a : F) :
    (exponentPolynomial V).eval a = ∑ E ∈ V, a ^ E.val := by
  simp [exponentPolynomial, Polynomial.eval_finsetSum]

private theorem exponentPolynomial_ne_zero
    (V : Finset (Fin m)) (hV : V.Nonempty) :
    exponentPolynomial (F := F) V ≠ 0 := by
  obtain ⟨E₀, hE₀⟩ := hV
  intro hzero
  have hcoeff : (exponentPolynomial (F := F) V).coeff E₀.val = 1 := by
    rw [exponentPolynomial, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_X_pow]
    rw [sum_eq_single E₀]
    · simp
    · intro E _ hne
      exact ite_eq_right (fun h ↦ hne (Fin.ext h.symm))
    · exact fun h ↦ absurd hE₀ h
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

private theorem exponentPolynomial_natDegree_le (V : Finset (Fin m)) :
    (exponentPolynomial (F := F) V).natDegree ≤ m - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun E _ ↦ ?_
  rw [Polynomial.natDegree_X_pow]
  omega

private theorem card_exponent_sum_eq_zero_le [Fintype F] [DecidableEq F]
    (V : Finset (Fin m)) (hV : V.Nonempty) :
    #{a : F | ∑ E ∈ V, a ^ E.val = 0} ≤ m - 1 := by
  classical
  refine le_trans
    (Polynomial.card_le_degree_of_subset_roots
      (p := exponentPolynomial (F := F) V) fun a ha ↦ ?_)
    (exponentPolynomial_natDegree_le V)
  rw [Polynomial.mem_roots (exponentPolynomial_ne_zero V hV),
    Polynomial.IsRoot, eval_exponentPolynomial]
  simpa using ha

end Polynomial

section LinearForms

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  {s : ℕ}

private theorem card_eq_two_pow
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) :
    Fintype.card F = 2 ^ s := by
  rw [Fintype.card_congr bits.toEquiv, Fintype.card_pi_const, ZMod.card]

private theorem dotProduct_bits_half
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (w : F) (hw : w ≠ 0) :
    2 * #{b : F | dotProduct (bits w) (bits b) = 1} = Fintype.card F := by
  have hbits : bits w ≠ 0 := fun h ↦ hw (bits.map_eq_zero_iff.mp h)
  have hcard :
      #{b : F | dotProduct (bits w) (bits b) = 1} =
        #{y : Fin s → ZMod 2 | dotProduct (bits w) y = 1} :=
    Finset.card_equiv bits.toEquiv fun b ↦ by simp
  rw [hcard, binary_dotProduct_half _ hbits,
    Fintype.card_congr bits.toEquiv]

private theorem dotProduct_bits_zero_count
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) :
    #{b : F | dotProduct (bits 0) (bits b) = 1} = 0 := by
  simp

private theorem dotProduct_bits_count_le_half
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (w : F) :
    2 * #{b : F | dotProduct (bits w) (bits b) = 1} ≤ Fintype.card F := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [dotProduct_bits_zero_count]
    exact Nat.zero_le _
  · exact (dotProduct_bits_half bits w hw).le

end LinearForms

section Counts

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  {m s : ℕ}

/-- Let a finite field be written as `s` binary coordinates.  For a nonempty
set `V` of exponents below `m`, the number of pairs `(a, b)` for which an odd
number of the dot products `bits (a ^ E) ⬝ᵥ bits b` equal one satisfies the
cleared-denominator lower bound

`|F| ^ 2 ≤ 2 * oddPairs + (m - 1) * |F|`.

This is a one-sided odd-frequency estimate. -/
theorem odd_dotProduct_power_count
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (V : Finset (Fin m)) (hV : V.Nonempty) :
    Fintype.card F ^ 2 ≤
      2 * #{p : F × F |
        Odd #{E ∈ V |
          dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}} +
        (m - 1) * Fintype.card F := by
  classical
  rw [card_pairs, mul_sum]
  have hterm : ∀ a : F,
      Fintype.card F ≤
        2 * #{b : F |
          Odd #{E ∈ V |
            dotProduct (bits (a ^ E.val)) (bits b) = 1}} +
        if ∑ E ∈ V, a ^ E.val = 0 then Fintype.card F else 0 := by
    intro a
    simp only [odd_power_dotProducts_iff]
    split_ifs with hzero
    · exact Nat.le_add_left _ _
    · exact (dotProduct_bits_half bits _ hzero).ge
  calc
    Fintype.card F ^ 2 = ∑ _a : F, Fintype.card F := by
      rw [sum_const, card_univ, smul_eq_mul, sq]
    _ ≤ ∑ a : F,
        (2 * #{b : F |
          Odd #{E ∈ V |
            dotProduct (bits (a ^ E.val)) (bits b) = 1}} +
          if ∑ E ∈ V, a ^ E.val = 0 then Fintype.card F else 0) :=
      sum_le_sum fun a _ ↦ hterm a
    _ = ∑ a : F,
          2 * #{b : F |
            Odd #{E ∈ V |
              dotProduct (bits (a ^ E.val)) (bits b) = 1}} +
        #{a : F | ∑ E ∈ V, a ^ E.val = 0} * Fintype.card F := by
      rw [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (card_exponent_sum_eq_zero_le V hV)) _

/-- Under `16 * m ≤ 2 ^ s`, at least `15 / 32` of the field pairs have odd
parity across any nonempty exponent set `V`.  Fractions are cleared in the
statement. -/
theorem odd_dotProduct_power_count_of_sixteen_mul_le
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (h16 : 16 * m ≤ 2 ^ s) (V : Finset (Fin m)) (hV : V.Nonempty) :
    15 * Fintype.card F ^ 2 ≤
      32 * #{p : F × F |
        Odd #{E ∈ V |
          dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1}} := by
  have hcount := odd_dotProduct_power_count bits V hV
  rw [← card_eq_two_pow bits] at h16
  have herror :
      16 * ((m - 1) * Fintype.card F) ≤ Fintype.card F ^ 2 := by
    rw [sq, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (le_trans (by omega) h16)
  omega

/-- For one exponent `E`, at most half of all field pairs satisfy
`dotProduct (bits (a ^ E)) (bits b) = 1`. -/
theorem dotProduct_power_count_le_half
    (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (E : Fin m) :
    2 * #{p : F × F |
      dotProduct (bits (p.1 ^ E.val)) (bits p.2) = 1} ≤
        Fintype.card F ^ 2 := by
  classical
  rw [card_pairs, mul_sum]
  calc
    ∑ a : F, 2 * #{b : F |
        dotProduct (bits (a ^ E.val)) (bits b) = 1} ≤
        ∑ _a : F, Fintype.card F :=
      sum_le_sum fun a _ ↦ dotProduct_bits_count_le_half bits _
    _ = Fintype.card F ^ 2 := by
      rw [sum_const, card_univ, smul_eq_mul, sq]

end Counts

end FiniteField
