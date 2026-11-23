/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.MvPolynomial.LinearProduct
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.ZMod.Basic

@[expose] public section

set_option autoImplicit false

open MvPolynomial

private noncomputable def pInt : MvPolynomial (Fin 2) ℤ :=
  monomial (Finsupp.single 0 1) 2 - monomial (Finsupp.single 1 1) 3

private noncomputable def qInt : MvPolynomial (Fin 2) ℤ :=
  monomial (Finsupp.single 0 2) 1 +
    monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 4

private noncomputable def m21 : Fin 2 →₀ ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 1

private theorem single_zero_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
  intro h
  have h0 := DFunLike.congr_fun h 0
  norm_num at h0

private theorem single_zero_add_self :
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 0 1 : Fin 2 →₀ ℕ) =
      Finsupp.single 0 2 := by
  ext i
  fin_cases i <;> simp

private theorem mixed_ne_square :
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
      Finsupp.single 0 2 := by
  intro h
  have h1 := DFunLike.congr_fun h 1
  norm_num at h1

private theorem m21_sub_zero :
    m21 - Finsupp.single 0 1 = Finsupp.single 0 1 + Finsupp.single 1 1 := by
  ext i
  fin_cases i <;> simp [m21]

private theorem m21_sub_one :
    m21 - Finsupp.single 1 1 = Finsupp.single 0 2 := by
  ext i
  fin_cases i <;> simp [m21]

private theorem single_three_sub_one :
    (Finsupp.single (0 : Fin 2) 3 : Fin 2 →₀ ℕ) - Finsupp.single 0 1 =
      Finsupp.single 0 2 := by
  ext i
  fin_cases i <;> simp

private theorem pInt_isHomogeneous : pInt.IsHomogeneous 1 := by
  rw [pInt]
  exact (isHomogeneous_monomial 2 (by simp)).sub
    (isHomogeneous_monomial 3 (by simp))

example : pInt = C 2 * X 0 - C 3 * X 1 := by
  rw [pInt]
  simp only [MvPolynomial.X]
  rw [MvPolynomial.C_mul_monomial, MvPolynomial.C_mul_monomial]
  norm_num

example : qInt = X 0 ^ 2 + C 4 * X 0 * X 1 := by
  rw [qInt]
  simp only [MvPolynomial.X, pow_two]
  rw [MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial, single_zero_add_self]
  norm_num

-- Both supported variables contribute: `2 * 4 + (-3) * 1 = 5`.
example : (pInt * qInt).coeff m21 = 5 := by
  rw [pInt_isHomogeneous.coeff_mul_eq_sum_support]
  have hm : m21.support = {0, 1} := by
    ext i
    fin_cases i <;> simp [m21]
  rw [hm]
  simp only [Finset.sum_insert, Finset.mem_singleton, Fin.zero_ne_one, not_false_eq_true,
    Finset.sum_singleton]
  rw [m21_sub_zero, m21_sub_one]
  norm_num [pInt, qInt, single_zero_ne_single_one, Ne.symm single_zero_ne_single_one,
    mixed_ne_square, Ne.symm mixed_ne_square]

-- The concrete mixed-variable coefficient is computed by the public rule.
example :
    (pInt * qInt).coeff m21 =
      ∑ i ∈ m21.support, pInt.coeff (Finsupp.single i 1) *
        qInt.coeff (m21 - Finsupp.single i 1) :=
  pInt_isHomogeneous.coeff_mul_eq_sum_support qInt m21

-- Removing one occurrence of the repeated variable gives coefficient `2`, not `3 * 2`.
example : (pInt * qInt).coeff (Finsupp.single 0 3) = 2 := by
  rw [pInt_isHomogeneous.coeff_mul_eq_sum_support]
  rw [Finsupp.support_single 0 (by norm_num), Finset.sum_singleton,
    single_three_sub_one]
  norm_num [pInt, qInt, single_zero_ne_single_one, Ne.symm single_zero_ne_single_one,
    mixed_ne_square]

-- The constant and an unsupported degree-one monomial have zero coefficient.
example : (pInt * qInt).coeff 0 = 0 := by
  rw [pInt_isHomogeneous.coeff_mul_eq_sum_support]
  simp

example : (pInt * qInt).coeff (Finsupp.single 0 1) = 0 := by
  rw [pInt_isHomogeneous.coeff_mul_eq_sum_support,
    Finsupp.support_single 0 (by norm_num), Finset.sum_singleton]
  norm_num [qInt]

-- Either zero factor is covered by the same rule.
example (m : Fin 2 →₀ ℕ) :
    ((0 : MvPolynomial (Fin 2) ℤ) * qInt).coeff m =
      ∑ i ∈ m.support, (0 : MvPolynomial (Fin 2) ℤ).coeff (Finsupp.single i 1) *
        qInt.coeff (m - Finsupp.single i 1) :=
  (isHomogeneous_zero (Fin 2) ℤ 1).coeff_mul_eq_sum_support qInt m

example (m : Fin 2 →₀ ℕ) :
    (pInt * 0).coeff m =
      ∑ i ∈ m.support, pInt.coeff (Finsupp.single i 1) *
        (0 : MvPolynomial (Fin 2) ℤ).coeff (m - Finsupp.single i 1) :=
  pInt_isHomogeneous.coeff_mul_eq_sum_support 0 m

private theorem unit_single_two_sub_one :
    (Finsupp.single () 2 : Unit →₀ ℕ) - Finsupp.single () 1 = Finsupp.single () 1 := by
  ext
  simp

-- The theorem needs no additive inverses in the coefficient ring.
example :
    ((monomial (Finsupp.single () 1) 2 : MvPolynomial Unit ℕ) *
      monomial (Finsupp.single () 1) 1).coeff (Finsupp.single () 2) = 2 := by
  rw [(isHomogeneous_monomial 2 (by simp)).coeff_mul_eq_sum_support,
    Finsupp.support_single () (by norm_num), Finset.sum_singleton]
  rw [unit_single_two_sub_one]
  norm_num

-- In characteristic two the two mixed-variable contributions cancel.
example :
    ((X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) ^ 2).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 1) = 0 := by
  have hp : (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)).IsHomogeneous 1 :=
    (isHomogeneous_X (ZMod 2) 0).add (isHomogeneous_X (ZMod 2) 1)
  rw [pow_two, hp.coeff_mul_eq_sum_support]
  have hsupp :
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1).support = {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [hsupp]
  simp only [Finset.sum_insert, Finset.mem_singleton, Fin.zero_ne_one, not_false_eq_true,
    Finset.sum_singleton]
  have hsub0 :
      Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 - Finsupp.single 0 1 =
        Finsupp.single 1 1 := by
    ext i
    fin_cases i <;> simp
  have hsub1 :
      Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 - Finsupp.single 1 1 =
        Finsupp.single 0 1 := by
    ext i
    fin_cases i <;> simp
  rw [hsub0, hsub1]
  norm_num [MvPolynomial.coeff_X, single_zero_ne_single_one,
    Ne.symm single_zero_ne_single_one]
  exact ZMod.natCast_self 2

-- With no variables, a degree-one homogeneous polynomial over `ℤ` is zero.
example (p : MvPolynomial Empty ℤ) (hp : p.IsHomogeneous 1) : p = 0 := by
  ext d
  have hd : d = 0 := Subsingleton.elim _ _
  subst d
  simpa using hp.coeff_eq_zero (d := 0) (by norm_num)

-- A nonzero constant is not homogeneous of degree one.
example : ¬(C 1 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := by
  intro h
  have hz := h.coeff_eq_zero (d := 0) (by norm_num)
  norm_num at hz

-- Without homogeneity the displayed formula fails already at the constant monomial.
example :
    ((C 1 : MvPolynomial (Fin 2) ℤ) * C 1).coeff 0 ≠
      ∑ i ∈ (0 : Fin 2 →₀ ℕ).support,
        (C 1 : MvPolynomial (Fin 2) ℤ).coeff (Finsupp.single i 1) *
          (C 1 : MvPolynomial (Fin 2) ℤ).coeff (0 - Finsupp.single i 1) := by
  norm_num

private abbrev SourceVu := MvPolynomial ℕ (LaurentPolynomial ℚ)

private theorem source_hypothesis_iff_isHomogeneous (p : SourceVu) :
    (∀ m, p.coeff m ≠ 0 → m.degree = 1) ↔ p.IsHomogeneous 1 := by
  constructor
  · intro hp d hd
    rw [Finsupp.weight_apply]
    calc
      d.sum (fun i c => c • (1 : ℕ)) = d.sum (fun _ c => c) :=
        Finsupp.sum_congr fun _ _ => by simp
      _ = d.degree := by
        rw [Finsupp.degree_apply]
        rfl
      _ = 1 := hp d hd
  · intro hp d hd
    by_contra hdegree
    exact hd (hp.coeff_eq_zero hdegree)

-- The exact source carrier and coefficient hypothesis recover the source equation.
example (p q : SourceVu) (m : ℕ →₀ ℕ)
    (hp : ∀ d, p.coeff d ≠ 0 → d.degree = 1) :
    (p * q).coeff m =
      ∑ i ∈ m.support, p.coeff (Finsupp.single i 1) *
        q.coeff (m - Finsupp.single i 1) :=
  (source_hypothesis_iff_isHomogeneous p).1 hp |>.coeff_mul_eq_sum_support q m

#print axioms MvPolynomial.IsHomogeneous.coeff_mul_eq_sum_support
