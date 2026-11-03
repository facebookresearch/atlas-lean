/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: generalized the base algebra and exponent monoid, renamed the API,
used Mathlib's support lemma, and added simplification laws and importing-client tests.
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.Derivation.Basic

/-! # Coefficientwise derivations of Hahn series

A derivation of the coefficient algebra extends to Hahn series by acting on every coefficient.
The resulting operator satisfies the Leibniz rule and preserves commutation of derivations.
It does not differentiate the exponent variable.

Adapted from `eth/proof/rates/GeneralPieces/GenF/Hahn.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
The source treats commutative ℚ-algebras and integer exponents; this module also permits other
commutative base rings and ordered cancellative additive monoids of exponents.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace HahnSeries

variable {Γ R A : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R] [CommRing A] [Algebra R A]

/-- Apply a coefficient derivation to a Hahn series as an `R`-linear operator. -/
noncomputable def coefficientLinearMap (d : Derivation R A A) :
    HahnSeries Γ A →ₗ[R] HahnSeries Γ A where
  toFun f := f.map d
  map_add' f g := by
    ext y
    simp
  map_smul' q f := by
    ext y
    simp

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The coefficient formula for the linear operator underlying the lifted derivation. -/
@[simp] theorem coeff_coefficientLinearMap (d : Derivation R A A)
    (f : HahnSeries Γ A) (y : Γ) :
    (coefficientLinearMap d f).coeff y = d (f.coeff y) := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Acting on coefficients cannot introduce new exponents into the support. -/
theorem support_coefficientLinearMap (d : Derivation R A A)
    (f : HahnSeries Γ A) : (coefficientLinearMap d f).support ⊆ f.support :=
  support_map_subset f ⟨d, map_zero d⟩

/-- Extend a derivation of the coefficient algebra by applying it to each coefficient. -/
noncomputable def coefficientDerivation (d : Derivation R A A) :
    Derivation R (HahnSeries Γ A) (HahnSeries Γ A) :=
  Derivation.mk' (coefficientLinearMap d) fun f g => by
    ext y
    rw [coeff_coefficientLinearMap, smul_eq_mul, smul_eq_mul, coeff_add, mul_comm g,
      coeff_mul, coeff_mul_right' g.isPWO_support (support_coefficientLinearMap d g),
      coeff_mul_left' f.isPWO_support (support_coefficientLinearMap d f), map_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, coeff_coefficientLinearMap,
      coeff_coefficientLinearMap, mul_comm (g.coeff p.2)]

/-- The coefficient of the lifted derivation is the derivative of that coefficient. -/
@[simp] theorem coeff_coefficientDerivation (d : Derivation R A A)
    (f : HahnSeries Γ A) (y : Γ) :
    (coefficientDerivation d f).coeff y = d (f.coeff y) := rfl

/-- The lift of the zero derivation is zero. -/
@[simp] theorem coefficientDerivation_zero :
    coefficientDerivation (Γ := Γ) (0 : Derivation R A A) = 0 := by
  ext f y
  simp

/-- A one-term series keeps its exponent and differentiates its coefficient. -/
@[simp] theorem coefficientDerivation_single (d : Derivation R A A) (y : Γ) (a : A) :
    coefficientDerivation d (single y a) = single y (d a) := by
  ext z
  rw [coeff_coefficientDerivation]
  by_cases h : z = y
  · rw [h, coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne h, coeff_single_of_ne h, map_zero]

/-- On a constant series, the lift acts on its constant coefficient. -/
@[simp] theorem coefficientDerivation_C (d : Derivation R A A) (a : A) :
    coefficientDerivation (Γ := Γ) d (HahnSeries.C a) = HahnSeries.C (d a) :=
  coefficientDerivation_single d 0 a

/-- Commuting coefficient derivations lift to commuting derivations of Hahn series. -/
theorem coefficientDerivation_commute {d d' : Derivation R A A}
    (h : Function.Commute d d') :
    Function.Commute (coefficientDerivation (Γ := Γ) d) (coefficientDerivation d') := by
  intro f
  ext y
  simpa using h (f.coeff y)

end HahnSeries
