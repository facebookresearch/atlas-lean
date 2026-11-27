/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_MvPolynomial_CrossingQuotient.lean`,
`Definitions/Def_MvPolynomial_CrossingResolution.lean`
and
`Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_exists_open_
 pullback_twist_iso_tensorUnit_of_degree_eq_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

noncomputable section

namespace MvPolynomial

variable (W : Type*) [CommRing W]

abbrev CrossingQuotient (t : W) : Type _ :=
  MvPolynomial (Fin 2) W ⧸ Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}

variable {W}

namespace CrossingQuotient

variable (t : W)

abbrev mk : MvPolynomial (Fin 2) W →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.mkₐ W (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)})

theorem mk_apply (p : MvPolynomial (Fin 2) W) :
    mk t p = Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) p := rfl

theorem mk_surjective : Function.Surjective (mk t) := Ideal.Quotient.mkₐ_surjective W _

theorem mk_X_mul_mk_X : mk t (X 0) * mk t (X 1) = algebraMap W (CrossingQuotient W t) t := by
  rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

def monomial (n : ℤ) : CrossingQuotient W t :=
  if 0 ≤ n then mk t (X 0) ^ n.toNat else mk t (X 1) ^ (-n).toNat

theorem monomial_of_nonneg {n : ℤ} (h : 0 ≤ n) : monomial t n = mk t (X 0) ^ n.toNat :=
  ite_eq_left h

theorem monomial_of_neg {n : ℤ} (h : n < 0) :
    monomial t n = mk t (X 1) ^ (-n).toNat := ite_eq_right (not_le.mpr h)

@[simp] theorem monomial_natCast (n : ℕ) : monomial t (n : ℤ) = mk t (X 0) ^ n := by
  rw [monomial_of_nonneg t (Int.natCast_nonneg n), Int.toNat_natCast]

@[simp] theorem monomial_neg_natCast (n : ℕ) : monomial t (-(n : ℤ)) = mk t (X 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, neg_zero, monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero, pow_zero]
  · rw [monomial_of_neg t (by omega), neg_neg, Int.toNat_natCast]

@[simp] theorem monomial_zero : monomial t 0 = 1 := by
  rw [monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero]

def powMap (e : ℕ) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C (t ^ e) : MvPolynomial (Fin 2) W)})
    (aeval fun i : Fin 2 => mk t (X i) ^ e) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, map_sub, map_mul, aeval_X, aeval_X, aeval_C, ← mul_pow, mk_X_mul_mk_X,
        ← map_pow, sub_self,
        mul_zero])

theorem powMap_mk (e : ℕ) (p : MvPolynomial (Fin 2) W) :
    powMap t e (mk (t ^ e) p) = aeval (fun i : Fin 2 => mk t (X i) ^ e) p := rfl

@[simp] theorem powMap_mk_X (e : ℕ) (i : Fin 2) :
    powMap t e (mk (t ^ e) (X i)) = mk t (X i) ^ e := by
  rw [powMap_mk, aeval_X]

end CrossingQuotient

end MvPolynomial

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type*} [CommRing W] (t : W)

abbrev U : CrossingQuotient W t := mk t (X 0)

abbrev V : CrossingQuotient W t := mk t (X 1)

theorem U_mul_V : U t * V t = algebraMap W (CrossingQuotient W t) t := mk_X_mul_mk_X t

theorem aeval_rel_eq_zero {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) :
    aeval ![a, b] (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

def lift {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t) :
    CrossingQuotient W t →ₐ[W] A :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) (aeval ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, aeval_rel_eq_zero t a b h, mul_zero])

theorem lift_mk {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t)
    (p : MvPolynomial (Fin 2) W) : lift t a b h (mk t p) = aeval ![a, b] p := rfl

@[simp] theorem lift_U {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (U t) = a := by
  rw [lift_mk, aeval_X]; rfl

@[simp] theorem lift_V {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (V t) = b := by
  rw [lift_mk, aeval_X]; rfl

def resolutionChart (e : ℕ) (i : Fin e) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  lift (t ^ e) (algebraMap W _ (t ^ (i : ℕ)) * U t) (algebraMap W _ (t ^ (e - 1 - i)) * V t) (by
    have hi : (i : ℕ) + (e - 1 - i) + 1 = e := by have := i.2; omega
    rw [mul_mul_mul_comm, U_mul_V, ← map_mul, ← map_mul, ← pow_add, ← pow_succ, hi])

theorem resolutionChart_U (e : ℕ) (i : Fin e) :
    resolutionChart t e i (U (t ^ e)) = algebraMap W _ (t ^ (i : ℕ)) * U t := lift_U _ _ _ _

theorem resolutionChart_V (e : ℕ) (i : Fin e) :
    resolutionChart t e i (V (t ^ e)) = algebraMap W _ (t ^ (e - 1 - i)) * V t := lift_V _ _ _ _

def transitionUp : CrossingQuotient W t →ₐ[W] Localization.Away (V t) :=
  lift t (IsLocalization.Away.invSelf (V t))
    (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (V t)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V t)),
        IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (V t))])

theorem transitionUp_U :
    transitionUp t (U t) = IsLocalization.Away.invSelf (V t) := lift_U _ _ _ _

theorem transitionUp_V : transitionUp t (V t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (V t)) (V t) :=
  lift_V _ _ _ _

def transitionDown : CrossingQuotient W t →ₐ[W] Localization.Away (U t) :=
  lift t (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (U t))
    (IsLocalization.Away.invSelf (U t)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (U t))])

theorem transitionDown_U : transitionDown t (U t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (U t)) (U t) :=
  lift_U _ _ _ _

theorem transitionDown_V :
    transitionDown t (V t) = IsLocalization.Away.invSelf (U t) := lift_V _ _ _ _

end CrossingQuotient

end MvPolynomial

end
