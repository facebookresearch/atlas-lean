/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

namespace MvPolynomial

/-- Apply the operators `1 - ∂ᵢ`, in list order, to a multivariate polynomial. -/
public noncomputable def mixedDifferential {σ R : Type*} [CommRing R]
    (indices : List σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  indices.foldl (fun q i ↦ q - pderiv i q) p

/-- Applying no mixed differential operators leaves a polynomial unchanged. -/
@[simp]
public theorem mixedDifferential_nil {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) : mixedDifferential [] p = p := by
  rfl

/-- The first mixed differential operator can be peeled from the defining list. -/
public theorem mixedDifferential_cons {σ R : Type*} [CommRing R]
    (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    mixedDifferential (i :: is) p = mixedDifferential is (p - pderiv i p) := by
  rfl

/-- The mixed differential operator depends only on the multiset of differentiation indices. -/
public theorem mixedDifferential_eq_of_perm {σ R : Type*} [CommRing R]
    {is js : List σ} (h : is.Perm js) (p : MvPolynomial σ R) :
    mixedDifferential is p = mixedDifferential js p := by
  induction h generalizing p with
  | nil => rfl
  | cons i h ih =>
      rw [mixedDifferential_cons, mixedDifferential_cons]
      exact ih _
  | swap i j is =>
      rw [mixedDifferential_cons, mixedDifferential_cons, mixedDifferential_cons,
        mixedDifferential_cons]
      congr 1
      rw [map_sub, map_sub, pderiv_comm]
      abel
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)

/-- Applying mixed differential operators to an appended list is function composition. -/
public theorem mixedDifferential_append {σ R : Type*} [CommRing R]
    (is js : List σ) (p : MvPolynomial σ R) :
    mixedDifferential (is ++ js) p = mixedDifferential js (mixedDifferential is p) := by
  simp only [mixedDifferential, List.foldl_append]

/-- Partial differentiation commutes with every mixed differential operator. -/
public theorem pderiv_mixedDifferential {σ R : Type*} [CommRing R]
    (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    pderiv i (mixedDifferential is p) = mixedDifferential is (pderiv i p) := by
  induction is generalizing p with
  | nil => rfl
  | cons j js ih =>
      rw [mixedDifferential_cons, mixedDifferential_cons, ih]
      congr 1
      rw [map_sub, pderiv_comm]

end MvPolynomial
