/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Coprime representatives of ideal classes

A nonzero ideal in a Dedekind domain has a coprime multiplier making it principal. That every ideal
class has an integral representative coprime to any prescribed nonzero ideal is Mathlib's
`ClassGroup.exists_mk0_eq_and_isCoprime`.
-/

@[expose] public section

open Ideal

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

/-- **Making an ideal principal with a factor coprime to a given ideal.** Let $A$ be a
Dedekind domain and let $I$ and $\mathfrak{a}$ be nonzero ideals of $A$. Then there is an
ideal $J$ of $A$ with $J + \mathfrak{a} = A$ such that the product $IJ$ is a principal
ideal. -/
theorem Ideal.exists_isCoprime_mul_isPrincipal (I a : Ideal A) (hI : I ≠ ⊥)
    (ha : a ≠ ⊥) :
    ∃ J : Ideal A, IsCoprime J a ∧ Submodule.IsPrincipal (I * J) := by
  have hle : I * a ≤ I := Ideal.mul_le_left
  have hne : I * a ≠ ⊥ := mul_ne_zero hI ha
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have hx_le : Ideal.span {x} ≤ I := by rw [← hx]; exact le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hx_le
  refine ⟨J, ?_, ?_⟩
  · have h1 : I * (a ⊔ J) = I * ⊤ := by
      rw [Ideal.mul_sup, Ideal.mul_top, ← hJ, hx]
    have h2 : a ⊔ J = ⊤ := mul_left_cancel₀ hI h1
    exact Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm]; exact h2)
  · rw [← hJ]
    exact ⟨⟨x, rfl⟩⟩
