/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.CyclotomicIdealCompl

@[expose] public section

open Polynomial

-- exactSource consumer: the original binders apply verbatim.
open Classical in
example (A : Type) [CommRing A] [IsDomain A] (B : Type) [CommRing B] [Algebra A B]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓA : IsUnit ((ℓ : ℕ) : A)) (hω : ∃ ω : A, IsPrimitiveRoot ω ℓ)
    (ξ : B) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A) = 0)
    (a : A) (ha : a ^ ℓ = 1) (ha1 : a ≠ 1) :
    IsCompl (Ideal.span {ξ - algebraMap A B a})
      (Ideal.span {∏ μ ∈ (primitiveRoots ℓ A).erase a, (ξ - algebraMap A B μ)}) :=
  Ideal.isCompl_span_singleton_sub_algebraMap_of_aeval_cyclotomic_eq_zero A B ℓ hℓA ξ hξ a ha ha1

-- Boundary: the hypothesis that `ξ` is a root of the cyclotomic polynomial matters.
-- With `A = B = ℚ`, `ℓ = 2`, `a = -1` and `ξ = 1` (so `Φ₂(ξ) = 2 ≠ 0`), both principal
-- ideals are the unit ideal, and the unit ideal is not complementary to itself.
open Classical in
example :
    ¬ IsCompl (Ideal.span {(1 : ℚ) - algebraMap ℚ ℚ (-1)})
      (Ideal.span {∏ μ ∈ (primitiveRoots 2 ℚ).erase (-1), ((1 : ℚ) - algebraMap ℚ ℚ μ)}) := by
  have hroots : primitiveRoots 2 ℚ = {-1} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one 0 (by norm_num),
      fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  have hprod : ∏ μ ∈ (primitiveRoots 2 ℚ).erase (-1), ((1 : ℚ) - algebraMap ℚ ℚ μ) = 1 := by
    rw [hroots]
    simp
  rw [hprod]
  have h1 : Ideal.span {(1 : ℚ) - algebraMap ℚ ℚ (-1)} = ⊤ := by
    rw [Ideal.span_singleton_eq_top]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    norm_num
  have h2 : Ideal.span {(1 : ℚ)} = ⊤ := Ideal.span_singleton_one
  rw [h1, h2]
  intro h
  have hbot : (⊤ : Ideal ℚ) = ⊥ := by
    have := h.inf_eq_bot
    simpa using this
  exact (by norm_num : (1 : ℚ) ≠ 0) (by
    have hmem : (1 : ℚ) ∈ (⊥ : Ideal ℚ) := hbot ▸ Submodule.mem_top
    simpa using hmem)
