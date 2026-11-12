/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact source-type consumer below restates the theorem cited in
MathlibExt/RingTheory/Nullstellensatz/PointAvoidance.lean, from
https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE credits the respective Mathlib authors under Apache 2.0.
-/

import MathlibExt.RingTheory.Nullstellensatz.PointAvoidance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PointAvoidanceTest

/-- The complete frozen source type, including all universes and assumptions. -/
theorem exact_source
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B]
    {ι : Type*} [Finite ι] (g : ι → B) (hg : ∀ i, g i ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 :=
  Algebra.exists_algHom_forall_ne_zero (k := k) g hg

/-- One specialization preserves all the given nonzero determinants. -/
theorem simultaneous_determinants
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] {ι n : Type*} [Finite ι]
    [Fintype n] [DecidableEq n] (M : ι → Matrix n n B)
    (hM : ∀ i, (M i).det ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, ((M i).map χ).det ≠ 0 := by
  obtain ⟨χ, hχ⟩ := Algebra.exists_algHom_forall_ne_zero (k := k)
    (fun i ↦ (M i).det) hM
  exact ⟨χ, fun i ↦ (χ.map_det (M i)) ▸ hχ i⟩

/-- An integral affine closed set has a point outside any finite list of
proper principal closed conditions. This is not restricted to characteristic
zero, and the coordinate algebra is a quotient rather than a field. -/
theorem affine_closed_conditions
    {k : Type*} [Field k] [IsAlgClosed k] {σ ι : Type*}
    [Finite σ] [Finite ι] (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (g : ι → MvPolynomial σ k) (hg : ∀ i, g i ∉ I) :
    ∃ x : σ → k, (∀ f ∈ I, MvPolynomial.aeval x f = 0) ∧
      ∀ i, MvPolynomial.aeval x (g i) ≠ 0 := by
  obtain ⟨χ, hχ⟩ := Algebra.exists_algHom_forall_ne_zero (k := k)
    (fun i ↦ Ideal.Quotient.mk I (g i))
    (fun i ↦ by simpa only [Ne, Ideal.Quotient.eq_zero_iff_mem] using hg i)
  let ψ := χ.comp (Ideal.Quotient.mkₐ k I)
  refine ⟨ψ ∘ MvPolynomial.X, ?_, ?_⟩
  · intro f hf
    rw [← MvPolynomial.aeval_unique ψ]
    change χ (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  · intro i
    rw [← MvPolynomial.aeval_unique ψ]
    exact hχ i

/-- Concrete polynomials `X` and `X - 1` are simultaneously nonzero over any
algebraically closed field, including in characteristic two. -/
theorem avoid_zero_and_one {k : Type*} [Field k] [IsAlgClosed k] :
    ∃ x : k, x ≠ 0 ∧ x - 1 ≠ 0 := by
  let g : Bool → Polynomial k := fun b ↦
    if b then Polynomial.X else Polynomial.X - 1
  have hg : ∀ b, g b ≠ 0 := by
    intro b
    cases b
    · intro h
      have := congrArg (fun p : Polynomial k ↦ p.coeff 1) h
      simp [g, Polynomial.coeff_one] at this
    · exact Polynomial.X_ne_zero
  obtain ⟨χ, hχ⟩ := Algebra.exists_algHom_forall_ne_zero (k := k) g hg
  refine ⟨χ Polynomial.X, ?_, ?_⟩
  · simpa [g] using hχ true
  · simpa [g] using hχ false

/-- Empty families still produce a point of an arbitrary finite-type domain. -/
theorem empty_family
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] : Nonempty (B →ₐ[k] k) := by
  obtain ⟨χ, _⟩ := Algebra.exists_algHom_forall_ne_zero (k := k)
    (fun i : Fin 0 ↦ Fin.elim0 i : Fin 0 → B) (fun i ↦ Fin.elim0 i)
  exact ⟨χ⟩

/-- A zero function cannot be avoided. -/
theorem cannot_avoid_zero {k B : Type*} [Field k] [CommRing B]
    [Algebra k B] : ¬ ∃ χ : B →ₐ[k] k, χ 0 ≠ 0 := by
  simp

/-- Both orthogonal idempotents are nonzero, but no field-valued point of
`k × k` can avoid both. Reducedness alone does not replace the domain premise. -/
theorem product_ring_boundary {k : Type*} [Field k] :
    ((1, 0) : k × k) ≠ 0 ∧ ((0, 1) : k × k) ≠ 0 ∧
      ¬ ∃ χ : (k × k) →ₐ[k] k, χ (1, 0) ≠ 0 ∧ χ (0, 1) ≠ 0 := by
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨χ, h₁, h₂⟩
  apply mul_ne_zero h₁ h₂
  rw [← map_mul]
  have hzero : ((1, 0) * (0, 1) : k × k) = 0 := by ext <;> simp
  rw [hzero, map_zero]

end PointAvoidanceTest
