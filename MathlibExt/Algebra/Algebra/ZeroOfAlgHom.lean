/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_
tensorProduct.lean`
and
`P2M/Sol/S_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_
tensorProduct.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

/-- An element of a torsion-free algebra that vanishes under every algebra
homomorphism into an algebraically closed field is zero, provided the
tensor product with the fraction field is reduced and finite.

This is the Nullstellensatz-style statement that points detect functions:
it is used to show maps of schemes are determined by their values on
geometric points, to pass from vanishing on fibers to vanishing globally,
and to prove reducedness from pointwise vanishing. -/
theorem eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {B : Type u} [CommRing B] [Algebra R B]
    [NoZeroSMulDivisors R B] [IsReduced (TensorProduct R K B)]
    [Module.Finite K (TensorProduct R K B)] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω] (b : B)
    (hb : ∀ φ : B →ₐ[R] Ω, φ b = 0) : b = 0 := by
  classical
  set A := K ⊗[R] B with hA

  have hinj : ∀ b : B, (1 : K) ⊗ₜ[R] b = 0 → b = 0 := by
    intro b hb0
    haveI : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K B 1) :=
      inferInstance
    obtain ⟨⟨s, hs⟩, hsb⟩ :=
      (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R)
        (TensorProduct.mk R K B 1)).mp hb0
    exact (smul_eq_zero.mp hsb).resolve_left (nonZeroDivisors.ne_zero hs)
  apply hinj

  set a : A := (1 : K) ⊗ₜ[R] b with ha
  have hpts : ∀ ψ : A →ₐ[K] Ω, ψ a = 0 := by
    intro ψ
    let φ : B →ₐ[R] Ω := (ψ.restrictScalars R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] A))
    have hφ := hb φ
    change ψ ((Algebra.TensorProduct.includeRight : B →ₐ[R] A) b) = 0 at hφ
    rw [Algebra.TensorProduct.includeRight_apply] at hφ
    exact hφ

  by_contra hne
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := by
    rw [IsArtinianRing.jacobson_eq_radical]
    exact nilradical_eq_zero A
  have hmem : a ∉ (⊥ : Ideal A).jacobson := by rw [hjac]; simpa using hne
  rw [Ideal.jacobson, Submodule.mem_sInf] at hmem
  push Not at hmem
  obtain ⟨𝔪, ⟨-, h𝔪⟩, ha𝔪⟩ := hmem
  haveI hmax : Ideal.IsMaximal 𝔪 := h𝔪

  haveI : IsDomain (A ⧸ 𝔪) := Ideal.Quotient.isDomain 𝔪
  let j : (A ⧸ 𝔪) →ₐ[K] Ω := IsAlgClosed.lift (R := K) (S := A ⧸ 𝔪) (M := Ω)
  have h0 : j (Ideal.Quotient.mk 𝔪 a) = 0 := by
    have hpts' := hpts (j.comp (Ideal.Quotient.mkₐ K 𝔪))
    simpa using hpts'
  have h1 : Ideal.Quotient.mk 𝔪 a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]

  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp h𝔪
  obtain ⟨c, hc⟩ := hfield.mul_inv_cancel h1
  have hmul : j (Ideal.Quotient.mk 𝔪 a) * j c = 1 := by rw [← map_mul, hc, map_one]
  rw [h0, zero_mul] at hmul
  exact zero_ne_one hmul

end Algebra
