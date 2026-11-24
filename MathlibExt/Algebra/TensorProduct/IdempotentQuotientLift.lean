/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq.lean`
and
`P2M/Sol/S_Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq.lean`
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

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct

universe uR uK uH uS

namespace TensorProductIdempotentQuotientAux

variable {R : Type uR} [CommRing R] [IsDomain R] {K : Type uK} [Field K] [Algebra R K]
  [IsFractionRing R K] {H : Type uH} [CommRing H] [Algebra R H]

private theorem exists_mul_one_tmul_eq (e : H)
    (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e))
    (γ : K ⊗[R] H) :
    ∃ m : H, γ * ((1 : K) ⊗ₜ[R] (1 - e)) = (1 : K) ⊗ₜ[R] (m * (1 - e)) := by
  induction γ using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [zero_mul, zero_mul, TensorProduct.tmul_zero]⟩
  | add x y hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    exact ⟨m₁ + m₂, by rw [add_mul, h₁, h₂, add_mul, TensorProduct.tmul_add]⟩
  | tmul k y =>
    obtain ⟨r, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap R K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    obtain ⟨z, hz⟩ := hdiv d hd0 (r • y)
    refine ⟨z, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hk : algebraMap R K r / algebraMap R K d = r • (algebraMap R K d)⁻¹ := by
      rw [div_eq_inv_mul, Algebra.smul_def, mul_comm]
    rw [hk, TensorProduct.smul_tmul, ← smul_mul_assoc, ← hz, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_inv_cancel₀ hdK]

/-- The linear projection onto the `e`-component, descended along `πf`.
Its value on `πf h` is `h * e`; it is a linear map, not a ring section. -/
private theorem exists_linear_projection (e : H) (he : IsIdempotentElem e)
    {S : Type uS} [CommRing S] [Algebra R S]
    (πf : H →ₐ[R] S) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e}) :
    ∃ σ : S →ₗ[R] H, ∀ h : H, σ (πf h) = h * e := by
  let μ : H →ₗ[R] H := LinearMap.mulRight R e
  have hμ : LinearMap.ker πf.toLinearMap ≤ LinearMap.ker μ := by
    intro h hh
    rw [LinearMap.mem_ker] at hh ⊢
    change h * e = 0
    have hh' : h ∈ RingHom.ker πf := hh
    rw [hkerf, Ideal.mem_span_singleton] at hh'
    obtain ⟨x, rfl⟩ := hh'
    rw [mul_assoc, mul_comm x e, ← mul_assoc, sub_mul, one_mul, he.eq, sub_self, zero_mul]
  let μ' := (LinearMap.ker πf.toLinearMap).liftQ μ hμ
  have hπf' : Function.Surjective πf.toLinearMap := hπf
  refine ⟨μ'.comp (πf.toLinearMap.quotKerEquivOfSurjective hπf').symm.toLinearMap,
    fun h => ?_⟩
  change μ' ((πf.toLinearMap.quotKerEquivOfSurjective hπf').symm (πf.toLinearMap h)) =
    h * e
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem baseChange_projection_map (e : H) {S : Type uS} [CommRing S]
    [Algebra R S]
    (πf : H →ₐ[R] S) (σ : S →ₗ[R] H) (hσ : ∀ h : H, σ (πf h) = h * e)
    (γ : K ⊗[R] H) :
    σ.baseChange K (Algebra.TensorProduct.map (AlgHom.id K K) πf γ) =
      γ * ((1 : K) ⊗ₜ[R] e) := by
  induction γ using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, zero_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_mul]
  | tmul k h =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.baseChange_tmul, hσ,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

end TensorProductIdempotentQuotientAux

/-- An element of `K ⊗[R] H` mapping to a pure tensor `1 ⊗ₜ a` under a
surjective algebra map whose kernel is spanned by `1 - e`, for an
idempotent `e`, is itself a pure tensor `1 ⊗ₜ h` with `πf h = a`,
provided denominators can be cleared on the `1 - e` component. -/
public theorem Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul
    (R : Type uR) [CommRing R] [IsDomain R] (K : Type uK) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (H : Type uH) [CommRing H] [Algebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e))
    (S : Type uS) [CommRing S] [Algebra R S]
    (πf : H →ₐ[R] S) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e})
    (β : K ⊗[R] H)
    (a : S) (hβa : Algebra.TensorProduct.map (AlgHom.id K K) πf β = (1 : K) ⊗ₜ[R] a) :
    ∃ h : H, β = (1 : K) ⊗ₜ[R] h ∧ πf h = a := by
  obtain ⟨σ, hσ⟩ :=
    TensorProductIdempotentQuotientAux.exists_linear_projection e he πf hπf hkerf
  obtain ⟨h₀, rfl⟩ := hπf a
  obtain ⟨m, hm⟩ :=
    TensorProductIdempotentQuotientAux.exists_mul_one_tmul_eq (K := K) e hdiv β
  have he_part : β * ((1 : K) ⊗ₜ[R] e) = (1 : K) ⊗ₜ[R] (h₀ * e) := by
    rw [← TensorProductIdempotentQuotientAux.baseChange_projection_map (K := K) e πf σ hσ β,
      hβa, LinearMap.baseChange_tmul, hσ]
  have hπe : πf (1 - e) = 0 := by
    rw [← RingHom.mem_ker, hkerf]
    exact Ideal.mem_span_singleton_self _
  have hπe' : πf e = 1 := by
    have h := hπe
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h.symm
  refine ⟨h₀ * e + m * (1 - e), ?_, ?_⟩
  · calc β = β * ((1 : K) ⊗ₜ[R] e) + β * ((1 : K) ⊗ₜ[R] (1 - e)) := by
          rw [← mul_add, ← TensorProduct.tmul_add, add_sub_cancel,
            ← Algebra.TensorProduct.one_def, mul_one]
      _ = (1 : K) ⊗ₜ[R] (h₀ * e + m * (1 - e)) := by
          rw [he_part, hm, TensorProduct.tmul_add]
  · rw [map_add, map_mul, map_mul, hπe, mul_zero, add_zero, hπe', mul_one]
