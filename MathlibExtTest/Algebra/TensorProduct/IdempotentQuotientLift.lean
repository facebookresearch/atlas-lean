/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.TensorProduct.IdempotentQuotientLift

@[expose] public section

open scoped TensorProduct

-- Consumer with the original binders.
example
    (R : Type) [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (H : Type) [CommRing H] [Algebra R H]
    (e f : H) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hfe : f * e = e)
    (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e))
    (S : Type) [CommRing S] [Algebra R S]
    (πf : H →ₐ[R] S) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e})
    (β : K ⊗[R] H) (hβf : β * ((1 : K) ⊗ₜ[R] f) = β)
    (a : S) (hβa : Algebra.TensorProduct.map (AlgHom.id K K) πf β = (1 : K) ⊗ₜ[R] a) :
    ∃ h : H, β = (1 : K) ⊗ₜ[R] h ∧ πf h = a :=
  Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq
    R K H e f he hf hfe hdiv S πf hπf hkerf β hβf a hβa

-- The kernel hypothesis matters: if `πf (1 - e) ≠ 0`, the descended
-- projection need not exist; here `1 - e` itself witnesses that the
-- span condition cannot be dropped for the identity map on `ℤ × ℤ`
-- with `e = (1, 0)`, since `1 - e = (0, 1) ≠ 0` is not in the kernel.
example : (1 - (1, 0) : ℤ × ℤ) ≠ 0 := by decide
