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

universe uR uK uH uS

-- Consumer with the original binders, derived from the stronger
-- statement that drops the unused `f` hypotheses.
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
  Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul
    R K H e he hdiv S πf hπf hkerf β a hβa

-- Higher-universe consumer.
example
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
    ∃ h : H, β = (1 : K) ⊗ₜ[R] h ∧ πf h = a :=
  Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul
    R K H e he hdiv S πf hπf hkerf β a hβa

-- Concrete positive application: with `e = 1` the quotient map is the
-- identity on `ℚ` over `ℤ`, and the theorem recovers the pure tensor.
example : ∃ h : ℚ, ((1 : ℚ) ⊗ₜ[ℤ] (2 : ℚ)) = (1 : ℚ) ⊗ₜ[ℤ] h ∧ h = 2 := by
  obtain ⟨h, hβ, hh⟩ := Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul
    ℤ ℚ ℚ 1 (by simp [IsIdempotentElem])
    (fun d _ y => ⟨0, by simp⟩) ℚ (AlgHom.id ℤ ℚ) Function.surjective_id
    (by ext x; simp) ((1 : ℚ) ⊗ₜ[ℤ] (2 : ℚ)) 2 (by simp)
  exact ⟨h, hβ, hh⟩
