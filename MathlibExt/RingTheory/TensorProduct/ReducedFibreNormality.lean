/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre.lean`
and
`P2M/Sol/S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre.lean`
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

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.ScaleRoots

@[expose] public section

open scoped TensorProduct
open Polynomial

private theorem pow_natDegree_mem_of_aeval_scaleRoots_eq_zero_aux {B : Type*} [CommRing B]
    {p : B[X]} (hp : p.Monic) {s b : B} (I : Ideal B) (hs : s ∈ I)
    (h : aeval b (p.scaleRoots s) = 0) : b ^ p.natDegree ∈ I := by
  have hsum : aeval b (p.scaleRoots s) =
      ∑ i ∈ Finset.range ((p.scaleRoots s).natDegree + 1), (p.scaleRoots s).coeff i * b ^ i := by
    rw [aeval_def, eval₂_eq_sum_range]
    rfl
  rw [h, natDegree_scaleRoots, Finset.sum_range_succ, coeff_scaleRoots, Nat.sub_self, pow_zero,
    mul_one, hp.coeff_natDegree, one_mul] at hsum
  have hrest : (∑ i ∈ Finset.range p.natDegree, (p.scaleRoots s).coeff i * b ^ i) ∈ I := by
    refine sum_mem fun i hi => ?_
    rw [Finset.mem_range] at hi
    refine Ideal.mul_mem_right _ _ ?_
    rw [coeff_scaleRoots]
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_mem_of_mem I hs (p.natDegree - i) (by omega)
  have hb : b ^ p.natDegree =
      -(∑ i ∈ Finset.range p.natDegree, (p.scaleRoots s).coeff i * b ^ i) :=
    eq_neg_of_add_eq_zero_right hsum.symm
  rw [hb]
  exact I.neg_mem_iff.mpr hrest

private theorem mem_span_of_isIntegral_mk_aux {B : Type*} [CommRing B] (ϖ : B)
    [IsReduced (B ⧸ Ideal.span {ϖ})]
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization.Away ϖ L]
    (hinj : Function.Injective (algebraMap B L))
    (m : ℕ) (b : B)
    (hz : IsIntegral B (IsLocalization.mk' L b (⟨ϖ ^ (m + 1), m + 1, rfl⟩ :
      Submonoid.powers ϖ))) :
    b ∈ Ideal.span {ϖ} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have h1 := scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero hpz
  rw [aeval_algebraMap_apply L b, map_eq_zero_iff _ hinj] at h1
  have hbn : b ^ p.natDegree ∈ Ideal.span {ϖ} :=
    pow_natDegree_mem_of_aeval_scaleRoots_eq_zero_aux hp (Ideal.span {ϖ})
      (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton ϖ)) (m + 1)
        (Nat.succ_pos m)) h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsReduced.eq_zero
  refine ⟨p.natDegree, ?_⟩
  have := (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {ϖ})).mpr hbn
  simpa only [map_pow] using this

private theorem isIntegrallyClosedIn_of_isReduced_quotient_span_singleton_aux
    {B : Type*} [CommRing B] (ϖ : B) (hϖ : ϖ ∈ nonZeroDivisors B)
    [IsReduced (B ⧸ Ideal.span {ϖ})]
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization.Away ϖ L] :
    IsIntegrallyClosedIn B L := by
  have hle : Submonoid.powers ϖ ≤ nonZeroDivisors B := (Submonoid.powers_le).mpr hϖ
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L hle
  rw [isIntegrallyClosedIn_iff]
  refine ⟨hinj, ?_⟩
  suffices key : ∀ (m : ℕ) (b : B),
      IsIntegral B (IsLocalization.mk' L b (⟨ϖ ^ m, m, rfl⟩ : Submonoid.powers ϖ)) →
      ∃ y, algebraMap B L y = IsLocalization.mk' L b (⟨ϖ ^ m, m, rfl⟩ : Submonoid.powers ϖ) by
    intro z hz
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ϖ) z
    obtain ⟨_, m, rfl⟩ := s
    exact key m b hz
  intro m
  induction m with
  | zero =>
    intro b _
    refine ⟨b, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    simp
  | succ m ih =>
    intro b hz
    have hb : b ∈ Ideal.span {ϖ} := mem_span_of_isIntegral_mk_aux ϖ L hinj m b hz
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have heq : IsLocalization.mk' L (b' * ϖ) (⟨ϖ ^ (m + 1), m + 1, rfl⟩ :
        Submonoid.powers ϖ) =
        IsLocalization.mk' L b' (⟨ϖ ^ m, m, rfl⟩ : Submonoid.powers ϖ) := by
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      simp only [pow_succ]
      ring
    rw [heq] at hz ⊢
    exact ih b' hz

private theorem isIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization_aux
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by
  let K := FractionRing C
  have hg : ∀ y : M, IsUnit (algebraMap C K y) := fun y =>
    isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective C K)).mpr (nonZeroDivisors.ne_zero (hM y.2)))
  letI algLK : Algebra L K := (IsLocalization.lift (M := M) (S := L) hg).toAlgebra
  haveI : IsScalarTower C L K :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := L) (A := K)
      (IsLocalization.lift_comp (M := M) hg).symm
  haveI : IsFractionRing L K := IsFractionRing.isFractionRing_of_isLocalization M L K hM
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ?_
  have hxL : IsIntegral L x := hx.tower_top
  obtain ⟨l, rfl⟩ := (isIntegrallyClosed_iff K).mp inferInstance hxL
  have hl : IsIntegral C l :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom C L K) (IsFractionRing.injective L K)).mp hx
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hl
  exact ⟨c, IsScalarTower.algebraMap_apply C L K c⟩

universe u

/-- A flat tensor product is a domain and integrally closed when its generic
localization is, and its special fibre at a nonzerodivisor is reduced.

Let `B` be a flat `R`-algebra, `ϖ` a nonzerodivisor of an `R`-algebra `R'`,
`K'` the localization of `R'` away from `ϖ`, and `k'` an `R'`-algebra whose
structure map is surjective with kernel `(ϖ)`. If `K' ⊗[R] B` is a domain
and integrally closed and `k' ⊗[R] B` is reduced, then `R' ⊗[R] B` is a
domain and integrally closed. -/
public theorem Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre
    {R B R' K' k' : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] B)] [IsIntegrallyClosed (K' ⊗[R] B)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') =
      Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] B)) :
    IsDomain (R' ⊗[R] B) ∧ IsIntegrallyClosed (R' ⊗[R] B) := by
  classical
  let f₀ : R' →ₐ[R] K' := IsScalarTower.toAlgHom R R' K'
  let φ : R' ⊗[R] B →ₐ[R] K' ⊗[R] B := Algebra.TensorProduct.map f₀ (AlgHom.id R B)
  have hinjRK : Function.Injective (algebraMap R' K') :=
    IsLocalization.injective K' (Submonoid.powers_le.mpr hϖ)
  have hφ : Function.Injective φ := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) f₀.toLinearMap hinjRK
    have h2 : ∀ x, φ x = LinearMap.rTensor B f₀.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a b => simp [φ]
      | add x y hx hy => simp only [map_add, hx, hy]
    intro x y hxy
    apply h1
    rw [← h2, ← h2, hxy]
  haveI hdom : IsDomain (R' ⊗[R] B) := Function.Injective.isDomain φ.toRingHom hφ
  set ϖC : R' ⊗[R] B := algebraMap R' (R' ⊗[R] B) ϖ with hϖCdef
  have hφϖ : φ ϖC = algebraMap K' (K' ⊗[R] B) (algebraMap R' K' ϖ) := by
    rw [hϖCdef, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp [φ, f₀]
  have hunit : IsUnit (φ ϖC) := by
    rw [hφϖ]
    exact (IsLocalization.Away.algebraMap_isUnit ϖ).map _
  have hϖC : ϖC ∈ nonZeroDivisors (R' ⊗[R] B) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply hunit.ne_zero
    rw [h0, map_zero]
  letI algCL : Algebra (R' ⊗[R] B) (K' ⊗[R] B) := φ.toRingHom.toAlgebra
  have halgCL : ∀ x, algebraMap (R' ⊗[R] B) (K' ⊗[R] B) x = φ x := fun _ => rfl
  haveI : IsLocalization.Away ϖC (K' ⊗[R] B) := by
    rw [IsLocalization.Away, isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      rw [halgCL, map_pow]
      exact hunit.pow n
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp [halgCL]⟩
      | tmul κ b =>
        obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers ϖ) κ
        refine ⟨(r ⊗ₜ b, ⟨ϖC ^ n, n, rfl⟩), ?_⟩
        simp only [halgCL]
        rw [map_pow, hφϖ]
        simp only [φ, f₀, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          ← map_pow]
        dsimp only at hr
        rw [hr]
      | add x y hx hy =>
        obtain ⟨⟨x₁, ⟨_, n₁, rfl⟩⟩, h₁⟩ := hx
        obtain ⟨⟨y₁, ⟨_, n₂, rfl⟩⟩, h₂⟩ := hy
        refine ⟨(x₁ * ϖC ^ n₂ + y₁ * ϖC ^ n₁, ⟨ϖC ^ (n₁ + n₂), n₁ + n₂, rfl⟩), ?_⟩
        simp only [halgCL, map_add, map_mul, map_pow] at h₁ h₂ ⊢
        rw [pow_add]
        calc (x + y) * (φ ϖC ^ n₁ * φ ϖC ^ n₂)
            = x * φ ϖC ^ n₁ * φ ϖC ^ n₂ + y * φ ϖC ^ n₂ * φ ϖC ^ n₁ := by ring
          _ = φ x₁ * φ ϖC ^ n₂ + φ y₁ * φ ϖC ^ n₁ := by rw [h₁, h₂]
    · intro x y hxy
      exact ⟨1, by rw [hφ hxy]⟩
  have hI : (Ideal.span {ϖ}).map (algebraMap R' (R' ⊗[R] B)) = Ideal.span {ϖC} := by
    rw [Ideal.map_span, Set.image_singleton]
  let e2 : (R' ⧸ Ideal.span {ϖ}) ⊗[R'] (R' ⊗[R] B) ≃ₐ[R']
      (R' ⊗[R] B) ⧸ (Ideal.span {ϖ}).map (algebraMap R' (R' ⊗[R] B)) :=
    (Algebra.TensorProduct.comm R' _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R' ⊗[R] B)
        (Ideal.span {ϖ})).symm.restrictScalars R')
  have e3 := Algebra.TensorProduct.cancelBaseChange R R' R' (R' ⧸ Ideal.span {ϖ}) B
  let g₀ : R' →ₐ[R] k' := IsScalarTower.toAlgHom R R' k'
  have hg₀ : Function.Surjective g₀ := hk
  have hkerg : RingHom.ker g₀ = Ideal.span {ϖ} := hker
  let eI : (R' ⧸ Ideal.span {ϖ}) ≃ₐ[R] k' :=
    (Ideal.quotientEquivAlgOfEq R hkerg.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hg₀)
  have e4 := Algebra.TensorProduct.congr eI (AlgEquiv.refl (R := R) (A₁ := B))
  have e1 := Ideal.quotEquivOfEq hI.symm
  have etot := e1.trans (e2.symm.toRingEquiv.trans (e3.toRingEquiv.trans e4.toRingEquiv))
  haveI : IsReduced (k' ⊗[R] B) := hred
  haveI : IsReduced ((R' ⊗[R] B) ⧸ Ideal.span {ϖC}) :=
    isReduced_of_injective etot etot.injective
  haveI : IsIntegrallyClosedIn (R' ⊗[R] B) (K' ⊗[R] B) :=
    isIntegrallyClosedIn_of_isReduced_quotient_span_singleton_aux ϖC hϖC (K' ⊗[R] B)
  have hle : Submonoid.powers ϖC ≤ nonZeroDivisors (R' ⊗[R] B) := Submonoid.powers_le.mpr hϖC
  exact ⟨hdom, isIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization_aux
    (Submonoid.powers ϖC) hle (K' ⊗[R] B)⟩
