/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal`
`.lean` and
`P2M/Sol/S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal`
`.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Integral closures of complete DVRs in finite separable extensions

Let `𝒪` be a discrete valuation ring which is complete for its maximal
ideal, and `L'` a finite separable extension of its fraction field.
Then the integral closure of `𝒪` in `L'` is finite over `𝒪`, is a
discrete valuation ring, and is complete for its maximal ideal. The
proof goes through Hensel lifting of idempotents to show the integral
closure is local.
-/

@[expose] public section

open scoped TensorProduct

namespace IntegralClosureDVR

open AdicCompletion IsLocalRing Polynomial

universe u

private theorem isAdicComplete_of_finite_aux {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e1 : M ≃ₗ[R] R ⊗[R] M := (TensorProduct.lid R M).symm
  let e2 : R ⊗[R] M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
     LinearEquiv.rTensor M (AdicCompletion.ofLinearEquiv I R)
  let e3 : AdicCompletion I R ⊗[R] M ≃ₗ[R] AdicCompletion I M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have : (of I M : M → _) = e3 ∘ e2 ∘ e1 := by
    funext x
    simp only [e1, e2, e3, Function.comp_apply, LinearEquiv.restrictScalars_apply,
      ofTensorProductEquivOfFiniteNoetherian_apply, TensorProduct.lid_symm_apply,
      LinearEquiv.rTensor_tmul, ofLinearEquiv_apply, ofTensorProduct_tmul]
    have h1 : (of I R) 1 = 1 := by
      have := (AdicCompletion.algebraMap_apply (S := R) (I := I) (1 : R)).symm
      rw [map_one] at this
      simpa using this
    rw [h1, one_smul]
  rw [this]; exact e3.bijective.comp (e2.bijective.comp e1.bijective)

private theorem isAdicComplete_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (of I N : N → _) = (AdicCompletion.congr I e) ∘ (of I M) ∘ e.symm := by
    funext x
    simp [AdicCompletion.congr_apply, map_of]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

private theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  haveI : IsAdicComplete I ((Fin n → R) ⧸ LinearMap.ker p) := isAdicComplete_of_finite_aux I _
  exact isAdicComplete_of_linearEquiv I (p.quotKerEquivOfSurjective hp)

private theorem isAdicComplete_of_pow_le_of_le {R : Type*} [CommRing R] {I J : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    {k : ℕ} (hJI : J ^ k ≤ I) (hIJ : I ≤ J) : IsAdicComplete J M := by
  have hpow : ∀ n : ℕ, (J ^ ((k + 1) * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
    intro n
    apply Submodule.smul_mono_left
    rw [pow_mul]
    exact Ideal.pow_right_mono (le_trans (Ideal.pow_le_pow_right (Nat.le_succ k)) hJI) n
  have hpow' : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff J M := by
    constructor
    intro x hx
    refine IsHausdorff.haus (I := I) inferInstance x fun n => ?_
    exact (hx ((k + 1) * n)).mono (hpow n)
  have hP : IsPrecomplete J M := by
    constructor
    intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
      (f := fun n => f ((k + 1) * n)) fun {m n} hmn =>
        (hf (Nat.mul_le_mul_left (k + 1) hmn)).mono (hpow m)
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f ((k + 1) * n) [SMOD (J ^ n • ⊤ : Submodule R M)] :=
      hf (by nlinarith)
    exact h1.trans ((hL n).mono (hpow' n))
  exact ⟨⟩

private theorem trivial_idem_quot {B : Type*} [CommRing B] (J : Ideal B) [HenselianRing B J]
    (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∀ e : B ⧸ J, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  set f : B[X] := X ^ 2 - X with hf
  have hmonic : f.Monic := by
    rw [hf]
    exact Polynomial.monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  have hbJ : b * b - b ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
    exact sub_eq_zero.mpr he.eq
  have heval : f.eval b ∈ J := by
    simpa [hf, sq] using hbJ
  have hder : IsUnit (Ideal.Quotient.mk J (f.derivative.eval b)) := by
    have hd : f.derivative.eval b = 2 * b - 1 := by
      simp [hf]; ring
    rw [hd]
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * b - 1)) ?_
    rw [← map_mul, ← (Ideal.Quotient.mk J).map_one, Ideal.Quotient.eq]
    have : (2 * b - 1) * (2 * b - 1) - 1 = 4 * (b * b - b) := by ring
    rw [this]
    exact J.mul_mem_left _ hbJ
  obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian f hmonic b heval hder
  have haid : IsIdempotentElem a := by
    have : a ^ 2 - a = 0 := by simpa [hf] using ha
    rw [IsIdempotentElem, ← sq]
    exact sub_eq_zero.mp this
  have hba : Ideal.Quotient.mk J b = Ideal.Quotient.mk J a := by
    rw [eq_comm, Ideal.Quotient.eq]; exact hab
  rcases hB a haid with h | h
  · left; rw [hba, h, _root_.map_zero]
  · right; rw [hba, h, _root_.map_one]

private theorem isUnit_or_isUnit_one_sub {A : Type*} [CommRing A] [IsArtinianRing A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) (a : A) :
    IsUnit a ∨ IsUnit (1 - a) := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, mul_one] at hy
  have key : ∀ k : ℕ, a ^ n = a ^ (n + k) * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a ^ n = a ^ (n + k) * y ^ k := ih
        _ = a ^ k * a ^ n * y ^ k := by ring
        _ = a ^ k * (a ^ (n + 1) * y) * y ^ k := by rw [hy]
        _ = a ^ (n + (k + 1)) * y ^ (k + 1) := by ring
  set e := a ^ n * y ^ n with he
  have hidem : IsIdempotentElem e := by
    change e * e = e
    calc e * e = (a ^ (n + n) * y ^ n) * y ^ n := by rw [he]; ring
      _ = a ^ n * y ^ n := by rw [← key n]
  rcases hA e hidem with h0 | h1
  · right
    have hn : a ^ n = 0 := by
      calc a ^ n = a ^ (n + n) * y ^ n := key n
        _ = a ^ n * e := by rw [he]; ring
        _ = 0 := by rw [h0, mul_zero]
    exact (IsNilpotent.isUnit_one_sub ⟨n, hn⟩)
  · left
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [pow_one, pow_zero] at hy
      exact IsUnit.of_mul_eq_one _ hy
    · apply isUnit_of_dvd_one
      rw [← h1, he]
      exact Dvd.dvd.mul_right (dvd_pow_self a hn.ne') _

private theorem isLocalRing_of_henselian {B : Type*} [CommRing B] [Nontrivial B] (J : Ideal B)
    [HenselianRing B J] [IsArtinianRing (B ⧸ J)]
    (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  have hJ := trivial_idem_quot J hB
  haveI := isLocalHom_of_le_jacobson_bot J (HenselianRing.jac)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  rcases isUnit_or_isUnit_one_sub hJ (Ideal.Quotient.mk J b) with h | h
  · exact Or.inl (IsUnit.of_map (Ideal.Quotient.mk J) b h)
  · refine Or.inr (IsUnit.of_map (Ideal.Quotient.mk J) (1 - b) ?_)
    simpa using h

section Main

variable (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (L : Type*) [Field L] [Algebra 𝒪 L] [IsFractionRing 𝒪 L]
    (L' : Type*) [Field L'] [Algebra 𝒪 L'] [Algebra L L'] [IsScalarTower 𝒪 L L']

include L in
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem algebraMap_injective :
    Function.Injective (algebraMap 𝒪 (integralClosure 𝒪 L')) := by
  have h : Function.Injective (algebraMap 𝒪 L') := by
    rw [IsScalarTower.algebraMap_eq 𝒪 L L']
    exact (algebraMap L L').injective.comp (IsFractionRing.injective 𝒪 L)
  rw [IsScalarTower.algebraMap_eq 𝒪 (integralClosure 𝒪 L') L', RingHom.coe_comp] at h
  exact Function.Injective.of_comp h

include L in
private theorem not_isField : ¬ IsField (integralClosure 𝒪 L') := by
  rw [← Algebra.IsIntegral.isField_iff_isField (algebraMap_injective 𝒪 L L')]
  exact IsDiscreteValuationRing.not_isField 𝒪

private theorem isArtinianRing_quotient [Module.Finite 𝒪 (integralClosure 𝒪 L')] :
    IsArtinianRing (integralClosure 𝒪 L' ⧸
      (maximalIdeal 𝒪).map (algebraMap 𝒪 (integralClosure 𝒪 L'))) := by
  letI : Field (𝒪 ⧸ maximalIdeal 𝒪) := Ideal.Quotient.field _
  have : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (integralClosure 𝒪 L' ⧸
      (maximalIdeal 𝒪).map (algebraMap 𝒪 (integralClosure 𝒪 L'))) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  exact IsArtinianRing.of_finite (𝒪 ⧸ maximalIdeal 𝒪) _

end Main

end IntegralClosureDVR

open IntegralClosureDVR IsLocalRing in
/-- The integral closure of a complete discrete valuation ring in a finite
separable extension of its fraction field is finite over the base, is a
discrete valuation ring, and is complete for its maximal ideal. -/
theorem integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (L : Type*) [Field L] [Algebra 𝒪 L] [IsFractionRing 𝒪 L]
    (L' : Type*) [Field L'] [Algebra 𝒪 L'] [Algebra L L'] [IsScalarTower 𝒪 L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L'] :
    Module.Finite 𝒪 (integralClosure 𝒪 L') ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L'),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L'))
        (integralClosure 𝒪 L') := by
  haveI hfin : Module.Finite 𝒪 (integralClosure 𝒪 L') := IsIntegralClosure.finite 𝒪 L L' _
  haveI hD : IsDedekindDomain (integralClosure 𝒪 L') :=
    IsIntegralClosure.isDedekindDomain 𝒪 L L' _
  set J : Ideal (integralClosure 𝒪 L') :=
    (maximalIdeal 𝒪).map (algebraMap 𝒪 (integralClosure 𝒪 L')) with hJdef
  haveI hJ : IsAdicComplete J (integralClosure 𝒪 L') :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal 𝒪) (integralClosure 𝒪 L')).mpr
      (isAdicComplete_of_finite (maximalIdeal 𝒪) (integralClosure 𝒪 L'))
  haveI : IsArtinianRing (integralClosure 𝒪 L' ⧸ J) := isArtinianRing_quotient 𝒪 L'
  haveI hloc : IsLocalRing (integralClosure 𝒪 L') :=
    isLocalRing_of_henselian J fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he
  haveI hdvr : IsDiscreteValuationRing (integralClosure 𝒪 L') :=
    ((IsDiscreteValuationRing.TFAE (integralClosure 𝒪 L') (not_isField 𝒪 L L')).out 3 1).mp hD
  refine ⟨hfin, hdvr, ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  have hJle : J ≤ maximalIdeal (integralClosure 𝒪 L') := by
    rw [← jacobson_eq_maximalIdeal (⊥ : Ideal (integralClosure 𝒪 L')) bot_ne_top]
    exact IsAdicComplete.le_jacobson_bot J
  exact isAdicComplete_of_pow_le_of_le hn hJle
