/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import MathlibExt.RingTheory.AdicCompletion.ModuleFinite

/-!
# Cyclotomic discrete valuation rings over a prime maximal ideal

Over a complete discrete valuation ring whose maximal ideal is generated
by a rational prime `q`, adjoining a root of the `q`-th cyclotomic
polynomial gives a complete discrete valuation ring in which `ζ - 1`
generates the maximal ideal and `ζ` is universal for elements whose
`q`-th cyclotomic sum vanishes.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open IsLocalRing Polynomial

namespace CycloDVR


section AdicTransfer

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem smul_top_pow_mul_le {I J : Ideal R} {c : ℕ} (hJI : J ^ c ≤ I) (n : ℕ) :
    (J ^ (c * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ :=
  Submodule.smul_mono_left (by rw [pow_mul]; exact Ideal.pow_right_mono hJI n)

private theorem isHausdorff_of_pow_le {I J : Ideal R} {c : ℕ} (hJI : J ^ c ≤ I)
    [h : IsHausdorff I M] :
    IsHausdorff J M := by
  refine ⟨fun x hx => IsHausdorff.haus h x fun n => ?_⟩
  exact (hx (c * n)).mono (smul_top_pow_mul_le hJI n)

private theorem isPrecomplete_of_pow_le_of_le {I J : Ideal R} {c : ℕ}
    (hJI : J ^ c ≤ I) (hIJ : I ≤ J)
    [h : IsPrecomplete I M] : IsPrecomplete J M := by
  refine ⟨fun f hf => ?_⟩
  have hIJ' : ∀ n, (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h (f := fun k => f (c * k + k)) fun {m n} hmn => by
    have h1 : f (c * m + m) ≡ f (c * n + n) [SMOD (J ^ (c * m + m) • ⊤ : Submodule R M)] :=
      hf (Nat.add_le_add (Nat.mul_le_mul_left c hmn) hmn)
    exact (h1.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right _ _)))).mono
      (smul_top_pow_mul_le hJI m)
  refine ⟨L, fun n => ?_⟩
  have h1 : f n ≡ f (c * n + n) [SMOD (J ^ n • ⊤ : Submodule R M)] := hf (Nat.le_add_left _ _)
  exact h1.trans ((hL n).mono (hIJ' n))

private theorem isAdicComplete_of_pow_le_of_le {I J : Ideal R} {c : ℕ}
    (hJI : J ^ c ≤ I) (hIJ : I ≤ J)
    [IsAdicComplete I M] : IsAdicComplete J M :=
  { toIsHausdorff := isHausdorff_of_pow_le hJI
    toIsPrecomplete := isPrecomplete_of_pow_le_of_le hJI hIJ }

end AdicTransfer

section Eisenstein

variable (q : ℕ) [hq : Fact q.Prime] (W₀ : Type*) [CommRing W₀] [IsDomain W₀]
  [IsDiscreteValuationRing W₀]

private theorem natCast_ne_zero (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) : (q : W₀) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field W₀
  rw [hW₀, h, Ideal.span_singleton_eq_bot]

private theorem natCast_mem_maximalIdeal (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (q : W₀) ∈ maximalIdeal W₀ :=
  hW₀ ▸ Ideal.mem_span_singleton_self _

private theorem natCast_not_mem_sq (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (q : W₀) ∉ (maximalIdeal W₀) ^ 2 := by
  have hq0 := natCast_ne_zero q W₀ hW₀
  have hqmem := natCast_mem_maximalIdeal q W₀ hW₀
  rw [hW₀, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h1 : (q : W₀) * (1 - q * c) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← sq, ← hc, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact hq0 h
  · have hu : IsUnit (q : W₀) := IsUnit.of_mul_eq_one c (by rwa [sub_eq_zero, eq_comm] at h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hqmem hu

private theorem cyclotomic_comp_X_add_one_eq_map :
    (cyclotomic q W₀).comp (X + 1) = ((cyclotomic q ℤ).comp (X + 1)).map (Int.castRingHom W₀) := by
  rw [Polynomial.map_comp, map_cyclotomic_int]
  simp

private theorem monic_cyclotomic_comp_X_add_one_int : ((cyclotomic q ℤ).comp (X + 1)).Monic := by
  rw [show (X + 1 : ℤ[X]) = X + C 1 by simp]
  exact (cyclotomic.monic q ℤ).comp (monic_X_add_C 1) (by rw [natDegree_X_add_C]; exact one_ne_zero)

private theorem monic_cyclotomic_comp_X_add_one : ((cyclotomic q W₀).comp (X + 1)).Monic := by
  rw [cyclotomic_comp_X_add_one_eq_map]
  exact (monic_cyclotomic_comp_X_add_one_int q).map _

private theorem natDegree_cyclotomic_comp_X_add_one :
    ((cyclotomic q W₀).comp (X + 1)).natDegree = ((cyclotomic q ℤ).comp (X + 1)).natDegree := by
  rw [cyclotomic_comp_X_add_one_eq_map, (monic_cyclotomic_comp_X_add_one_int q).natDegree_map]

private theorem natDegree_cyclotomic_comp_X_add_one_int :
    ((cyclotomic q ℤ).comp (X + 1)).natDegree = q - 1 := by
  rw [natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hq.out,
    show (X + 1 : ℤ[X]) = X + C 1 by simp, natDegree_X_add_C, mul_one]

private theorem isEisensteinAt_cyclotomic_comp_X_add_one
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    ((cyclotomic q W₀).comp (X + 1)).IsEisensteinAt (maximalIdeal W₀) := by
  have hEz := cyclotomic_comp_X_add_one_isEisensteinAt q
  refine (monic_cyclotomic_comp_X_add_one q W₀).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal W₀).ne_top ?_ ?_
  · intro n hn
    rw [natDegree_cyclotomic_comp_X_add_one] at hn
    have hmem : ((cyclotomic q ℤ).comp (X + 1)).coeff n ∈ Ideal.span {(q : ℤ)} := hEz.mem hn
    have hd : (q : ℤ) ∣ ((cyclotomic q ℤ).comp (X + 1)).coeff n := Ideal.mem_span_singleton.mp hmem
    rw [cyclotomic_comp_X_add_one_eq_map, coeff_map, hW₀, Ideal.mem_span_singleton]
    simpa using map_dvd (Int.castRingHom W₀) hd
  · have h0 : ((cyclotomic q W₀).comp (X + 1)).coeff 0 = (q : W₀) := by
      rw [coeff_zero_eq_eval_zero, eval_comp]
      simp [eval_one_cyclotomic_prime]
    rw [h0]
    exact natCast_not_mem_sq q W₀ hW₀

private theorem irreducible_cyclotomic (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    Irreducible (cyclotomic q W₀) := by
  have hirr : Irreducible ((cyclotomic q W₀).comp (X + 1)) :=
    (isEisensteinAt_cyclotomic_comp_X_add_one q W₀ hW₀).irreducible
      (IsLocalRing.maximalIdeal.isMaximal W₀).isPrime
      (monic_cyclotomic_comp_X_add_one q W₀).isPrimitive
      (by
        rw [natDegree_cyclotomic_comp_X_add_one, natDegree_cyclotomic_comp_X_add_one_int]
        have := hq.out.two_le
        omega)
  have hcomp : (algEquivAevalXAddC (1 : W₀)) (cyclotomic q W₀) =
      (cyclotomic q W₀).comp (X + 1) := by
    rw [algEquivAevalXAddC_apply, comp_eq_aeval, map_one]
  rw [← MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : W₀)).toMulEquiv]
  exact hcomp ▸ hirr

private theorem prime_cyclotomic (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    Prime (cyclotomic q W₀) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_cyclotomic q W₀ hW₀)

end Eisenstein

section Main

variable (q : ℕ) [hq : Fact q.Prime] (W₀ : Type*) [CommRing W₀] [IsDomain W₀]
  [IsDiscreteValuationRing W₀]

private abbrev O (q : ℕ) [Fact q.Prime] (W₀ : Type*) [CommRing W₀] : Type _ :=
  AdjoinRoot (cyclotomic q W₀)

private noncomputable abbrev zeta (q : ℕ) [Fact q.Prime] (W₀ : Type*) [CommRing W₀] :
    O q W₀ := AdjoinRoot.root (cyclotomic q W₀)

private theorem aeval_cyclotomic_prime_eq_sum {S : Type*} [CommRing S] [Algebra W₀ S] (z : S) :
    aeval z (cyclotomic q W₀) = ∑ i ∈ Finset.range q, z ^ i := by
  rw [cyclotomic_prime, map_sum]
  simp

private theorem sum_zeta_pow : (∑ i ∈ Finset.range q, (zeta q W₀) ^ i) = 0 := by
  rw [← aeval_cyclotomic_prime_eq_sum q W₀ (zeta q W₀), AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

private theorem zeta_sub_one_dvd_natCast : (zeta q W₀ - 1) ∣ (q : O q W₀) := by
  have h : (q : O q W₀) = -∑ i ∈ Finset.range q, ((zeta q W₀) ^ i - 1) := by
    rw [Finset.sum_sub_distrib, sum_zeta_pow]
    simp
  rw [h]
  refine (Finset.dvd_sum fun i _ => ?_).neg_right
  simpa using sub_dvd_pow_sub_pow (zeta q W₀) 1 i

private theorem natCast_mem_span : (q : O q W₀) ∈ Ideal.span {zeta q W₀ - 1} :=
  Ideal.mem_span_singleton.mpr (zeta_sub_one_dvd_natCast q W₀)

private theorem natCast_O_ne_zero (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (q : O q W₀) ≠ 0 := by
  intro h
  have hdeg : (cyclotomic q W₀).degree ≠ 0 := by
    rw [degree_cyclotomic, Nat.totient_prime hq.out]
    have := hq.out.two_le
    exact_mod_cast (show q - 1 ≠ 0 by omega)
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  apply natCast_ne_zero q W₀ hW₀
  apply hinj
  rw [map_natCast, map_zero]
  exact h

private theorem isDomain (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) : IsDomain (O q W₀) :=
  AdjoinRoot.isDomain_of_prime (prime_cyclotomic q W₀ hW₀)

section Residue

variable (k : Type*) [Field k] [CharP k q] (res₀ : W₀ →+* k)

private theorem eval₂_one_cyclotomic : (cyclotomic q W₀).eval₂ res₀ 1 = 0 := by
  rw [eval₂_at_one, eval_one_cyclotomic_prime, map_natCast, CharP.cast_eq_zero]

private noncomputable def res : O q W₀ →+* k :=
  AdjoinRoot.lift res₀ 1 (eval₂_one_cyclotomic q W₀ k res₀)

private theorem res_of (w : W₀) : res q W₀ k res₀ (algebraMap W₀ (O q W₀) w) = res₀ w := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

private theorem res_zeta : res q W₀ k res₀ (zeta q W₀) = 1 :=
  AdjoinRoot.lift_root _

private theorem res_surjective (hres₀ : Function.Surjective res₀) :
    Function.Surjective (res q W₀ k res₀) := fun y => by
  obtain ⟨w, rfl⟩ := hres₀ y
  exact ⟨algebraMap W₀ (O q W₀) w, res_of q W₀ k res₀ w⟩

private theorem ker_res (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    RingHom.ker (res q W₀ k res₀) = Ideal.span {zeta q W₀ - 1} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    induction x using AdjoinRoot.induction_on with
    | ih p =>
      have hp : res q W₀ k res₀ (AdjoinRoot.mk _ p) = res₀ (p.eval 1) := by
        rw [res, AdjoinRoot.lift_mk, eval₂_at_one]
      rw [hp] at hx
      have h1 : p.eval 1 ∈ Ideal.span {(q : W₀)} := by
        rw [← hW₀, ← hker₀, RingHom.mem_ker]; exact hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
      have hsplit : AdjoinRoot.mk (cyclotomic q W₀) p =
          AdjoinRoot.mk (cyclotomic q W₀) (p - C (p.eval 1)) +
            algebraMap W₀ (O q W₀) a * (q : O q W₀) := by
        rw [map_sub, AdjoinRoot.mk_C, ← ha, map_mul, map_natCast, ← AdjoinRoot.algebraMap_eq]
        ring
      rw [hsplit]
      refine dvd_add ?_ (dvd_mul_of_dvd_right (zeta_sub_one_dvd_natCast q W₀) _)
      have hd : (X - C (1 : W₀)) ∣ p - C (p.eval 1) := X_sub_C_dvd_sub_C_eval
      have := map_dvd (AdjoinRoot.mk (cyclotomic q W₀)) hd
      simpa [AdjoinRoot.mk_X, AdjoinRoot.mk_C] using this
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      res_zeta, map_one, sub_self]

private theorem isMaximal_span (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (Ideal.span {zeta q W₀ - 1}).IsMaximal := by
  rw [← ker_res q W₀ k res₀ hker₀ hW₀]
  exact RingHom.ker_isMaximal_of_surjective _ (res_surjective q W₀ k res₀ hres₀)

end Residue

private scoped instance : Module.Finite W₀ (O q W₀) := (cyclotomic.monic q W₀).finite_adjoinRoot

private theorem zeta_sub_one_pow_mem (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (zeta q W₀ - 1) ^ (q - 1) ∈ Ideal.span {(q : O q W₀)} := by
  have := isDomain q W₀ hW₀
  have hEis := isEisensteinAt_cyclotomic_comp_X_add_one q W₀ hW₀
  have hmo := monic_cyclotomic_comp_X_add_one q W₀
  have hroot : aeval (zeta q W₀ - 1) ((cyclotomic q W₀).comp (X + 1)) = 0 := by
    rw [aeval_comp]
    simp only [map_add, aeval_X, map_one, sub_add_cancel]
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h := hEis.isWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      hroot hmo (q - 1)
    (by rw [hmo.natDegree_map, natDegree_cyclotomic_comp_X_add_one,
      natDegree_cyclotomic_comp_X_add_one_int])
  rw [hW₀, Ideal.map_span, Set.image_singleton, map_natCast] at h
  exact h

private theorem span_pow_le (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    Ideal.span {zeta q W₀ - 1} ^ (q - 1) ≤ Ideal.span {(q : O q W₀)} := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  exact zeta_sub_one_pow_mem q W₀ hW₀

private theorem span_natCast_le : Ideal.span {(q : O q W₀)} ≤ Ideal.span {zeta q W₀ - 1} := by
  rw [Ideal.span_singleton_le_iff_mem]
  exact natCast_mem_span q W₀

private theorem map_maximalIdeal (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    (maximalIdeal W₀).map (algebraMap W₀ (O q W₀)) = Ideal.span {(q : O q W₀)} := by
  rw [hW₀, Ideal.map_span, Set.image_singleton, map_natCast]

private theorem isAdicComplete_span_natCast [IsAdicComplete (maximalIdeal W₀) W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    IsAdicComplete (Ideal.span {(q : O q W₀)}) (O q W₀) := by
  have hmod : IsAdicComplete (maximalIdeal W₀) (O q W₀) :=
    IsAdicComplete.of_module_finite (maximalIdeal W₀)
  rw [← map_maximalIdeal q W₀ hW₀]
  exact
    { toIsHausdorff := (IsHausdorff.map_algebraMap_iff (S := O q W₀)).mpr hmod.toIsHausdorff
      toIsPrecomplete := (IsPrecomplete.map_algebraMap_iff (S := O q W₀)).mpr hmod.toIsPrecomplete }

private theorem isAdicComplete_span [IsAdicComplete (maximalIdeal W₀) W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)}) :
    IsAdicComplete (Ideal.span {zeta q W₀ - 1}) (O q W₀) :=
  haveI := isAdicComplete_span_natCast q W₀ hW₀
  isAdicComplete_of_pow_le_of_le (span_pow_le q W₀ hW₀) (span_natCast_le q W₀)

private theorem isLocalRing [IsAdicComplete (maximalIdeal W₀) W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type*) [Field k] [CharP k q] (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) : IsLocalRing (O q W₀) :=
  haveI := isMaximal_span q W₀ k res₀ hres₀ hker₀ hW₀
  haveI := isAdicComplete_span q W₀ hW₀
  isLocalRing_of_isAdicComplete_maximal (Ideal.span {zeta q W₀ - 1})

private theorem maximalIdeal_eq [IsAdicComplete (maximalIdeal W₀) W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type*) [Field k] [CharP k q] (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) :
    @maximalIdeal (O q W₀) _ (isLocalRing q W₀ hW₀ k res₀ hres₀ hker₀) =
      Ideal.span {zeta q W₀ - 1} :=
  letI := isLocalRing q W₀ hW₀ k res₀ hres₀ hker₀
  (IsLocalRing.eq_maximalIdeal (isMaximal_span q W₀ k res₀ hres₀ hker₀ hW₀)).symm

private theorem isDiscreteValuationRing [IsAdicComplete (maximalIdeal W₀) W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type*) [Field k] [CharP k q] (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = maximalIdeal W₀) :
    @IsDiscreteValuationRing (O q W₀) _ (isDomain q W₀ hW₀) := by
  let := isDomain q W₀ hW₀
  let := isLocalRing q W₀ hW₀ k res₀ hres₀ hker₀
  have hmax := maximalIdeal_eq q W₀ hW₀ k res₀ hres₀ hker₀
  have hnf : ¬IsField (O q W₀) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax]
    intro h
    apply natCast_O_ne_zero q W₀ hW₀
    have := natCast_mem_span q W₀
    rw [h] at this
    exact (Submodule.mem_bot _).mp this
  have hprinc : (maximalIdeal (O q W₀)).IsPrincipal := ⟨⟨zeta q W₀ - 1, hmax⟩⟩
  have hpow : ∀ I : Ideal (O q W₀), I ≠ ⊥ → ∃ n : ℕ, I = maximalIdeal (O q W₀) ^ n :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (O q W₀)).out 5 7).mp hprinc
  have hpir : IsPrincipalIdealRing (O q W₀) := ⟨fun I => by
    by_cases hI : I = ⊥
    · rw [hI]
      exact ⟨⟨0, by simp⟩⟩
    · obtain ⟨n, rfl⟩ := hpow I hI
      obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (maximalIdeal (O q W₀))
      exact ⟨⟨a ^ n, by rw [ha]; exact Ideal.span_singleton_pow a n⟩⟩⟩
  exact { hpir with
    not_a_field' := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf }

private theorem existsUnique_algHom (S : Type*) [CommRing S] [Algebra W₀ S] (z : S)
    (hz : (∑ i ∈ Finset.range q, z ^ i) = 0) :
    ∃! f : O q W₀ →ₐ[W₀] S, f (zeta q W₀) = z := by
  have hz' : (cyclotomic q W₀).eval₂ (Algebra.ofId W₀ S) z = 0 := by
    have := aeval_cyclotomic_prime_eq_sum q W₀ z
    rw [hz, aeval_def] at this
    exact this
  refine ⟨AdjoinRoot.liftAlgHom (cyclotomic q W₀) (Algebra.ofId W₀ S) z hz',
    AdjoinRoot.liftAlgHom_root _ _ _ _, fun g hg => ?_⟩
  apply AdjoinRoot.algHom_ext
  rw [hg, AdjoinRoot.liftAlgHom_root]

end Main

end CycloDVR

universe u v w

open CycloDVR in
/-- Over a complete discrete valuation ring `W₀` whose maximal ideal is
generated by a rational prime `q`, there is a complete discrete valuation
ring obtained by adjoining a primitive `q`-th root of unity: its maximal
ideal is generated by `ζ - 1`, it maps onto the given residue field, and
it is universal for elements `z` with `∑ i < q, z ^ i = 0`. -/
public theorem IsDiscreteValuationRing.exists_cyclotomic_dvr_of_maximalIdeal_eq_span_prime
    (q : ℕ) [Fact q.Prime]
    (W₀ : Type u) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (k : Type v) [Field k] [CharP k q]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀)
    (hker₀ : RingHom.ker res₀ = IsLocalRing.maximalIdeal W₀) :
    ∃ (𝒪 : Type u) (_ : CommRing 𝒪) (_ : IsDomain 𝒪) (_ : IsDiscreteValuationRing 𝒪)
      (_ : Algebra W₀ 𝒪)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪) (ζ : 𝒪) (res : 𝒪 →+* k),
      (∑ i ∈ Finset.range q, ζ ^ i) = 0 ∧
      IsLocalRing.maximalIdeal 𝒪 = Ideal.span {ζ - 1} ∧
      Function.Surjective res ∧ RingHom.ker res = IsLocalRing.maximalIdeal 𝒪 ∧
      (∀ w : W₀, res (algebraMap W₀ 𝒪 w) = res₀ w) ∧
      (∀ (S : Type w) [CommRing S] [Algebra W₀ S] (z : S),
        (∑ i ∈ Finset.range q, z ^ i) = 0 →
        ∃! f : 𝒪 →ₐ[W₀] S, f ζ = z) := by
  let hdom := CycloDVR.isDomain q W₀ hW₀
  let hdvr := CycloDVR.isDiscreteValuationRing q W₀ hW₀ k res₀ hres₀ hker₀
  have hmax : IsLocalRing.maximalIdeal (CycloDVR.O q W₀) =
      Ideal.span {CycloDVR.zeta q W₀ - 1} :=
    (IsLocalRing.eq_maximalIdeal
      (CycloDVR.isMaximal_span q W₀ k res₀ hres₀ hker₀ hW₀)).symm
  have hcomp : IsAdicComplete (IsLocalRing.maximalIdeal (CycloDVR.O q W₀))
      (CycloDVR.O q W₀) := by
    rw [hmax]; exact CycloDVR.isAdicComplete_span q W₀ hW₀
  refine ⟨CycloDVR.O q W₀, inferInstance, hdom, hdvr, inferInstance, hcomp,
    CycloDVR.zeta q W₀, CycloDVR.res q W₀ k res₀,
    CycloDVR.sum_zeta_pow q W₀, hmax, CycloDVR.res_surjective q W₀ k res₀ hres₀, ?_,
    CycloDVR.res_of q W₀ k res₀,
    fun S _ _ z hz => CycloDVR.existsUnique_algHom q W₀ S z hz⟩
  rw [hmax, CycloDVR.ker_res q W₀ k res₀ hker₀ hW₀]
