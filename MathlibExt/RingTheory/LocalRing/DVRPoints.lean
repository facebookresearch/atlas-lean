/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot.lean`
and
`P2M/Sol/S_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot.lean`
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

public import MathlibExt.RingTheory.LocalRing.AdicCompleteDomain
public import MathlibExt.RingTheory.DiscreteValuationRing.FiniteExtensionComplete
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Finitely many DVR points of a finite torsion-free algebra

Let `𝒪` be an adically complete discrete valuation ring with finite residue
field and of characteristic zero, and `P` a finite torsion-free `𝒪`-algebra
that is local and reduced. Then there are finitely many adically complete
discrete valuation rings `A i`, finite over `𝒪`, with local maps `P → A i`
whose kernels intersect to `⊥`, and a common denominator `a ∈ 𝒪` clearing
all denominators: every tuple `(y i)` comes from some `x : P` after
scaling by `a`.
-/

@[expose] public section

open IsLocalRing
universe u v

namespace Ideal

private theorem algebraMap_quotient_injective_of_mem_minimalPrimes
    {𝒪 : Type u} {P : Type v} [CommRing 𝒪] [IsDomain 𝒪] [CommRing P] [Algebra 𝒪 P]
    [Module.IsTorsionFree 𝒪 P] {𝔭 : Ideal P} (h𝔭 : 𝔭 ∈ minimalPrimes P) :
    Function.Injective (algebraMap 𝒪 (P ⧸ 𝔭)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  rw [IsScalarTower.algebraMap_apply 𝒪 P (P ⧸ 𝔭), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  refine notMem_nonZeroDivisors_of_mem_mem_minimalPrimes ha h𝔭 ?_
  have hreg : IsSMulRegular P (algebraMap 𝒪 P a) :=
    (isSMulRegular_algebraMap_iff P).mpr ((IsRegular.of_ne_zero ha0).isSMulRegular)
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => hreg ?_, fun x hx => hreg ?_⟩
  · simpa [smul_eq_mul] using hx
  · simpa [smul_eq_mul, mul_comm] using hx

private theorem exists_ne_zero_forall_exists_mk_eq_smul
    {𝒪 : Type u} {P : Type v} [CommRing 𝒪] [IsDomain 𝒪] [CommRing P] [Algebra 𝒪 P]
    [Module.Finite 𝒪 P]
    {n : ℕ} (𝔭 : Fin n → Ideal P) (h𝔭 : ∀ i, 𝔭 i ∈ minimalPrimes P)
    (hinj : Function.Injective 𝔭) :
    ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : ∀ i, P ⧸ 𝔭 i, ∃ x : P, ∀ i, Ideal.Quotient.mk (𝔭 i) x = a • y i := by
  classical
  have hpr : ∀ i, (𝔭 i).IsPrime := fun i => (h𝔭 i).1.1
  haveI hdom : ∀ i, IsDomain (P ⧸ 𝔭 i) := fun i =>
    (Ideal.Quotient.isDomain_iff_prime (𝔭 i)).mpr (hpr i)
  have hsep : ∀ i, ∃ t : P, t ∈ (Finset.univ.erase i).inf 𝔭 ∧ t ∉ 𝔭 i := by
    intro i
    have hnle : ¬ (Finset.univ.erase i).inf 𝔭 ≤ 𝔭 i := by
      rw [(hpr i).inf_le']
      rintro ⟨j, hj, hle⟩
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hge : 𝔭 i ≤ 𝔭 j := (h𝔭 i).2 ⟨hpr j, bot_le⟩ hle
      exact hji (hinj (le_antisymm hle hge))
    obtain ⟨t, ht, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    exact ⟨t, ht, htn⟩
  choose t ht htn using hsep
  have hai : ∀ i, ∃ (a : 𝒪) (s : P), a ≠ 0 ∧
      Ideal.Quotient.mk (𝔭 i) (t i * s) = algebraMap 𝒪 (P ⧸ 𝔭 i) a := by
    intro i
    have ht0 : Ideal.Quotient.mk (𝔭 i) (t i) ≠ 0 :=
      mt Ideal.Quotient.eq_zero_iff_mem.mp (htn i)
    have hint : IsIntegral 𝒪 (Ideal.Quotient.mk (𝔭 i) (t i)) :=
      (Algebra.IsIntegral.isIntegral (R := 𝒪) (t i)).map (Ideal.Quotient.mkₐ 𝒪 (𝔭 i))
    obtain ⟨a, ha0, sb, hs⟩ :=
      hint.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ht0)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sb
    exact ⟨a, s, ha0, by rw [map_mul, ← hs]⟩
  choose a s ha0 has using hai
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.mpr fun i _ => ha0 i, fun y => ?_⟩
  choose ylift hylift using fun i => Ideal.Quotient.mk_surjective (y i)
  refine ⟨∑ j, algebraMap 𝒪 P (∏ k ∈ Finset.univ.erase j, a k) * (t j * s j) * ylift j,
    fun i => ?_⟩
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_mul, map_mul, has, hylift, Ideal.Quotient.mk_algebraMap, ← map_mul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i), Algebra.smul_def]
  · intro j _ hji
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ?_))
    have hle : (Finset.univ.erase j).inf 𝔭 ≤ 𝔭 i :=
      Finset.inf_le (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)
    exact hle (ht j)
  · intro h
    exact absurd (Finset.mem_univ i) h

end Ideal

namespace IsLocalRing

private theorem exists_algHom_dvr_of_isDomain
    {𝒪 : Type u} {D : Type v} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    [CommRing D] [IsDomain D] [IsLocalRing D] [Algebra 𝒪 D] [Module.Finite 𝒪 D]
    [FaithfulSMul 𝒪 D] :
    ∃ (A : Type v) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : Algebra 𝒪 A) (_ : Module.Finite 𝒪 A) (_ : FaithfulSMul 𝒪 A) (χ : D →ₐ[𝒪] A),
      Function.Injective χ ∧ IsLocalHom χ.toRingHom ∧
        ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : A, ∃ x : D, a • y = χ x := by
  let K := FractionRing 𝒪
  let L := FractionRing D
  letI : Algebra K L := FractionRing.liftAlgebra 𝒪 L
  haveI : FiniteDimensional K L := inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  haveI : Algebra.IsSeparable K L := inferInstance
  let C := integralClosure 𝒪 L
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain_fractionRing 𝒪 L
  haveI : Module.Finite 𝒪 C := IsIntegralClosure.finite 𝒪 K L C
  haveI : IsLocalRing C := IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete (R := 𝒪)
  have hinj𝒪C : Function.Injective (algebraMap 𝒪 C) :=
    FaithfulSMul.algebraMap_injective 𝒪 C
  have hnf : ¬ IsField C := fun h =>
    IsDiscreteValuationRing.not_isField 𝒪 (isField_of_isIntegral_of_isField hinj𝒪C h)
  haveI : IsDiscreteValuationRing C := by
    have h : IsDedekindDomain C ↔ IsDiscreteValuationRing C :=
      (IsDiscreteValuationRing.TFAE C hnf).out 3 1
    exact h.mp inferInstance
  let χ : D →ₐ[𝒪] C := IsIntegralClosure.lift 𝒪 C L
  have hχ : ∀ x, algebraMap C L (χ x) = algebraMap D L x := fun x =>
    IsIntegralClosure.algebraMap_lift 𝒪 C L x
  have hχinj : Function.Injective χ := fun x y hxy =>
    IsFractionRing.injective D L (by rw [← hχ, ← hχ, hxy])
  have hint : χ.toRingHom.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap 𝒪 D) χ.toRingHom ?_
    rw [show χ.toRingHom.comp (algebraMap 𝒪 D) = algebraMap 𝒪 C from
      RingHom.ext fun x => χ.commutes x]
    exact algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral 𝒪 C)
  have hpt : ∀ y : C, ∃ (a : 𝒪) (x : D), a ≠ 0 ∧ a • y = χ x := by
    intro y
    obtain ⟨d, s, hs, hds⟩ := IsFractionRing.div_surjective (A := D) (algebraMap C L y)
    have hsalg : IsAlgebraic 𝒪 s := (Algebra.IsIntegral.isIntegral (R := 𝒪) s).isAlgebraic
    obtain ⟨r, hr0, u, hu⟩ := hsalg.exists_nonzero_dvd hs
    refine ⟨r, u * d, hr0, ?_⟩
    apply IsIntegralClosure.algebraMap_injective C 𝒪 L
    have hs0 : algebraMap D L s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply 𝒪 C L, hχ,
      IsScalarTower.algebraMap_apply 𝒪 D L, hu, ← hds, map_mul, map_mul]
    have key : ∀ a b c : L, c ≠ 0 → c * a * (b / c) = a * b := fun a b c hc =>
      calc c * a * (b / c) = a * b * (c / c) := by ring
        _ = a * b := by rw [div_self hc, mul_one]
    exact key _ _ _ hs0
  have htors : ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : C, ∃ x : D, a • y = χ x := by
    classical
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := 𝒪) (M := C)
    choose a x ha0 hax using fun k => hpt (g k)
    refine ⟨∏ k, a k, Finset.prod_ne_zero_iff.mpr fun k _ => ha0 k, fun y => ?_⟩
    have hy : y ∈ Submodule.span 𝒪 (Set.range g) := hg ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪).mp hy
    refine ⟨∑ k, (c k * ∏ l ∈ Finset.univ.erase k, a l) • x k, ?_⟩
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hax, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_comm]
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, χ, hχinj, hint.isLocalHom hχinj, htors⟩

/-- A finite torsion-free local reduced algebra over an adically complete DVR
with finite residue field and characteristic zero admits finitely many
adically complete DVR points whose kernels intersect to `⊥`, with a common
denominator clearing all denominators. -/
theorem exists_fin_points_dvr_iInf_ker_eq_bot
    {𝒪 : Type u} {P : Type v} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    [CommRing P] [IsLocalRing P] [IsReduced P] [Algebra 𝒪 P] [Module.Finite 𝒪 P]
    [Module.IsTorsionFree 𝒪 P] :
    ∃ (n : ℕ) (A : Fin n → Type v) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsDiscreteValuationRing (A i))
      (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (A i))) (_ : ∀ i, CharZero (A i))
      (_ : ∀ i, Algebra 𝒪 (A i)) (_ : ∀ i, Module.Finite 𝒪 (A i))
      (_ : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)))
      (χ : ∀ i, P →ₐ[𝒪] A i),
      (∀ i, IsLocalHom (χ i).toRingHom) ∧ ⨅ i, RingHom.ker (χ i).toRingHom = ⊥ ∧
        ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : ∀ i, A i, ∃ x : P, ∀ i, χ i x = a • y i := by
  classical
  haveI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing 𝒪 P
  have hfin : (minimalPrimes P).Finite := minimalPrimes.finite_of_isNoetherianRing P
  let t := hfin.toFinset
  let e : t ≃ Fin t.card := t.equivFin
  let 𝔭 : Fin t.card → Ideal P := fun i => ((e.symm i : t) : Ideal P)
  have h𝔭 : ∀ i, 𝔭 i ∈ minimalPrimes P := fun i => hfin.mem_toFinset.mp (e.symm i).2
  have hpr : ∀ i, (𝔭 i).IsPrime := fun i => (h𝔭 i).1.1
  haveI hdom : ∀ i, IsDomain (P ⧸ 𝔭 i) := fun i =>
    (Ideal.Quotient.isDomain_iff_prime (𝔭 i)).mpr (hpr i)
  haveI hlocal : ∀ i, IsLocalRing (P ⧸ 𝔭 i) := fun i =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (𝔭 i)) Ideal.Quotient.mk_surjective
  haveI hff : ∀ i, FaithfulSMul 𝒪 (P ⧸ 𝔭 i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective 𝒪 (P ⧸ 𝔭 i)).mpr
      (Ideal.algebraMap_quotient_injective_of_mem_minimalPrimes (h𝔭 i))
  haveI hmf : ∀ i, Module.Finite 𝒪 (P ⧸ 𝔭 i) := fun i =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 (𝔭 i)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 (𝔭 i))
  choose A iCR iDom iDVR iAlg iMF iFF ψ hψinj hψloc hψtors using
    fun i => IsLocalRing.exists_algHom_dvr_of_isDomain (𝒪 := 𝒪) (D := P ⧸ 𝔭 i)
  haveI hlh : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)) := fun i =>
    Algebra.IsIntegral.isLocalHom 𝒪 (A i)
  refine ⟨t.card, A, iCR, iDom, iDVR,
    fun i => IsDiscreteValuationRing.isAdicComplete_of_finite_local_extension (A := 𝒪),
    fun i => IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) ‹_›,
    fun i => charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective 𝒪 (A i)),
    iAlg, iMF, hlh, fun i => (ψ i).comp (Ideal.Quotient.mkₐ 𝒪 (𝔭 i)), ?_, ?_, ?_⟩
  · intro i
    haveI := hψloc i
    haveI : IsLocalHom (Ideal.Quotient.mkₐ 𝒪 (𝔭 i)).toRingHom :=
      IsLocalHom.of_surjective _ (Ideal.Quotient.mkₐ_surjective 𝒪 (𝔭 i))
    exact RingHom.isLocalHom_comp (ψ i).toRingHom (Ideal.Quotient.mkₐ 𝒪 (𝔭 i)).toRingHom
  · have hker : ∀ i, RingHom.ker ((ψ i).comp (Ideal.Quotient.mkₐ 𝒪 (𝔭 i))).toRingHom = 𝔭 i :=
      fun i => by
        ext x
        rw [RingHom.mem_ker]
        change ψ i (Ideal.Quotient.mk (𝔭 i) x) = 0 ↔ _
        rw [← map_zero (ψ i), (hψinj i).eq_iff, Ideal.Quotient.eq_zero_iff_mem]
    have hsinf : sInf (minimalPrimes P) = (⊥ : Ideal P) := by
      rw [show minimalPrimes P = (⊥ : Ideal P).minimalPrimes from rfl,
        Ideal.sInf_minimalPrimes]
      exact nilradical_eq_zero P
    have h1 : (⨅ i, 𝔭 i) ≤ sInf (minimalPrimes P) := le_sInf fun 𝔮 h𝔮 => by
      have hm : 𝔮 ∈ t := hfin.mem_toFinset.mpr h𝔮
      have heq : 𝔭 (e ⟨𝔮, hm⟩) = 𝔮 := by
        change ((e.symm (e ⟨𝔮, hm⟩) : t) : Ideal P) = 𝔮
        rw [Equiv.symm_apply_apply]
      exact heq ▸ iInf_le _ (e ⟨𝔮, hm⟩)
    exact le_antisymm ((iInf_congr hker).le.trans (h1.trans hsinf.le)) bot_le
  · have h𝔭inj : Function.Injective 𝔭 := fun i j hij =>
      e.symm.injective (Subtype.ext hij)
    obtain ⟨a₀, ha₀, hcrt⟩ :=
      Ideal.exists_ne_zero_forall_exists_mk_eq_smul (𝒪 := 𝒪) 𝔭 h𝔭 h𝔭inj
    choose b hb0 hbt using hψtors
    refine ⟨a₀ * ∏ i, b i, mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i),
      fun y => ?_⟩
    choose z hz using fun i => hbt i (y i)
    obtain ⟨x, hx⟩ := hcrt fun i => (∏ j ∈ Finset.univ.erase i, b j) • z i
    refine ⟨x, fun i => ?_⟩
    change ψ i (Ideal.Quotient.mk (𝔭 i) x) = _
    rw [hx i, map_smul, map_smul, ← hz i, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

end IsLocalRing
