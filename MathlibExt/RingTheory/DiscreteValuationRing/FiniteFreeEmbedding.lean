/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free.lean`
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

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import MathlibExt.RingTheory.AdicCompletion.ModuleFinite
public import MathlibExt.RingTheory.LocalRing.AdicCompleteDomain
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Embedding a finite free algebra over a complete DVR into a product of DVRs

A reduced finite free algebra `T` over a complete characteristic-zero
discrete valuation ring `𝒪` with finite residue field embeds, as an
`𝒪`-algebra, into a finite product of complete characteristic-zero discrete
valuation rings with finite residue fields, each factor carrying a local
`𝒪`-algebra map. The factors are the integral closures of `𝒪` in the
fraction fields of the quotients of `T` by its minimal primes; when `T` is
the zero ring the product is empty.
-/

@[expose] public section

universe u v

namespace IsDiscreteValuationRingFiniteFreeAux

open IsLocalRing

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
  [CharZero 𝒪]
  {T : Type v} [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
  [Module.Free 𝒪 T]

private theorem eq_zero_or_eq_zero_of_smul_eq_zero_of_free {x : 𝒪} {t : T}
    (h : x • t = 0) : x = 0 ∨ t = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    let b := Module.Free.chooseBasis 𝒪 T
    have hrepr : b.repr (x • t) = 0 := by rw [h, map_zero]
    rw [map_smul] at hrepr
    have ht : b.repr t = 0 := by
      ext i
      have hi := DFunLike.congr_fun hrepr i
      rw [Finsupp.smul_apply, smul_eq_mul] at hi
      simpa using (mul_eq_zero.mp hi).resolve_left hx
    exact b.repr.map_eq_zero_iff.mp ht

private theorem algebraMap_quotient_injective_of_mem_minimalPrimes
    (P : Ideal T) (hP : P ∈ minimalPrimes T) :
    Function.Injective (algebraMap 𝒪 (T ⧸ P)) := by
  haveI : P.IsPrime := hP.1.1
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hmem : algebraMap 𝒪 T x ∈ P := by
    rw [IsScalarTower.algebraMap_apply 𝒪 T (T ⧸ P)] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hnzd : algebraMap 𝒪 T x ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    have hsmul : x • t = 0 := by rw [Algebra.smul_def, mul_comm]; exact ht
    exact (eq_zero_or_eq_zero_of_smul_eq_zero_of_free hsmul).resolve_left hx0
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hP hnzd

variable (𝒪) in
private abbrev IntClosure (P : Ideal T) [P.IsPrime] : Type v :=
  integralClosure 𝒪 (FractionRing (T ⧸ P))

section PerPrime

variable (P : Ideal T) [P.IsPrime]
  (hinj : Function.Injective (algebraMap 𝒪 (T ⧸ P)))

include hinj in

private theorem moduleFinite_intClosure : Module.Finite 𝒪 (IntClosure 𝒪 P) := by
  haveI : FaithfulSMul 𝒪 (T ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (T ⧸ P)).mpr hinj
  haveI : Module.Finite 𝒪 (T ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 P)
  haveI : CharZero (T ⧸ P) := charZero_of_injective_algebraMap hinj
  haveI : CharZero (FractionRing 𝒪) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ P) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra (FractionRing 𝒪) (FractionRing (T ⧸ P)) := FractionRing.liftAlgebra _ _
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact IsIntegralClosure.finite 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) (IntClosure 𝒪 P)

include hinj in
private theorem algebraMap_intClosure_injective :
    Function.Injective (algebraMap 𝒪 (IntClosure 𝒪 P)) := by
  have h1 : Function.Injective (algebraMap 𝒪 (FractionRing (T ⧸ P))) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))]
    exact (IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P))).comp hinj
  intro x y hxy
  apply h1
  rw [IsScalarTower.algebraMap_apply 𝒪 (IntClosure 𝒪 P) (FractionRing (T ⧸ P)),
    IsScalarTower.algebraMap_apply 𝒪 (IntClosure 𝒪 P) (FractionRing (T ⧸ P)), hxy]

include hinj in
private theorem charZero_intClosure : CharZero (IntClosure 𝒪 P) :=
  charZero_of_injective_algebraMap (algebraMap_intClosure_injective P hinj)

include hinj in

private theorem isDedekindDomain_intClosure : IsDedekindDomain (IntClosure 𝒪 P) := by
  haveI : FaithfulSMul 𝒪 (T ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (T ⧸ P)).mpr hinj
  haveI : Module.Finite 𝒪 (T ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 P)
  haveI : CharZero (T ⧸ P) := charZero_of_injective_algebraMap hinj
  haveI : CharZero (FractionRing 𝒪) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ P) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra (FractionRing 𝒪) (FractionRing (T ⧸ P)) := FractionRing.liftAlgebra _ _
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact IsIntegralClosure.isDedekindDomain 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P))
    (IntClosure 𝒪 P)

include hinj in
private theorem isDVR_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsDiscreteValuationRing (IntClosure 𝒪 P) := by
  haveI : IsDedekindDomain (IntClosure 𝒪 P) := isDedekindDomain_intClosure P hinj
  have hnf : ¬ IsField (IntClosure 𝒪 P) := by
    intro hfieldR
    have hfield𝒪 : IsField 𝒪 :=
      isField_of_isIntegral_of_isField (algebraMap_intClosure_injective P hinj) hfieldR
    exact IsDiscreteValuationRing.not_isField 𝒪 hfield𝒪
  have h : IsDedekindDomain (IntClosure 𝒪 P) ↔ IsDiscreteValuationRing (IntClosure 𝒪 P) :=
    (IsDiscreteValuationRing.TFAE _ hnf).out 3 1
  exact h.mp inferInstance

include hinj in
private theorem isLocalHom_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsLocalHom (algebraMap 𝒪 (IntClosure 𝒪 P)) := by
  haveI : FaithfulSMul 𝒪 (IntClosure 𝒪 P) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (IntClosure 𝒪 P)).mpr
      (algebraMap_intClosure_injective P hinj)
  exact Algebra.IsIntegral.isLocalHom 𝒪 (IntClosure 𝒪 P)

include hinj in

private theorem isAdicComplete_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (IntClosure 𝒪 P)) (IntClosure 𝒪 P) := by
  haveI := moduleFinite_intClosure P hinj
  exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)

include hinj in

private theorem finite_residueField_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    Finite (IsLocalRing.ResidueField (IntClosure 𝒪 P)) := by
  haveI := moduleFinite_intClosure P hinj
  haveI := isLocalHom_intClosure P hinj
  exact IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) ‹_›

private noncomputable def toIntClosure : T →ₐ[𝒪] IntClosure 𝒪 P :=
  AlgHom.codRestrict
    ((IsScalarTower.toAlgHom 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))).comp
      (Ideal.Quotient.mkₐ 𝒪 P))
    (integralClosure 𝒪 (FractionRing (T ⧸ P)))
    (fun t => (Algebra.IsIntegral.isIntegral (R := 𝒪) t).map
      ((IsScalarTower.toAlgHom 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))).comp
        (Ideal.Quotient.mkₐ 𝒪 P)))

private theorem toIntClosure_eq_zero_iff {t : T} :
    toIntClosure (𝒪 := 𝒪) P t = 0 ↔ t ∈ P := by
  constructor
  · intro h
    have hval : algebraMap (T ⧸ P) (FractionRing (T ⧸ P)) (Ideal.Quotient.mk P t) = 0 :=
      congrArg (fun x : IntClosure 𝒪 P => (x : FractionRing (T ⧸ P))) h
    have hmk : Ideal.Quotient.mk P t = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P)))).mp hval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · intro h
    apply Subtype.ext
    change algebraMap (T ⧸ P) (FractionRing (T ⧸ P)) (Ideal.Quotient.mk P t) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

end PerPrime

private theorem exists_embedding_into_dvrs :
    ∃ (n : ℕ) (R : Fin n → Type v) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing 𝒪 T
  have hfin : (minimalPrimes T).Finite := minimalPrimes.finite_of_isNoetherianRing T
  haveI := hfin.fintype
  let e : Fin (Fintype.card (minimalPrimes T)) ≃ (minimalPrimes T) := (Fintype.equivFin _).symm
  haveI hprime : ∀ j, ((e j : Ideal T)).IsPrime := fun j => (e j).2.1.1
  have hinj : ∀ j, Function.Injective (algebraMap 𝒪 (T ⧸ (e j : Ideal T))) := fun j =>
    algebraMap_quotient_injective_of_mem_minimalPrimes _ (e j).2
  haveI hfinite : ∀ j, Module.Finite 𝒪 (IntClosure 𝒪 (e j : Ideal T)) :=
    fun j => moduleFinite_intClosure (e j : Ideal T) (hinj j)
  haveI hlocal : ∀ j, IsLocalRing (IntClosure 𝒪 (e j : Ideal T)) := fun j =>
    IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete (R := 𝒪)
  refine ⟨_, fun j => IntClosure 𝒪 (e j : Ideal T),
    fun j => inferInstance,
    fun j => inferInstanceAs
      (IsDomain (integralClosure 𝒪 (FractionRing (T ⧸ (e j : Ideal T))))),
    fun j => isDVR_intClosure _ (hinj j),
    fun j => isAdicComplete_intClosure _ (hinj j),
    fun j => finite_residueField_intClosure _ (hinj j),
    fun j => charZero_intClosure _ (hinj j),
    fun j => inferInstance,
    fun j => isLocalHom_intClosure _ (hinj j),
    Pi.algHom _ _ (fun j => toIntClosure (e j : Ideal T)),
    ?_⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hmem : ∀ p ∈ minimalPrimes T, t ∈ p := by
    intro p hp
    have hj := congr_fun ht (e.symm ⟨p, hp⟩)
    have hzero : toIntClosure (𝒪 := 𝒪) (e (e.symm ⟨p, hp⟩) : Ideal T) t = 0 := hj
    have hP : t ∈ (e (e.symm ⟨p, hp⟩) : Ideal T) :=
      (toIntClosure_eq_zero_iff _).mp hzero
    have hP' : (e (e.symm ⟨p, hp⟩) : Ideal T) = p := by rw [e.apply_symm_apply]
    exact hP' ▸ hP
  have hsinf : t ∈ sInf ((⊥ : Ideal T).minimalPrimes) :=
    Submodule.mem_sInf.mpr (fun p hp => hmem p hp)
  rw [Ideal.sInf_minimalPrimes, ← Ideal.zero_eq_bot, ← nilradical, nilradical_eq_zero,
    Ideal.zero_eq_bot] at hsinf
  exact (Ideal.mem_bot).mp hsinf

end IsDiscreteValuationRingFiniteFreeAux

namespace IsDiscreteValuationRing

open IsDiscreteValuationRingFiniteFreeAux

/-- A reduced finite free algebra over a complete characteristic-zero
discrete valuation ring with finite residue field embeds into a finite
product of complete characteristic-zero discrete valuation rings with
finite residue fields, each factor a local algebra over the base. -/
public theorem exists_algHom_pi_of_module_finite_free
    {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (T : Type v) [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    [Module.Free 𝒪 T] :
    ∃ (n : ℕ) (R : Fin n → Type v) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι :=
  IsDiscreteValuationRingFiniteFreeAux.exists_embedding_into_dvrs (𝒪 := 𝒪) (T := T)


end IsDiscreteValuationRing
