/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_coe_eq_heckeT.lean`,
`P2M/Sol/S_CuspForm_exists_coe_eq_heckeT.lean`,
`Theorems/Thm_CuspForm_exists_coe_eq_heckeU.lean`,
`P2M/Sol/S_CuspForm_exists_coe_eq_heckeU.lean`,
`Theorems/Thm_IsIntegral_of_mem_span_of_apply_eq_smul.lean`,
`P2M/Sol/S_IsIntegral_of_mem_span_of_apply_eq_smul.lean`,
`Theorems/Thm_exists_integralClosure_coe_eq_of_isIntegral.lean`,
`P2M/Sol/S_exists_integralClosure_coe_eq_of_isIntegral.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean`,
`P2M/Sol/S_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice.lean`,
`Theorems/Thm_CuspForm_linearIndependent_of_mem_intLattice.lean`,
`P2M/Sol/S_CuspForm_linearIndependent_of_mem_intLattice.lean`,
`Theorems/Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom.lean`,
`P2M/Sol/S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean`,
`P2M/Sol/S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean`,
`P2M/Sol/S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra.lean`,
`Theorems/Thm_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean`, and
`P2M/Sol/S_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import MathlibExt.NumberTheory.ModularForms.NormalizedEigenform
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0
import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0

/-!
# Integrality of the Hecke algebra of cusp forms on `Γ₀(N)`

This file shows that eigenvalues of an endomorphism stabilizing a finitely generated lattice
are algebraic integers, and that, under an integral structure, the Hecke algebra
`CuspForm.heckeAlgebra N k S` is a finite free `ℤ`-module and every ring homomorphism
from it to `ℂ` is the system of eigenvalues of a nonzero cusp form.

## Main statements

* `IsIntegral.of_mem_span_of_apply_eq_smul`: an eigenvalue of a lattice-stabilizing
  endomorphism, on an eigenvector in the span of the lattice, is integral over `ℤ`.
* `CuspForm.linearIndependent_of_mem_intLattice`: `ℤ`-independent lattice vectors are
  `ℂ`-independent.
* `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom`: a character of a
  commutative ring acting faithfully on a finitely generated lattice has an eigenvector.
* `CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul`: every character of
  the Hecke algebra is realized by a nonzero simultaneous eigenform.
* `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra`,
  `CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra`: the Hecke algebra is finite
  and free over `ℤ`.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

section IsIntegral

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def restrLattice (L : Submodule ℤ V) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) :
    Module.End ℤ L :=
  (T.restrictScalars ℤ).restrict hTL

private theorem coe_restrLattice_pow_apply (L : Submodule ℤ V) (T : V →ₗ[ℂ] V)
    (hTL : ∀ x ∈ L, T x ∈ L) (n : ℕ) (x : L) :
    (((restrLattice L T hTL ^ n) x : L) : V) = (T ^ n) (x : V) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, pow_succ, mul_apply_eq_comp]
    rfl

private theorem coe_aeval_restrLattice_apply (L : Submodule ℤ V) (T : V →ₗ[ℂ] V)
    (hTL : ∀ x ∈ L, T x ∈ L) (P : ℤ[X]) (x : L) :
    ((aeval (restrLattice L T hTL) P x : L) : V) = aeval T (P.map (algebraMap ℤ ℂ)) (x : V) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq, Polynomial.map_add, map_add,
      LinearMap.add_apply]
  | monomial n a =>
    rw [aeval_monomial, mul_apply_eq_comp, Module.algebraMap_end_apply, Submodule.coe_smul,
      coe_restrLattice_pow_apply, Polynomial.map_monomial, aeval_monomial, mul_apply_eq_comp,
      Module.algebraMap_end_apply, eq_intCast, Int.cast_smul_eq_zsmul]

/-- Let `T` be a `ℂ`-linear endomorphism stabilizing a finitely generated `ℤ`-lattice `L`.
An eigenvalue of `T` on a nonzero eigenvector in the `ℂ`-span of `L` is integral over `ℤ`. -/
theorem IsIntegral.of_mem_span_of_apply_eq_smul (L : Submodule ℤ V) (hfg : L.FG)
    (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) {v : V}
    (hv : v ∈ Submodule.span ℂ (L : Set V)) (hv0 : v ≠ 0) {c : ℂ} (hTv : T v = c • v) :
    IsIntegral ℤ c := by
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  obtain ⟨P, hPm, hP⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℤ (restrLattice L T hTL)
  have hL : ∀ x ∈ L, aeval T (P.map (algebraMap ℤ ℂ)) x = 0 := by
    intro x hx
    have h := coe_aeval_restrLattice_apply L T hTL P ⟨x, hx⟩
    rw [hP, LinearMap.zero_apply, Submodule.coe_zero] at h
    exact h.symm
  have hker : Submodule.span ℂ (L : Set V) ≤ LinearMap.ker (aeval T (P.map (algebraMap ℤ ℂ))) :=
    Submodule.span_le.mpr fun x hx => LinearMap.mem_ker.mpr (hL x hx)
  have hv' : aeval T (P.map (algebraMap ℤ ℂ)) v = 0 := LinearMap.mem_ker.mp (hker hv)
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hTv, smul_eq_zero] at hv'
  have hroot : (P.map (algebraMap ℤ ℂ)).eval c = 0 := hv'.resolve_right hv0
  exact ⟨P, hPm, by rwa [eval_map] at hroot⟩

end IsIntegral

namespace CuspForm

private theorem coeff_add_aux {N : ℕ} {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    (qExpansion 1 ((f + g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ℍ → ℂ)).coeff n
      = (qExpansion 1 (f : ℍ → ℂ)).coeff n + (qExpansion 1 (g : ℍ → ℂ)).coeff n := by
  simp only [FunLike.coe_add]
  rw [ModularForm.qExpansion_add one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) f g, map_add]

/-- The first `B` `q`-expansion coefficients, as a `ℂ`-linear map. -/
private def truncC (N : ℕ) (k : ℤ) (B : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] (Fin B → ℂ) where
  toFun f i := (qExpansion 1 (f : ℍ → ℂ)).coeff i
  map_add' f g := by funext i; exact coeff_add_aux f g i
  map_smul' c f := by funext i; exact CuspForm.qCoeff_smul c f i

private def sturmBC (N : ℕ) (k : ℤ) : ℕ := (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 + 1

private theorem truncC_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (truncC N k (sturmBC N k)) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  have hmf : (ModularFormClass.modularForm f :
      ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 N _ fun n hn ↦ ?_
    have hcoeff := congrFun hf ⟨n, Nat.lt_succ_of_le hn⟩
    simpa [truncC] using hcoeff
  have hcoe : (f : ℍ → ℂ) = 0 := by
    have harg := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) k ↦
      (F : ℍ → ℂ)) hmf
    simpa using harg
  exact DFunLike.coe_injective (hcoe.trans (FunLike.coe_zero).symm)

/-- For `N ≠ 0`, cusp forms on `Γ₀(N)` in the integral lattice that are linearly independent over
`ℤ` are linearly independent over `ℂ`. -/
theorem linearIndependent_of_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (f : Fin n → CuspForm (CongruenceSubgroup.Gamma0 N) k) (hf : ∀ i, f i ∈ intLattice N k)
    (h : LinearIndependent ℤ f) : LinearIndependent ℂ f := by
  classical
  have hint : ∀ i (j : ℕ), ∃ m : ℤ, (qExpansion 1 (f i : ℍ → ℂ)).coeff j = (m : ℂ) :=
    fun i => (mem_intLattice_iff (f i)).mp (hf i)
  choose v hv using hint
  set B := sturmBC N k
  let w : Fin n → Fin B → ℤ := fun i j => v i j
  have htr : ∀ i, truncC N k B (f i) = algebraMap ℤ ℂ ∘ w i := by
    intro i
    funext j
    change (qExpansion 1 (f i : ℍ → ℂ)).coeff j = algebraMap ℤ ℂ (v i j)
    rw [hv, eq_intCast]
  have hw : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : truncC N k B (∑ i, c i • f i) = 0 := by
      rw [map_sum]
      funext j
      rw [Finset.sum_apply, Pi.zero_apply]
      have := congrFun hc j
      rw [Finset.sum_apply, Pi.zero_apply] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      calc ∑ i, (truncC N k B (c i • f i)) j
          = ∑ i, ((c i : ℂ) * algebraMap ℤ ℂ (w i j)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, Pi.smul_apply, smul_eq_mul, htr]
            rfl
        _ = algebraMap ℤ ℂ (∑ i, c i * w i j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, eq_intCast, eq_intCast]
        _ = 0 := by rw [this, map_zero]
    have hzero : ∑ i, c i • f i = 0 := truncC_injective N k (by rw [h0, map_zero])
    exact Fintype.linearIndependent_iff.mp h c hzero
  have hC : LinearIndependent ℂ (fun i => algebraMap ℤ ℂ ∘ w i) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℂ)).mpr hw
  have hC' : LinearIndependent ℂ (truncC N k B ∘ f) := by
    convert hC using 1
    funext i
    exact htr i
  exact LinearIndependent.of_comp _ hC'

end CuspForm

section Eigenvector

open Ideal

private theorem isTorsionFree_int_of_module (K V : Type*) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] : Module.IsTorsionFree ℤ V where
  isSMulRegular n hn a b hab := by
    have h : (n : K) • a = (n : K) • b := by
      simpa only [Int.cast_smul_eq_zsmul] using hab
    exact smul_right_injective V (Int.cast_ne_zero.mpr hn.ne_zero) h

private theorem isTorsionFree_int_submodule (K V : Type*) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (L : Submodule ℤ V) : Module.IsTorsionFree ℤ L := by
  have := isTorsionFree_int_of_module K V
  exact Function.Injective.moduleIsTorsionFree Subtype.val Subtype.val_injective fun _ _ => rfl

private theorem exists_ne_zero_forall_mem_smul_eq_zero_aux
    {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ 𝔪, a • v = 0 := by
  classical
  have hinj : Function.Injective (Algebra.lsmul K K V : A →ₐ[K] Module.End K V) := by
    intro a b hab
    refine FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_
    have := congrArg (fun f : Module.End K V => f v) hab
    simpa using this
  have : Module.Finite K A :=
    Module.Finite.of_injective (Algebra.lsmul K K V : A →ₐ[K] Module.End K V).toLinearMap hinj
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsNoetherianRing A := inferInstance
  have : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  have hann : Module.annihilator A V = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    rw [Module.mem_annihilator] at ha
    refine (Ideal.mem_bot).mpr (FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_)
    rw [ha v, zero_smul]
  have hmin : 𝔪 ∈ (Module.annihilator A V).minimalPrimes := by
    rw [hann]
    refine ⟨⟨h𝔪.isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hle
    have hqmax : q.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal q).mp hq
    exact (hqmax.eq_of_le h𝔪.ne_top hle).ge
  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A V hmin
  change (⊥ : Submodule A V).IsAssociatedPrime 𝔪 at hass
  rw [Submodule.isAssociatedPrime_iff] at hass
  obtain ⟨-, x, hx⟩ := hass
  refine ⟨x, ?_, fun a ha => ?_⟩
  · rintro rfl
    apply h𝔪.ne_top
    rw [hx, eq_top_iff]
    intro a _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  · have : a ∈ (⊥ : Submodule A V).colon {x} := hx ▸ ha
    rw [Submodule.mem_colon_singleton] at this
    simpa using this

private theorem exists_ne_zero_forall_smul_eq_algHom_aux
    {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V]
    (χ : A →ₐ[K] K) : ∃ v : V, v ≠ 0 ∧ ∀ a : A, a • v = χ a • v := by
  have hsurj : Function.Surjective χ := fun c => ⟨algebraMap K A c, χ.commutes c⟩
  have hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurj
  obtain ⟨v, hv, hkill⟩ :=
    exists_ne_zero_forall_mem_smul_eq_zero_aux (K := K) (V := V) (RingHom.ker χ) hmax
  refine ⟨v, hv, fun a => ?_⟩
  have hmem : a - algebraMap K A (χ a) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have := hkill _ hmem
  rw [sub_smul, sub_eq_zero, algebraMap_smul] at this
  exact this

open scoped TensorProduct in
private theorem exists_ne_zero_of_free_quotient_aux
    {K V T D : Type*} [Field K] [AddCommGroup V] [Module K V] [CommRing T] [CommRing D]
    [Module.Finite ℤ D] [Module.Free ℤ D]
    (ρ : T →+* Module.End K V) (χ : T →+* K) (π : T →+* D)
    (χbar : D →+* K) (hχ : ∀ t, χbar (π t) = χ t)
    (e : D →+ V) (heT : ∀ t d, e (π t * d) = ρ t (e d))
    (hind : ∀ (n : ℕ) (d : Fin n → D), LinearIndependent ℤ d →
      LinearIndependent K (fun i => e (d i))) :
    ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v := by
  classical
  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ D)
  let b : Module.Basis (Fin n) ℤ D := (Module.Free.chooseBasis ℤ D).reindex (Fintype.equivFin _)
  have : Module.Finite K (K ⊗[ℤ] D) := inferInstance
  let χA : K ⊗[ℤ] D →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K) χbar.toIntAlgHom fun _ _ => Commute.all _ _
  have hχA : ∀ (c : K) (d : D), χA (c ⊗ₜ d) = c * χbar d := fun c d =>
    Algebra.TensorProduct.lift_tmul _ _ _ c d
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_smul_eq_algHom_aux (K := K) (V := K ⊗[ℤ] D) χA
  let eZ : D →ₗ[ℤ] V := e.toIntLinearMap
  let ι : K ⊗[ℤ] D →ₗ[K] V :=
    TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : K →ₗ[K] K).smulRight eZ)
  have hι : ∀ (c : K) (d : D), ι (c ⊗ₜ d) = c • e d := fun c d => rfl
  have hιT : ∀ (t : T) (a : K ⊗[ℤ] D), ρ t (ι a) = ι ((1 : K) ⊗ₜ (π t) * a) := by
    intro t a
    induction a using TensorProduct.inductionOn with
    | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hι, hι, map_smul, heT]
    | add a₁ a₂ h₁ h₂ => rw [mul_add, map_add, map_add, map_add, h₁, h₂]
  let bA : Module.Basis (Fin n) K (K ⊗[ℤ] D) := Algebra.TensorProduct.basis K b
  have hyK : LinearIndependent K (fun i => e (b i)) := hind n b b.linearIndependent
  have hιb : ∀ i, ι (bA i) = e (b i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, hι, one_smul]
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [← bA.sum_repr a] at ha ⊢
    simp only [map_sum, map_smul, hιb] at ha
    have hc := Fintype.linearIndependent_iff.mp hyK _ ha
    simp [hc]
  refine ⟨ι w, fun h => hw0 (hιinj (by rw [h, map_zero])), fun t => ?_⟩
  have hw' := hw ((1 : K) ⊗ₜ π t)
  rw [smul_eq_mul] at hw'
  rw [hιT, hw', map_smul, hχA, one_mul, hχ]

/-- Let a commutative ring `T` act through `ρ` on a vector space `V` over a field `K` of
characteristic zero, stabilizing a finitely generated `ℤ`-lattice `L` on which it acts
faithfully and whose `ℤ`-independent families stay `K`-independent. Then every character
`χ : T →+* K` is the system of eigenvalues of some nonzero `v ∈ V`. -/
theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom {K V T : Type*} [Field K]
    [CharZero K] [AddCommGroup V] [Module K V] [CommRing T] (ρ : T →+* Module.End K V)
    (L : Submodule ℤ V) (hL : L.FG) (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L)
    (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0)
    (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y →
      LinearIndependent K y)
    (χ : T →+* K) : ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v := by
  classical
  let modTV : Module T V := Module.compHom V ρ
  have hsmulT : ∀ (t : T) (v : V), t • v = ρ t v := fun _ _ => rfl
  let LT : Submodule T V :=
    { carrier := L
      add_mem' := fun ha hb => L.add_mem ha hb
      zero_mem' := L.zero_mem
      smul_mem' := fun t x hx => hstab t x hx }
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  let eL : L ≃ₗ[ℤ] LT :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite ℤ LT := Module.Finite.equiv eL
  have : Module.Finite T LT := Module.Finite.of_restrictScalars_finite ℤ T LT
  have : Module.IsTorsionFree ℤ LT := by
    have := isTorsionFree_int_submodule K V L
    exact Function.Injective.moduleIsTorsionFree eL.symm eL.symm.injective fun _ _ => rfl
  have : Module.Free ℤ LT := Module.free_of_finite_type_torsion_free'
  let ψ : T →+* Module.End ℤ LT := Module.toModuleEnd ℤ (S := T) LT
  have hψ : Function.Injective ψ.toAddMonoidHom.toIntLinearMap := by
    intro s t hst
    rw [← sub_eq_zero]
    apply hfaith
    intro x hx
    have h := congrArg (fun f : Module.End ℤ LT => ((f ⟨x, hx⟩ : LT) : V)) hst
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_toIntLinearMap,
      AddMonoidHom.coe_ofClass, ψ, Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply] at h
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    exact h
  have : Module.Finite ℤ T := Module.Finite.of_injective _ hψ
  have : IsNoetherianRing T := IsNoetherianRing.of_finite ℤ T
  have hann : Module.annihilator T LT = ⊥ := by
    refine eq_bot_iff.mpr fun t ht => ?_
    rw [Module.mem_annihilator] at ht
    refine (Ideal.mem_bot).mpr (hfaith t fun x hx => ?_)
    have := congrArg Subtype.val (ht ⟨x, hx⟩)
    simp only [SetLike.val_smul, ZeroMemClass.coe_zero] at this
    exact this
  have : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨𝔓, h𝔓min, h𝔓le⟩ :=
    Ideal.exists_minimalPrimes_le (show (⊥ : Ideal T) ≤ RingHom.ker χ from bot_le)
  have hmin : 𝔓 ∈ (Module.annihilator T LT).minimalPrimes := by rw [hann]; exact h𝔓min
  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes T LT hmin
  change (⊥ : Submodule T LT).IsAssociatedPrime 𝔓 at hass
  rw [Submodule.isAssociatedPrime_iff] at hass
  obtain ⟨h𝔓prime, x, hx⟩ := hass
  have : 𝔓.IsPrime := h𝔓prime
  have hmem𝔓 : ∀ t : T, t ∈ 𝔓 ↔ ρ t (x : V) = 0 := by
    intro t
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Subtype.ext_iff]
    exact Iff.rfl
  have hxL : (x : V) ∈ L := x.2
  let e : (T ⧸ 𝔓) →ₗ[T] V :=
    Submodule.liftQ 𝔓 (LinearMap.toSpanSingleton T V (x : V)) (fun t ht => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hsmulT]
      exact (hmem𝔓 t).mp ht)
  have he_mk : ∀ t : T, e (Ideal.Quotient.mk 𝔓 t) = ρ t x := fun t => rfl
  have he_inj : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [he_mk] at hd
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem𝔓 t).mpr hd)
  have he_memL : ∀ d, e d ∈ L := by
    intro d
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [he_mk]
    exact hstab t x hxL
  have he_smul : ∀ (t : T) (d : T ⧸ 𝔓), e (Ideal.Quotient.mk 𝔓 t * d) = ρ t (e d) := by
    intro t d
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [← map_mul, he_mk, he_mk, map_mul]
    rfl
  have : Module.Finite ℤ (T ⧸ 𝔓) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  have : Module.IsTorsionFree ℤ (T ⧸ 𝔓) := by
    have := isTorsionFree_int_of_module K V
    exact Function.Injective.moduleIsTorsionFree e he_inj fun r m => map_zsmul e r m
  have : Module.Free ℤ (T ⧸ 𝔓) := Module.free_of_finite_type_torsion_free'
  refine exists_ne_zero_of_free_quotient_aux ρ χ (Ideal.Quotient.mk 𝔓)
    (Ideal.Quotient.lift 𝔓 χ fun t ht => h𝔓le ht) (fun t => Ideal.Quotient.lift_mk 𝔓 χ _)
    e.toAddMonoidHom (fun t d => he_smul t d) ?_
  intro n d hd
  have h1 : LinearIndependent ℤ (fun i => e (d i)) := by
    have hker : LinearMap.ker (e.restrictScalars ℤ) = ⊥ := LinearMap.ker_eq_bot.mpr he_inj
    exact hd.map' (e.restrictScalars ℤ) hker
  exact hfree n _ (fun i => he_memL _) h1

end Eigenvector

namespace CuspForm

/-- For `N ≠ 0`, under an integral structure in weight `k ≥ 1`, every ring homomorphism from the
Hecke algebra to `ℂ` is the system of Hecke eigenvalues of a nonzero cusp form. -/
theorem HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul {N : ℕ} [NeZero N] {k : ℤ}
    (hN : HasIntegralStructure N k) (hk : 1 ≤ k) {S : Set ℕ}
    (χ : heckeAlgebra N k S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧
      ∀ t : heckeAlgebra N k S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f :=
  Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom (K := ℂ)
    (heckeAlgebra N k S).val.toRingHom (intLattice N k) (intLattice_fg N k)
    (fun t _ hf => mem_intLattice_of_mem_heckeAlgebra hk t.2 hf)
    (fun _ ht => Subtype.ext (LinearMap.ext_on (g := 0) hN fun f hf => ht f hf))
    (fun n f hf hind => linearIndependent_of_mem_intLattice n f hf hind) χ

/-- For `N ≠ 0`, under an integral structure, the Hecke algebra in weight `k ≥ 1` is a finitely
generated `ℤ`-module. -/
theorem HasIntegralStructure.moduleFinite_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ}
    (hN : HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) :
    Module.Finite ℤ (heckeAlgebra N k S) := by
  classical
  let V := CuspForm (CongruenceSubgroup.Gamma0 N) k
  let L : Submodule ℤ V := intLattice N k
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr (intLattice_fg N k)
  have := isTorsionFree_int_submodule ℂ V L
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ψ : heckeAlgebra N k S →ₗ[ℤ] Module.End ℤ L :=
    { toFun := fun t => ((t : Module.End ℂ V).restrictScalars ℤ).restrict
        (fun f hf => mem_intLattice_of_mem_heckeAlgebra hk t.2 hf)
      map_add' := fun t t' => by ext f; rfl
      map_smul' := fun n t => by ext f; rfl }
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    apply Subtype.ext
    refine LinearMap.ext_on (g := 0) hN fun f hf => ?_
    rw [LinearMap.zero_apply]
    calc (t : Module.End ℂ V) f = ((ψ t ⟨f, hf⟩ : L) : V) := rfl
      _ = 0 := by rw [ht]; rfl
  exact Module.Finite.of_injective ψ hψ

/-- For `N ≠ 0`, under an integral structure, the Hecke algebra in weight `k ≥ 1` is a free
`ℤ`-module. -/
theorem HasIntegralStructure.moduleFree_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ}
    (hN : HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) :
    Module.Free ℤ (heckeAlgebra N k S) := by
  have := hN.moduleFinite_heckeAlgebra hk S
  have := isTorsionFree_int_of_module ℂ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k))
  have : Module.IsTorsionFree ℤ (heckeAlgebra N k S) :=
    Function.Injective.moduleIsTorsionFree Subtype.val Subtype.val_injective fun _ _ => rfl
  exact Module.free_of_finite_type_torsion_free'

end CuspForm

end
