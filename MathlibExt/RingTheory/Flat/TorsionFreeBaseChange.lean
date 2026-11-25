/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import MathlibExt.RingTheory.KrullDimension.Integral

/-! Torsion-freeness retained by the actual flat scalar extension. -/

@[expose] public section
noncomputable section
open scoped TensorProduct nonZeroDivisors
universe u v w
namespace Module.IsTorsionFree

/-- Actual flat scalar extension preserves torsion-free modules over a domain. -/
theorem baseChange_of_flat_of_domain
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Module.IsTorsionFree S (S ⊗[R] M) := by
  let K := FractionRing R
  let N := LocalizedModule R⁰ M
  let j : M →ₗ[R] N := LocalizedModule.mkLinearMap R⁰ M
  have hj : Function.Injective j :=
    (IsLocalizedModule.injective_iff_isRegular R⁰ j).mpr (fun c =>
      (isRegular_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp c.property)).isSMulRegular)
  let _ : Module.Flat R K := IsLocalization.flat K R⁰
  let _ : Module.Flat R N := Module.Flat.trans R K N
  let e := j.baseChange S
  have he : Function.Injective e :=
    Module.Flat.lTensor_preserves_injective_linearMap j hj
  exact Function.Injective.moduleIsTorsionFree e he (fun r m => e.map_smul r m)


end Module.IsTorsionFree

namespace Algebra
/-- Every actual minimal component of a torsion-free algebra retains the original domain scalars. -/
theorem torsionFree_minimalPrime_algebraMap_injective
    (S : Type u) (B : Type v) [CommRing S] [IsDomain S] [CommRing B]
    [Algebra S B] [Module.IsTorsionFree S B] (p : Ideal B) (hp : p ∈ minimalPrimes B) :
    Function.Injective (algebraMap S (B ⧸ p)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  by_contra hne
  have hmem : algebraMap S B s ∈ p := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hs
  have hreg : algebraMap S B s ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    exact (isRegular_iff_ne_zero.mpr hne).smul_eq_zero_iff_right.mp
      (by simpa only [Algebra.smul_def, mul_comm] using hb)
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hp hreg

/-- Every original minimal-prime quotient of a finite torsion-free algebra has the original base dimension. -/
theorem finite_torsionFree_minimalPrime_quotient_dimension
    (S : Type u) (B : Type v) [CommRing S] [IsDomain S] [CommRing B]
    [Algebra S B] [Module.IsTorsionFree S B] [Module.Finite S B]
    (p : Ideal B) (hp : p ∈ minimalPrimes B) :
    ringKrullDim (B ⧸ p) = ringKrullDim S := by
  have hinj := torsionFree_minimalPrime_algebraMap_injective S B p hp
  let _ : FaithfulSMul S (B ⧸ p) := (faithfulSMul_iff_algebraMap_injective S (B ⧸ p)).mpr hinj
  exact Algebra.IsIntegral.ringKrullDim_eq_of_isIntegral

end Algebra
