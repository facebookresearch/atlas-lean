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

/-!
# Torsion-free modules under flat scalar extension

Let R be a commutative domain, S a flat commutative R-algebra and M a torsion-free R-module.
Then S ⊗[R] M is torsion-free over S: regular scalars of S act injectively. The localization
of M over the fraction field of R supplies an embedding into a flat module, and tensoring
preserves that embedding.

For a torsion-free commutative algebra B over a domain S, the map S → B/p is injective for
every minimal prime p of B. If B is also finite over S, this quotient is integral with
faithful scalar action, so ringKrullDim(B/p) = ringKrullDim(S). The scalar, algebra and module
universes are independent.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct nonZeroDivisors
universe u v w
namespace Module.IsTorsionFree

/-- Torsion-freeness preserved by flat base change from a domain.

Let R be a commutative domain, S a flat commutative R-algebra and M a torsion-free R-module.
Then S ⊗[R] M is torsion-free over S, in the sense that every regular scalar of S acts
injectively. -/
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
/-- Injective scalar map to a minimal-prime quotient of a torsion-free algebra.

Let S be a commutative domain and B a torsion-free commutative S-algebra. For p ∈
minimalPrimes B, the scalar map S → B/p is injective. The image in B of a nonzero scalar is a
non-zero-divisor and hence cannot lie in a minimal prime. -/
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

/-- Krull dimension of a finite torsion-free minimal-prime quotient.

Let B be a commutative algebra finite and torsion-free over a commutative domain S. For every
minimal prime p of B, ringKrullDim(B/p) = ringKrullDim(S). The scalar map to the quotient is
injective, and finite generation makes the extension integral. -/
theorem finite_torsionFree_minimalPrime_quotient_dimension
    (S : Type u) (B : Type v) [CommRing S] [IsDomain S] [CommRing B]
    [Algebra S B] [Module.IsTorsionFree S B] [Module.Finite S B]
    (p : Ideal B) (hp : p ∈ minimalPrimes B) :
    ringKrullDim (B ⧸ p) = ringKrullDim S := by
  have hinj := torsionFree_minimalPrime_algebraMap_injective S B p hp
  let _ : FaithfulSMul S (B ⧸ p) := (faithfulSMul_iff_algebraMap_injective S (B ⧸ p)).mpr hinj
  exact Algebra.IsIntegral.ringKrullDim_eq_of_isIntegral

end Algebra
