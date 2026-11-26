/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.LinearAlgebra.KernelCokernelMap
public import MathlibExt.RingTheory.Length.AnnihilatorQuotient
public import MathlibExt.RingTheory.Length.Exact
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Euler characteristic of multiplication by a ring element

For r in a commutative ring R and an R-module M, let μ_r be multiplication by r. When ker(μ_r)
and coker(μ_r) have finite length, define χ_r(M) = ℓ_R(coker μ_r) − ℓ_R(ker μ_r). The cokernel
is canonically M/rM.

The invariant is preserved by module equivalences and by the stated surjective scalar changes
or ring equivalences. It is additive in short exact module sequences with finite
multiplication kernel and cokernel lengths. On a prime quotient R/p it is zero when r ∈ p, and
otherwise is the length of the principal quotient. The ring and module universe levels are
independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

namespace Module

open scoped Pointwise

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Finite kernel and cokernel lengths for multiplication.

This condition records finite R-length of ker(μ_r) and of M/rM. -/
structure ElementEulerFiniteLength (r : R) : Prop where
/-- Finite length of the multiplication kernel.

The R-length of ker(μ_r : M → M) is not infinite. -/
  kernel_ne_top : Module.length R (LinearMap.lsmul R M r).ker ≠ ⊤
/-- Finite length of the multiplication cokernel.

The R-length of M modulo the range of μ_r is not infinite. -/
  cokernel_ne_top : Module.length R
    (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤

/-- The cokernel-minus-kernel Euler characteristic of one element.

Using finite multiplication lengths, define χ_r(M) as the integer length of M/rM minus that of
ker μ_r. -/
noncomputable def elementEulerCharacteristic
    (r : R) (_h : ElementEulerFiniteLength R M r) : ℤ :=
  (Module.length R (M ⧸ (LinearMap.lsmul R M r).range)).toNat -
    (Module.length R (LinearMap.lsmul R M r).ker).toNat

/-- The one-element Euler characteristic respects equality of scalars.

Equal elements r=s give the same Euler characteristic, with either finite-length witness. -/
theorem elementEulerCharacteristic_congr
    {r s : R} (hrs : r = s)
    (hr : ElementEulerFiniteLength R M r)
    (hs : ElementEulerFiniteLength R M s) :
    elementEulerCharacteristic R M r hr =
      elementEulerCharacteristic R M s hs := by
  subst s
  rfl

/-- The range of multiplication is the scalar multiple submodule.

The range of μ_r on M is r times the full submodule. -/
theorem range_lsmul_eq_smul_top (r : R) :
    (LinearMap.lsmul R M r).range = r • (⊤ : Submodule R M) := by
  rw [LinearMap.range_eq_map, Submodule.pointwise_smul_def]
  rfl

section ChangeRing

variable (S : Type u) [CommRing S]
variable (A : Type v) [CommRing A] [Algebra S A]

/-- Scalar multiplication agrees with restriction of algebra multiplication.

For an algebra S → A, multiplication by s on the S-module A equals the restriction of
multiplication by its image in A. -/
theorem lsmul_eq_restrictScalars_algebraMap (s : S) :
    LinearMap.lsmul S A s =
      (LinearMap.lsmul A A (algebraMap S A s)).restrictScalars S := by
  ext x
  simp [Algebra.smul_def]

/-- The kernel comparison for restricted scalar multiplication.

The S-linear multiplication kernel on A is canonically equivalent to the kernel of
multiplication by the image of s as an A-linear map, restricted to S. -/
noncomputable def lsmulKernelRestrictScalarsEquiv (s : S) :
    (LinearMap.lsmul S A s).ker ≃ₗ[S]
      (LinearMap.lsmul A A (algebraMap S A s)).ker :=
  (show (LinearMap.lsmul S A s).ker ≃ₗ[S]
      (LinearMap.lsmul A A
        (algebraMap S A s)).ker.restrictScalars S from
    LinearEquiv.ofEq _ _ (by
      rw [lsmul_eq_restrictScalars_algebraMap,
        LinearMap.ker_restrictScalars])).trans
    (((LinearMap.lsmul A A
      (algebraMap S A s)).ker.restrictScalarsEquiv S).restrictScalars S)

/-- The cokernel comparison for restricted scalar multiplication.

The S-module quotient by multiplication by s agrees with the quotient by multiplication by its
image in A, with scalars restricted. -/
noncomputable def lsmulCokernelRestrictScalarsEquiv (s : S) :
    (A ⧸ (LinearMap.lsmul S A s).range) ≃ₗ[S]
      A ⧸ (LinearMap.lsmul A A (algebraMap S A s)).range :=
  Submodule.quotEquivOfEq _ _ (by
    rw [lsmul_eq_restrictScalars_algebraMap,
      LinearMap.range_restrictScalars]) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv S
      (LinearMap.lsmul A A (algebraMap S A s)).range

/-- Multiplication kernel lengths agree under a surjective algebra map.

For surjective S → A, the length over S of the scalar kernel on A equals its length over A. -/
theorem length_lsmul_kernel_eq_of_surjective
    (s : S) (h : Function.Surjective (algebraMap S A)) :
    Module.length S (LinearMap.lsmul S A s).ker =
      Module.length A
        (LinearMap.lsmul A A (algebraMap S A s)).ker := by
  rw [(lsmulKernelRestrictScalarsEquiv S A s).length_eq,
    Module.length_eq_of_surjective h]

/-- Multiplication cokernel lengths agree under a surjective algebra map.

For surjective S → A, the scalar cokernel on A has the same length over S and A. -/
theorem length_lsmul_cokernel_eq_of_surjective
    (s : S) (h : Function.Surjective (algebraMap S A)) :
    Module.length S (A ⧸ (LinearMap.lsmul S A s).range) =
      Module.length A
        (A ⧸ (LinearMap.lsmul A A (algebraMap S A s)).range) := by
  rw [(lsmulCokernelRestrictScalarsEquiv S A s).length_eq,
    Module.length_eq_of_surjective h]

/-- Finite multiplication lengths pass through a surjective scalar change.

For surjective S → A, finite kernel and cokernel lengths of s on A as an S-module give the
corresponding finite A-lengths for its image. -/
theorem ElementEulerFiniteLength.changeRingOfSurjective
    (s : S) (hmap : Function.Surjective (algebraMap S A))
    (h : ElementEulerFiniteLength S A s) :
    ElementEulerFiniteLength A A (algebraMap S A s) where
  kernel_ne_top := by
    rw [← length_lsmul_kernel_eq_of_surjective S A s hmap]
    exact h.kernel_ne_top
  cokernel_ne_top := by
    rw [← length_lsmul_cokernel_eq_of_surjective S A s hmap]
    exact h.cokernel_ne_top

/-- The element Euler characteristic under surjective scalar change.

For surjective S → A, χ_s(A) over S equals χ_{image(s)}(A) over A. -/
theorem elementEulerCharacteristic_changeRingOfSurjective
    (s : S) (hmap : Function.Surjective (algebraMap S A))
    (h : ElementEulerFiniteLength S A s) :
    elementEulerCharacteristic S A s h =
      elementEulerCharacteristic A A (algebraMap S A s)
        (h.changeRingOfSurjective S A s hmap) := by
  unfold elementEulerCharacteristic
  rw [length_lsmul_cokernel_eq_of_surjective S A s hmap,
    length_lsmul_kernel_eq_of_surjective S A s hmap]

end ChangeRing

/-- An ideal element acts by zero on its quotient.

If r ∈ p, multiplication by r on R/p is the zero map. -/
theorem quotient_lsmul_eq_zero_of_mem
    (p : Ideal R) {r : R} (hr : r ∈ p) :
    LinearMap.lsmul R (R ⧸ p) r = 0 := by
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk p r * x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]

/-- An element outside a prime acts injectively on the prime quotient.

For prime p and r ∉ p, multiplication by r on R/p is injective. -/
theorem quotient_lsmul_injective_of_not_mem
    (p : Ideal R) [p.IsPrime] {r : R} (hr : r ∉ p) :
    Function.Injective (LinearMap.lsmul R (R ⧸ p) r) := by
  let Q := R ⧸ p
  have hrQ : Ideal.Quotient.mk p r ≠ 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).not.mpr hr
  have hQ : Function.Injective
      (LinearMap.lsmul Q Q (Ideal.Quotient.mk p r)) :=
    LinearMap.lsmul_injective hrQ
  intro x y hxy
  apply hQ
  exact hxy

/-- The multiplication cokernel is the scalar quotient.

Identify M modulo the range of μ_r with QuotSMulTop r M, the quotient by rM. -/
noncomputable def elementCokernelEquivQuotSMulTop (r : R) :
    (M ⧸ (LinearMap.lsmul R M r).range) ≃ₗ[R] QuotSMulTop r M :=
  Submodule.quotEquivOfEq _ _ (range_lsmul_eq_smul_top R M r)

/-- A finite-length module has finite multiplication lengths.

If M has finite R-length, both the kernel and cokernel of μ_r have finite length for every r. -/
theorem ElementEulerFiniteLength.of_module_length
    (r : R) (hM : Module.length R M ≠ ⊤) :
    ElementEulerFiniteLength R M r where
  kernel_ne_top :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective
        (LinearMap.lsmul R M r).ker.subtype
        (Submodule.injective_subtype _))
  cokernel_ne_top :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_surjective
        (LinearMap.lsmul R M r).range.mkQ
        (Submodule.mkQ_surjective _))

/-- Finite multiplication lengths from injectivity and a finite quotient.

If μ_r is injective and M/rM has finite length, its kernel and cokernel satisfy
ElementEulerFiniteLength. -/
theorem ElementEulerFiniteLength.of_injective
    (r : R) (hr : Function.Injective (LinearMap.lsmul R M r))
    (hquot : Module.length R
      (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤) :
    ElementEulerFiniteLength R M r where
  kernel_ne_top := by
    rw [LinearMap.ker_eq_bot.mpr hr, Module.length_bot]
    exact ENat.zero_ne_top
  cokernel_ne_top := hquot

/-- The Euler characteristic of injective multiplication.

If μ_r is injective, χ_r(M) is the natural-number length of M/rM. -/
theorem elementEulerCharacteristic_eq_quotient_of_injective
    (r : R) (hr : Function.Injective (LinearMap.lsmul R M r))
    (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h =
      (Module.length R
        (M ⧸ (LinearMap.lsmul R M r).range)).toNat := by
  unfold elementEulerCharacteristic
  rw [LinearMap.ker_eq_bot.mpr hr, Module.length_bot]
  simp

/-- Zero multiplication has zero Euler characteristic.

If μ_r is zero and its kernel and cokernel have finite length, their lengths coincide and
χ_r(M)=0. -/
theorem elementEulerCharacteristic_eq_zero_of_lsmul_eq_zero
    (r : R) (hr : LinearMap.lsmul R M r = 0)
    (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h = 0 := by
  have hker : (LinearMap.lsmul R M r).ker = ⊤ :=
    LinearMap.ker_eq_top.mpr hr
  have hrange : (LinearMap.lsmul R M r).range = ⊥ :=
    LinearMap.range_eq_bot.mpr hr
  let eker : (LinearMap.lsmul R M r).ker ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ hker).trans Submodule.topEquiv
  let ecoker : (M ⧸ (LinearMap.lsmul R M r).range) ≃ₗ[R] M :=
    (LinearMap.lsmul R M r).range.quotEquivOfEqBot hrange
  unfold elementEulerCharacteristic
  rw [eker.length_eq, ecoker.length_eq, sub_self]

/-- The Euler contribution of an ideal quotient containing the element.

If r ∈ p and the quotient multiplication lengths are finite, χ_r(R/p)=0. -/
theorem elementEulerCharacteristic_quotient_prime_eq_zero_of_mem
    (p : Ideal R) (r : R) (hr : r ∈ p)
    (h : ElementEulerFiniteLength R (R ⧸ p) r) :
    elementEulerCharacteristic R (R ⧸ p) r h = 0 :=
  elementEulerCharacteristic_eq_zero_of_lsmul_eq_zero R (R ⧸ p) r
    (quotient_lsmul_eq_zero_of_mem R p hr) h

/-- The Euler contribution of a prime quotient excluding the element.

For prime p with r ∉ p, χ_r(R/p) is the length of (R/p)/r(R/p), under the stated finiteness
condition. -/
theorem elementEulerCharacteristic_quotient_prime_eq_length_of_not_mem
    (p : Ideal R) [p.IsPrime] (r : R) (hr : r ∉ p)
    (h : ElementEulerFiniteLength R (R ⧸ p) r) :
    elementEulerCharacteristic R (R ⧸ p) r h =
      (Module.length R
        ((R ⧸ p) ⧸ (LinearMap.lsmul R (R ⧸ p) r).range)).toNat :=
  elementEulerCharacteristic_eq_quotient_of_injective R (R ⧸ p) r
    (quotient_lsmul_injective_of_not_mem R p hr) h

/-- An associated prime containing the element is maximal.

For a finitely generated M, if p is associated to M, contains r and M/rM has finite length,
then p is maximal. -/
theorem isMaximal_of_isAssociatedPrime_of_cokernel_length_ne_top
    [Module.Finite R M] (r : R) (p : PrimeSpectrum R)
    (hp : IsAssociatedPrime p.asIdeal M) (hr : r ∈ p.asIdeal)
    (hcoker : Module.length R
      (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤) :
    p.asIdeal.IsMaximal := by
  have hpSupport : p ∈ Module.support R M :=
    Module.mem_support_iff_of_finite.mpr (by
      simpa only [Submodule.annihilator_top] using hp.annihilator_le)
  have hpZero : p ∈ PrimeSpectrum.zeroLocus ({r} : Set R) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hr
  have hpCoker : p ∈ Module.support R
      (M ⧸ (LinearMap.lsmul R M r).range) := by
    rw [(elementCokernelEquivQuotSMulTop R M r).support_eq,
      Module.support_quotSMulTop]
    exact ⟨hpSupport, hpZero⟩
  exact Module.isMaximal_of_mem_support_of_length_ne_top R
    (M ⧸ (LinearMap.lsmul R M r).range) hcoker p hpCoker

/-- Finite multiplication lengths on an associated prime quotient.

Over a noetherian ring and for finitely generated M, finite length of M/rM gives finite kernel
and cokernel lengths for multiplication by r on R/p for every associated prime p. -/
theorem ElementEulerFiniteLength.quotient_prime_of_isAssociatedPrime
    [IsNoetherianRing R] [Module.Finite R M]
    (r : R) (p : PrimeSpectrum R)
    (hp : IsAssociatedPrime p.asIdeal M)
    (hcoker : Module.length R
      (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤) :
    ElementEulerFiniteLength R (R ⧸ p.asIdeal) r := by
  have hpAnn : Module.annihilator R M ≤ p.asIdeal := by
    simpa only [Submodule.annihilator_top] using hp.annihilator_le
  have hcokerPrime : Module.length R
      ((R ⧸ p.asIdeal) ⧸
        (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range) ≠ ⊤ := by
    apply Module.length_ne_top_of_forall_isMaximal_mem_support R
    intro q hq
    have hq' : q ∈ Module.support R (QuotSMulTop r (R ⧸ p.asIdeal)) := by
      rw [← (elementCokernelEquivQuotSMulTop
        R (R ⧸ p.asIdeal) r).support_eq]
      exact hq
    rw [Module.support_quotSMulTop] at hq'
    obtain ⟨hqQuotient, hqr⟩ := hq'
    have hpq : p.asIdeal ≤ q.asIdeal := by
      have hqAnn := Module.mem_support_iff_of_finite.mp hqQuotient
      simpa only [Ideal.annihilator_quotient] using hqAnn
    have hqM : q ∈ Module.support R M :=
      Module.mem_support_iff_of_finite.mpr (hpAnn.trans hpq)
    have hqMainQuotient : q ∈ Module.support R (QuotSMulTop r M) := by
      rw [Module.support_quotSMulTop]
      exact ⟨hqM, hqr⟩
    have hqMain : q ∈ Module.support R
        (M ⧸ (LinearMap.lsmul R M r).range) := by
      rw [(elementCokernelEquivQuotSMulTop R M r).support_eq]
      exact hqMainQuotient
    exact Module.isMaximal_of_mem_support_of_length_ne_top R
      (M ⧸ (LinearMap.lsmul R M r).range) hcoker q hqMain
  by_cases hrp : r ∈ p.asIdeal
  · have hzero : LinearMap.lsmul R (R ⧸ p.asIdeal) r = 0 :=
      quotient_lsmul_eq_zero_of_mem R p.asIdeal hrp
    have hrange :
        (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range = ⊥ :=
      LinearMap.range_eq_bot.mpr hzero
    let e : ((R ⧸ p.asIdeal) ⧸
        (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range) ≃ₗ[R]
        (R ⧸ p.asIdeal) :=
      (LinearMap.lsmul R (R ⧸ p.asIdeal) r).range.quotEquivOfEqBot hrange
    have hquotient : Module.length R (R ⧸ p.asIdeal) ≠ ⊤ := by
      rw [← e.length_eq]
      exact hcokerPrime
    exact ElementEulerFiniteLength.of_module_length R
      (R ⧸ p.asIdeal) r hquotient
  · exact ElementEulerFiniteLength.of_injective R (R ⧸ p.asIdeal) r
      (quotient_lsmul_injective_of_not_mem R p.asIdeal hrp) hcokerPrime

private theorem lsmul_naturality
    {N : Type w} [AddCommGroup N] [Module R N]
    (r : R) (f : M →ₗ[R] N) :
    (LinearMap.lsmul R N r).comp f =
      f.comp (LinearMap.lsmul R M r) := by
  ext x
  simp

/-- Regular multiplication cokernel lengths under a ring equivalence.

A ring equivalence R ≃ S identifies the length of R/rR with the length of S/e(r)S. -/
theorem length_lsmul_cokernel_ringEquiv
    {S : Type w} [CommRing S] (e : R ≃+* S) (r : R) :
    Module.length R
        (R ⧸ (LinearMap.lsmul R R r).range) =
      Module.length S
        (S ⧸ (LinearMap.lsmul S S (e r)).range) := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let eAlg : R ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv fun _ => rfl
  let ecoker :
      (R ⧸ (LinearMap.lsmul R R r).range) ≃ₗ[R]
        S ⧸ (LinearMap.lsmul R S r).range :=
    LinearMap.cokerEquiv
      (LinearMap.lsmul R R r) (LinearMap.lsmul R S r)
      eAlg.toLinearEquiv
      (lsmul_naturality R R r eAlg.toLinearMap)
  have hr : algebraMap R S r = e r := by
    change e.toRingHom r = e r
    rfl
  calc
    Module.length R (R ⧸ (LinearMap.lsmul R R r).range) =
        Module.length R (S ⧸ (LinearMap.lsmul R S r).range) :=
      ecoker.length_eq
    _ = Module.length S
        (S ⧸ (LinearMap.lsmul S S (algebraMap R S r)).range) :=
      length_lsmul_cokernel_eq_of_surjective R S r e.surjective
    _ = Module.length S
        (S ⧸ (LinearMap.lsmul S S (e r)).range) := by
      cases hr
      rfl

/-- Finite multiplication lengths under a module equivalence.

An R-linear equivalence M ≃ N carries finite kernel and cokernel length data for μ_r from M to
N. -/
theorem ElementEulerFiniteLength.equiv
    {N : Type w} [AddCommGroup N] [Module R N]
    (r : R) (e : M ≃ₗ[R] N) (h : ElementEulerFiniteLength R M r) :
    ElementEulerFiniteLength R N r where
  kernel_ne_top := by
    rw [← (LinearMap.kerEquiv
      (LinearMap.lsmul R M r) (LinearMap.lsmul R N r) e
        (lsmul_naturality R M r e.toLinearMap)).length_eq]
    exact h.kernel_ne_top
  cokernel_ne_top := by
    rw [← (LinearMap.cokerEquiv
      (LinearMap.lsmul R M r) (LinearMap.lsmul R N r) e
        (lsmul_naturality R M r e.toLinearMap)).length_eq]
    exact h.cokernel_ne_top

/-- The Euler characteristic is invariant under module equivalence.

For an R-linear equivalence M ≃ N, χ_r(M)=χ_r(N). -/
theorem elementEulerCharacteristic_equiv
    {N : Type w} [AddCommGroup N] [Module R N]
    (r : R) (e : M ≃ₗ[R] N) (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h =
      elementEulerCharacteristic R N r (h.equiv R M r e) := by
  unfold elementEulerCharacteristic
  rw [(LinearMap.cokerEquiv
      (LinearMap.lsmul R M r) (LinearMap.lsmul R N r) e
        (lsmul_naturality R M r e.toLinearMap)).length_eq,
    (LinearMap.kerEquiv
      (LinearMap.lsmul R M r) (LinearMap.lsmul R N r) e
        (lsmul_naturality R M r e.toLinearMap)).length_eq]

/-- Finite regular multiplication lengths under a ring equivalence.

A ring equivalence sends finite multiplication data for s on its regular source module to the
corresponding data for e(s) on the regular target module. -/
theorem ElementEulerFiniteLength.ringEquiv
    {S : Type u} {A : Type v} [CommRing S] [CommRing A]
    (e : S ≃+* A) (s : S) (h : ElementEulerFiniteLength S S s) :
    ElementEulerFiniteLength A A (e s) := by
  let _ : Algebra S A := e.toRingHom.toAlgebra
  let eAlg : S ≃ₐ[S] A :=
    AlgEquiv.ofRingEquiv fun _ => rfl
  let hSA := h.equiv S S s eAlg.toLinearEquiv
  have hs : algebraMap S A s = e s := by
    change e.toRingHom s = e s
    rfl
  rw [← hs]
  exact hSA.changeRingOfSurjective S A s e.surjective

/-- The regular one-element Euler characteristic under a ring equivalence.

For e : S ≃ A, χ_s(S)=χ_{e(s)}(A) with the transported finite-length data. -/
theorem elementEulerCharacteristic_ringEquiv
    {S : Type u} {A : Type v} [CommRing S] [CommRing A]
    (e : S ≃+* A) (s : S) (h : ElementEulerFiniteLength S S s) :
    elementEulerCharacteristic S S s h =
      elementEulerCharacteristic A A (e s) (h.ringEquiv e s) := by
  let _ : Algebra S A := e.toRingHom.toAlgebra
  let eAlg : S ≃ₐ[S] A :=
    AlgEquiv.ofRingEquiv fun _ => rfl
  let hSA := h.equiv S S s eAlg.toLinearEquiv
  let hA := hSA.changeRingOfSurjective S A s e.surjective
  have hs : algebraMap S A s = e s := by
    change e.toRingHom s = e s
    rfl
  calc
    elementEulerCharacteristic S S s h =
        elementEulerCharacteristic S A s hSA :=
      elementEulerCharacteristic_equiv S S s eAlg.toLinearEquiv h
    _ = elementEulerCharacteristic A A (algebraMap S A s) hA :=
      elementEulerCharacteristic_changeRingOfSurjective
        S A s e.surjective hSA
    _ = elementEulerCharacteristic A A (e s) (h.ringEquiv e s) := by
      cases hs
      rfl

section Additivity

variable {M₁ M₂ M₃ : Type v}
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable [AddCommGroup M₃] [Module R M₃]

/-- Finite multiplication lengths in a short exact sequence.

For an injective–exact–surjective sequence M₁ → M₂ → M₃, finite kernel and cokernel lengths on
M₁ and M₃ imply them on M₂. -/
theorem ElementEulerFiniteLength.of_shortExact
    (r : R) (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (h₁ : ElementEulerFiniteLength R M₁ r)
    (h₃ : ElementEulerFiniteLength R M₃ r) :
    ElementEulerFiniteLength R M₂ r := by
  let d₁ := LinearMap.lsmul R M₁ r
  let d₂ := LinearMap.lsmul R M₂ r
  let d₃ := LinearMap.lsmul R M₃ r
  have hcomm₁₂ : d₂.comp i = i.comp d₁ :=
    lsmul_naturality R M₁ r i
  have hcomm₂₃ : d₃.comp p = p.comp d₂ :=
    lsmul_naturality R M₂ r p
  exact
    { kernel_ne_top := Module.length_ne_top_of_exact R
        (LinearMap.mapKer d₁ d₂ i hcomm₁₂)
        (LinearMap.mapKer d₂ d₃ p hcomm₂₃)
        (LinearMap.exact_mapKer d₁ d₂ d₃ i p hi hip
          hcomm₁₂ hcomm₂₃)
        h₁.kernel_ne_top h₃.kernel_ne_top
      cokernel_ne_top := Module.length_ne_top_of_exact R
        (LinearMap.mapCoker d₁ d₂ i hcomm₁₂)
        (LinearMap.mapCoker d₂ d₃ p hcomm₂₃)
        (LinearMap.exact_mapCoker d₁ d₂ d₃ i p hp hip
          hcomm₁₂ hcomm₂₃)
        h₁.cokernel_ne_top h₃.cokernel_ne_top }

/-- A finite multiplication cokernel descends to a quotient module.

For a surjective module map M₂ → M₃, finite length of M₂/rM₂ implies finite length of M₃/rM₃. -/
theorem elementCokernel_length_ne_top_of_surjective
    (r : R) (p : M₂ →ₗ[R] M₃) (hp : Function.Surjective p)
    (h₂ : Module.length R
      (M₂ ⧸ (LinearMap.lsmul R M₂ r).range) ≠ ⊤) :
    Module.length R
      (M₃ ⧸ (LinearMap.lsmul R M₃ r).range) ≠ ⊤ := by
  have hcomm := lsmul_naturality R M₂ r p
  have hsurj := LinearMap.mapCoker_surjective
    (LinearMap.lsmul R M₂ r) (LinearMap.lsmul R M₃ r)
      p hcomm hp
  exact ne_top_of_le_ne_top h₂
    (Module.length_le_of_surjective _ hsurj)

/-- Finite length of the left multiplication cokernel.

In a short exact sequence, finite length of the middle cokernel and the right kernel of
multiplication by r implies finite length of the left cokernel. -/
theorem elementLeftCokernel_length_ne_top_of_shortExact
    (r : R) (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (h₂coker : Module.length R
      (M₂ ⧸ (LinearMap.lsmul R M₂ r).range) ≠ ⊤)
    (h₃kernel : Module.length R
      (LinearMap.lsmul R M₃ r).ker ≠ ⊤) :
    Module.length R
      (M₁ ⧸ (LinearMap.lsmul R M₁ r).range) ≠ ⊤ := by
  let d₁ := LinearMap.lsmul R M₁ r
  let d₂ := LinearMap.lsmul R M₂ r
  let d₃ := LinearMap.lsmul R M₃ r
  have hcomm₁₂ : d₂.comp i = i.comp d₁ :=
    lsmul_naturality R M₁ r i
  have hcomm₂₃ : d₃.comp p = p.comp d₂ :=
    lsmul_naturality R M₂ r p
  let c₁₂ : (M₁ ⧸ d₁.range) →ₗ[R] (M₂ ⧸ d₂.range) :=
    LinearMap.mapCoker d₁ d₂ i hcomm₁₂
  let delta : d₃.ker →ₗ[R] (M₁ ⧸ d₁.range) :=
    SnakeLemma.δ' d₁ d₂ d₃ i p hip i p hip
      hcomm₁₂.symm hcomm₂₃.symm
      d₃.ker.subtype d₃.exact_subtype_ker_map
      d₁.range.mkQ d₁.exact_map_mkQ_range hp hi
  have hdeltac_exact : Function.Exact delta c₁₂ := by
    apply SnakeLemma.exact_δ'_left d₁ d₂ d₃ i p hip i p hip
      hcomm₁₂.symm hcomm₂₃.symm
      d₃.ker.subtype d₃.exact_subtype_ker_map
      d₁.range.mkQ d₁.exact_map_mkQ_range
      d₂.range.mkQ d₂.exact_map_mkQ_range hp hi c₁₂
    · ext x
      rfl
    · exact Submodule.mkQ_surjective d₁.range
  exact Module.length_ne_top_of_exact R delta c₁₂ hdeltac_exact
    h₃kernel h₂coker

/-- Additivity of the one-element Euler characteristic.

For a short exact sequence and finite multiplication lengths on all three terms,
χ_r(M₂)=χ_r(M₁)+χ_r(M₃). -/
theorem elementEulerCharacteristic_additive
    (r : R) (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (h₁ : ElementEulerFiniteLength R M₁ r)
    (h₂ : ElementEulerFiniteLength R M₂ r)
    (h₃ : ElementEulerFiniteLength R M₃ r) :
    elementEulerCharacteristic R M₂ r h₂ =
      elementEulerCharacteristic R M₁ r h₁ +
        elementEulerCharacteristic R M₃ r h₃ := by
  let d₁ := LinearMap.lsmul R M₁ r
  let d₂ := LinearMap.lsmul R M₂ r
  let d₃ := LinearMap.lsmul R M₃ r
  have hcomm₁₂ : d₂.comp i = i.comp d₁ :=
    lsmul_naturality R M₁ r i
  have hcomm₂₃ : d₃.comp p = p.comp d₂ :=
    lsmul_naturality R M₂ r p
  let k₁₂ : d₁.ker →ₗ[R] d₂.ker :=
    LinearMap.mapKer d₁ d₂ i hcomm₁₂
  let k₂₃ : d₂.ker →ₗ[R] d₃.ker :=
    LinearMap.mapKer d₂ d₃ p hcomm₂₃
  let c₁₂ : (M₁ ⧸ d₁.range) →ₗ[R] (M₂ ⧸ d₂.range) :=
    LinearMap.mapCoker d₁ d₂ i hcomm₁₂
  let c₂₃ : (M₂ ⧸ d₂.range) →ₗ[R] (M₃ ⧸ d₃.range) :=
    LinearMap.mapCoker d₂ d₃ p hcomm₂₃
  let delta : d₃.ker →ₗ[R] (M₁ ⧸ d₁.range) :=
    SnakeLemma.δ' d₁ d₂ d₃ i p hip i p hip
      hcomm₁₂.symm hcomm₂₃.symm
      d₃.ker.subtype d₃.exact_subtype_ker_map
      d₁.range.mkQ d₁.exact_map_mkQ_range hp hi
  have hk₁₂_injective : Function.Injective k₁₂ :=
    LinearMap.mapKer_injective d₁ d₂ i hcomm₁₂ hi
  have hc₂₃_surjective : Function.Surjective c₂₃ :=
    LinearMap.mapCoker_surjective d₂ d₃ p hcomm₂₃ hp
  have hk_exact : Function.Exact k₁₂ k₂₃ :=
    LinearMap.exact_mapKer d₁ d₂ d₃ i p hi hip
      hcomm₁₂ hcomm₂₃
  have hkdelta_exact : Function.Exact k₂₃ delta := by
    apply SnakeLemma.exact_δ'_right d₁ d₂ d₃ i p hip i p hip
      hcomm₁₂.symm hcomm₂₃.symm
      d₂.ker.subtype d₂.exact_subtype_ker_map
      d₃.ker.subtype d₃.exact_subtype_ker_map
      d₁.range.mkQ d₁.exact_map_mkQ_range hp hi k₂₃
    · ext x
      rfl
    · exact Submodule.injective_subtype d₃.ker
  have hdeltac_exact : Function.Exact delta c₁₂ := by
    apply SnakeLemma.exact_δ'_left d₁ d₂ d₃ i p hip i p hip
      hcomm₁₂.symm hcomm₂₃.symm
      d₃.ker.subtype d₃.exact_subtype_ker_map
      d₁.range.mkQ d₁.exact_map_mkQ_range
      d₂.range.mkQ d₂.exact_map_mkQ_range hp hi c₁₂
    · ext x
      rfl
    · exact Submodule.mkQ_surjective d₁.range
  have hc_exact : Function.Exact c₁₂ c₂₃ :=
    LinearMap.exact_mapCoker d₁ d₂ d₃ i p hp hip
      hcomm₁₂ hcomm₂₃
  have hsix := Module.alternating_length_six_of_exact R
    k₁₂ k₂₃ delta c₁₂ c₂₃
    hk₁₂_injective hc₂₃_surjective hk_exact hkdelta_exact
    hdeltac_exact hc_exact h₂.kernel_ne_top h₃.kernel_ne_top
    h₁.cokernel_ne_top h₂.cokernel_ne_top
  dsimp [d₁, d₂, d₃] at hsix
  unfold elementEulerCharacteristic
  omega

end Additivity

end Module
