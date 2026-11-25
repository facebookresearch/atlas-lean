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
# Euler characteristic of multiplication by one element

For an element `r : R` acting on an `R`-module `M`, the two-term Euler
characteristic is the length of the cokernel of multiplication by `r` minus
the length of its kernel.  The module snake lemma and the six-term
finite-length telescope show that this invariant is additive in short exact
sequences carrying the compatible scalar action.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

namespace Module

open scoped Pointwise

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Explicit finite-length data for the kernel and cokernel of
multiplication by one element. -/
structure ElementEulerFiniteLength (r : R) : Prop where
  kernel_ne_top : Module.length R (LinearMap.lsmul R M r).ker ≠ ⊤
  cokernel_ne_top : Module.length R
    (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤

/-- Cokernel-minus-kernel Euler characteristic of multiplication by one
element. -/
noncomputable def elementEulerCharacteristic
    (r : R) (_h : ElementEulerFiniteLength R M r) : ℤ :=
  (Module.length R (M ⧸ (LinearMap.lsmul R M r).range)).toNat -
    (Module.length R (LinearMap.lsmul R M r).ker).toNat

/-- The Euler characteristic is insensitive to replacing the acting element
and its finiteness witness along an equality. -/
theorem elementEulerCharacteristic_congr
    {r s : R} (hrs : r = s)
    (hr : ElementEulerFiniteLength R M r)
    (hs : ElementEulerFiniteLength R M s) :
    elementEulerCharacteristic R M r hr =
      elementEulerCharacteristic R M s hs := by
  subst s
  rfl

/-- The range of multiplication by one element is its pointwise multiple of
the top submodule. -/
theorem range_lsmul_eq_smul_top (r : R) :
    (LinearMap.lsmul R M r).range = r • (⊤ : Submodule R M) := by
  rw [LinearMap.range_eq_map, Submodule.pointwise_smul_def]
  rfl

section ChangeRing

variable (S : Type u) [CommRing S]
variable (A : Type v) [CommRing A] [Algebra S A]

/-- Multiplication by a scalar from the source ring is the restriction of
multiplication by its image in the target ring. -/
theorem lsmul_eq_restrictScalars_algebraMap (s : S) :
    LinearMap.lsmul S A s =
      (LinearMap.lsmul A A (algebraMap S A s)).restrictScalars S := by
  ext x
  simp [Algebra.smul_def]

/-- The multiplication kernels before and after changing from a source ring
to an algebra are linearly equivalent over the source ring. -/
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

/-- The multiplication cokernels before and after changing from a source
ring to an algebra are linearly equivalent over the source ring. -/
noncomputable def lsmulCokernelRestrictScalarsEquiv (s : S) :
    (A ⧸ (LinearMap.lsmul S A s).range) ≃ₗ[S]
      A ⧸ (LinearMap.lsmul A A (algebraMap S A s)).range :=
  Submodule.quotEquivOfEq _ _ (by
    rw [lsmul_eq_restrictScalars_algebraMap,
      LinearMap.range_restrictScalars]) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv S
      (LinearMap.lsmul A A (algebraMap S A s)).range

/-- Under a surjective algebra map, the multiplication-kernel length is
unchanged by passing from the source ring to the target ring. -/
theorem length_lsmul_kernel_eq_of_surjective
    (s : S) (h : Function.Surjective (algebraMap S A)) :
    Module.length S (LinearMap.lsmul S A s).ker =
      Module.length A
        (LinearMap.lsmul A A (algebraMap S A s)).ker := by
  rw [(lsmulKernelRestrictScalarsEquiv S A s).length_eq,
    Module.length_eq_of_surjective h]

/-- Under a surjective algebra map, the multiplication-cokernel length is
unchanged by passing from the source ring to the target ring. -/
theorem length_lsmul_cokernel_eq_of_surjective
    (s : S) (h : Function.Surjective (algebraMap S A)) :
    Module.length S (A ⧸ (LinearMap.lsmul S A s).range) =
      Module.length A
        (A ⧸ (LinearMap.lsmul A A (algebraMap S A s)).range) := by
  rw [(lsmulCokernelRestrictScalarsEquiv S A s).length_eq,
    Module.length_eq_of_surjective h]

/-- Transport one-element Euler finiteness data through a surjective change
from the source ring to the target ring. -/
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

/-- The one-element Euler characteristic is invariant under a surjective
change from the source ring to the target ring. -/
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

/-- Multiplication by an element of an ideal is zero on its quotient. -/
theorem quotient_lsmul_eq_zero_of_mem
    (p : Ideal R) {r : R} (hr : r ∈ p) :
    LinearMap.lsmul R (R ⧸ p) r = 0 := by
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk p r * x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]

/-- On a prime quotient, multiplication by an element outside the prime is
injective. -/
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

/-- The cokernel model used by `elementEulerCharacteristic` agrees with the
standard `QuotSMulTop` reduction. -/
noncomputable def elementCokernelEquivQuotSMulTop (r : R) :
    (M ⧸ (LinearMap.lsmul R M r).range) ≃ₗ[R] QuotSMulTop r M :=
  Submodule.quotEquivOfEq _ _ (range_lsmul_eq_smul_top R M r)

/-- Finite length of the ambient module supplies finite-length kernel and
cokernel data for multiplication by every element. -/
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

/-- An injective multiplication map and a finite-length quotient supply the
one-element Euler finiteness data. -/
theorem ElementEulerFiniteLength.of_injective
    (r : R) (hr : Function.Injective (LinearMap.lsmul R M r))
    (hquot : Module.length R
      (M ⧸ (LinearMap.lsmul R M r).range) ≠ ⊤) :
    ElementEulerFiniteLength R M r where
  kernel_ne_top := by
    rw [LinearMap.ker_eq_bot.mpr hr, Module.length_bot]
    exact ENat.zero_ne_top
  cokernel_ne_top := hquot

/-- When multiplication is injective, the one-element Euler characteristic
is the quotient length. -/
theorem elementEulerCharacteristic_eq_quotient_of_injective
    (r : R) (hr : Function.Injective (LinearMap.lsmul R M r))
    (h : ElementEulerFiniteLength R M r) :
    elementEulerCharacteristic R M r h =
      (Module.length R
        (M ⧸ (LinearMap.lsmul R M r).range)).toNat := by
  unfold elementEulerCharacteristic
  rw [LinearMap.ker_eq_bot.mpr hr, Module.length_bot]
  simp

/-- If multiplication by the element is zero, its kernel and cokernel have
equal length and its Euler characteristic vanishes. -/
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

/-- An ideal quotient containing the element contributes zero to its Euler
characteristic, including the prime-filtration special case. -/
theorem elementEulerCharacteristic_quotient_prime_eq_zero_of_mem
    (p : Ideal R) (r : R) (hr : r ∈ p)
    (h : ElementEulerFiniteLength R (R ⧸ p) r) :
    elementEulerCharacteristic R (R ⧸ p) r h = 0 :=
  elementEulerCharacteristic_eq_zero_of_lsmul_eq_zero R (R ⧸ p) r
    (quotient_lsmul_eq_zero_of_mem R p hr) h

/-- A prime-quotient factor on which the element is nonzero contributes its
principal quotient length to the one-element Euler characteristic. -/
theorem elementEulerCharacteristic_quotient_prime_eq_length_of_not_mem
    (p : Ideal R) [p.IsPrime] (r : R) (hr : r ∉ p)
    (h : ElementEulerFiniteLength R (R ⧸ p) r) :
    elementEulerCharacteristic R (R ⧸ p) r h =
      (Module.length R
        ((R ⧸ p) ⧸ (LinearMap.lsmul R (R ⧸ p) r).range)).toNat :=
  elementEulerCharacteristic_eq_quotient_of_injective R (R ⧸ p) r
    (quotient_lsmul_injective_of_not_mem R p hr) h

/-- An associated prime containing the acting element is maximal whenever
the multiplication cokernel has finite length. -/
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

/-- A prime factor arising from an associated prime has finite one-element
Euler data whenever the ambient multiplication cokernel has finite length. -/
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

/-- A ring equivalence preserves the length of a principal multiplication
cokernel. -/
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

/-- Transport one-element Euler finiteness data through a linear
equivalence. -/
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

/-- The one-element Euler characteristic is invariant under linear
equivalence. -/
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

/-- Transport one-element Euler finiteness data across a ring equivalence. -/
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

/-- The one-element Euler characteristic is invariant under ring
equivalence. -/
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

/-- Finite one-element Euler data is closed under extensions. -/
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

/-- A surjection transports finite length of the multiplication cokernel to
the target module. -/
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

/-- In a short exact sequence, finite length of the middle cokernel and the
right kernel implies finite length of the left cokernel. -/
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

/-- The one-element Euler characteristic is additive in a short exact
sequence of modules. -/
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
