/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.StandardSmooth.DVR

@[expose] public section

example (L : Type*) [CommRing L] [IsLocalRing L] [IsNoetherianRing L] {ϖ : L}
    (hreg : IsSMulRegular L ϖ)
    (hmax : IsLocalRing.maximalIdeal L = Ideal.span {ϖ}) :
    IsDomain L :=
  IsLocalRing.isDomain_of_maximalIdeal_eq_span hreg hmax

example (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A] (p : Ideal A) [p.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime p),
      IsDiscreteValuationRing (Localization.AtPrime p) :=
  Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
    (k := k) p

example (k : Type*) [Field k] :
    (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k)))).IsMaximal := by
  have hsurj : Function.Surjective
      (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k))) :=
    fun b => ⟨MvPolynomial.C b, by simp⟩
  exact RingHom.ker_isMaximal_of_surjective
    (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k))).toRingHom hsurj

example (k : Type*) [Field k] :
    (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k)))).IsPrime := by
  have hsurj : Function.Surjective
      (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k))) :=
    fun b => ⟨MvPolynomial.C b, by simp⟩
  exact (RingHom.ker_isMaximal_of_surjective
    (MvPolynomial.aeval (R := k) (fun _ : Fin 1 => (0 : k))).toRingHom hsurj).isPrime
