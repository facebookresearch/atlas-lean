/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.SpanAlgebraNorm

@[expose] public section

universe u v

-- Consumer with the original binders.
example {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] {K : Type u} [Field K] (χ : B →+* K)
    (hχ : Function.Surjective (χ.comp (algebraMap A B))) (g : B)
    (hg : RingHom.ker χ = Ideal.span {g}) (𝔪 : Ideal A)
    (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal]
    (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ 𝔪]
    [IsDomain Aₘ] [IsDiscreteValuationRing Aₘ] :
    Ideal.span {Algebra.norm A g} = 𝔪 :=
  Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing χ hχ g hg 𝔪 h𝔪 Aₘ

-- Higher-universe consumer.
example {A B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] {K : Type v} [Field K] (χ : B →+* K)
    (hχ : Function.Surjective (χ.comp (algebraMap A B))) (g : B)
    (hg : RingHom.ker χ = Ideal.span {g}) (𝔪 : Ideal A)
    (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal]
    (Aₘ : Type v) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ 𝔪]
    [IsDomain Aₘ] [IsDiscreteValuationRing Aₘ] :
    Ideal.span {Algebra.norm A g} = 𝔪 :=
  Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing χ hχ g hg 𝔪 h𝔪 Aₘ
