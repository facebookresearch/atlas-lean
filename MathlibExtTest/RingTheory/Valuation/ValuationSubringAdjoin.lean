/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.ValuationSubringAdjoin

@[expose] public section

universe u v

-- Consumer with the original binders.
example (L : Type) [Field L] (A₀ : ValuationSubring L)
    (ϖ : ↥A₀) (hϖ : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {ϖ})
    (F : Type) [Field F] [Algebra L F] [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    (x : F) (V V' : ValuationSubring F)
    (hV : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V) (hϖV : algebraMap ↥A₀ F ϖ ∈ V.nonunits)
    (hxV : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V ∧ (Polynomial.aeval x P)⁻¹ ∈ V)
    (hV' : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V') (hϖV' : algebraMap ↥A₀ F ϖ ∈ V'.nonunits)
    (hxV' : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V' ∧ (Polynomial.aeval x P)⁻¹ ∈ V') :
    ∀ e : F, e ∈ IntermediateField.adjoin L ({x} : Set F) → (e ∈ V ↔ e ∈ V') :=
  ValuationSubring.mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem
    L A₀ ϖ hϖ F x V V' hV hϖV hxV hV' hϖV' hxV'

-- Higher-universe consumer.
example (L : Type u) [Field L] (A₀ : ValuationSubring L)
    (ϖ : ↥A₀) (hϖ : IsLocalRing.maximalIdeal ↥A₀ = Ideal.span {ϖ})
    (F : Type v) [Field F] [Algebra L F] [Algebra ↥A₀ F] [IsScalarTower ↥A₀ L F]
    (x : F) (V V' : ValuationSubring F)
    (hV : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V) (hϖV : algebraMap ↥A₀ F ϖ ∈ V.nonunits)
    (hxV : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V ∧ (Polynomial.aeval x P)⁻¹ ∈ V)
    (hV' : ∀ r : ↥A₀, algebraMap ↥A₀ F r ∈ V') (hϖV' : algebraMap ↥A₀ F ϖ ∈ V'.nonunits)
    (hxV' : ∀ P : Polynomial ↥A₀, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval x P ∈ V' ∧ (Polynomial.aeval x P)⁻¹ ∈ V') :
    ∀ e : F, e ∈ IntermediateField.adjoin L ({x} : Set F) → (e ∈ V ↔ e ∈ V') :=
  ValuationSubring.mem_iff_mem_of_mem_adjoin_simple_of_forall_aeval_inv_mem
    L A₀ ϖ hϖ F x V V' hV hϖV hxV hV' hϖV' hxV'
