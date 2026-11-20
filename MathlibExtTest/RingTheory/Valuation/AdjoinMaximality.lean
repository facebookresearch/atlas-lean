/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.AdjoinMaximality

@[expose] public section

open IsLocalRing

-- Consumer with the original binders, generalized to `Type*`.
example {F : Type*} [Field F]
    (A₀ : Type*) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ F]
    (O : Subring F) [IsLocalRing ↥O] [IsNoetherianRing ↥O]
    (hAO : ∀ a : A₀, algebraMap A₀ F a ∈ O)
    (hAOloc : ∀ a : A₀, a ∈ maximalIdeal A₀ →
      (⟨algebraMap A₀ F a, hAO a⟩ : ↥O) ∈ maximalIdeal ↥O)
    (B : Subalgebra A₀ F) (hBfg : B.FG)
    (hcomp : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime →
      Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      ∃ V : ValuationSubring F,
        (∀ f : F, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ f * (c : F) = (b : F)) ∧
        ¬ (O ≤ V.toSubring ∧ ∀ g : ↥O, g ∈ maximalIdeal ↥O → (g : F) ∈ V.nonunits))
    (ℜ : Ideal ↥(Algebra.adjoin ↥O (B : Set F))) [ℜ.IsPrime]
    (hℜ : ∀ g : ↥O, g ∈ maximalIdeal ↥O ↔
      algebraMap ↥O ↥(Algebra.adjoin ↥O (B : Set F)) g ∈ ℜ) :
    ℜ.IsMaximal :=
  Subring.isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring
    A₀ O hAO hAOloc B hBfg hcomp ℜ hℜ

universe w

-- Higher-universe consumer.
example {F : Type w} [Field F]
    (A₀ : Type w) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ F]
    (O : Subring F) [IsLocalRing ↥O] [IsNoetherianRing ↥O]
    (hAO : ∀ a : A₀, algebraMap A₀ F a ∈ O)
    (hAOloc : ∀ a : A₀, a ∈ maximalIdeal A₀ →
      (⟨algebraMap A₀ F a, hAO a⟩ : ↥O) ∈ maximalIdeal ↥O)
    (B : Subalgebra A₀ F) (hBfg : B.FG)
    (hcomp : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime →
      Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      ∃ V : ValuationSubring F,
        (∀ f : F, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ f * (c : F) = (b : F)) ∧
        ¬ (O ≤ V.toSubring ∧ ∀ g : ↥O, g ∈ maximalIdeal ↥O → (g : F) ∈ V.nonunits))
    (ℜ : Ideal ↥(Algebra.adjoin ↥O (B : Set F))) [ℜ.IsPrime]
    (hℜ : ∀ g : ↥O, g ∈ maximalIdeal ↥O ↔
      algebraMap ↥O ↥(Algebra.adjoin ↥O (B : Set F)) g ∈ ℜ) :
    ℜ.IsMaximal :=
  Subring.isMaximal_of_liesOver_adjoin_of_forall_not_isMaximal_valuationSubring
    A₀ O hAO hAOloc B hBfg hcomp ℜ hℜ
