/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.DVRQuotient
public import MathlibExt.RingTheory.Valuation.HeightOne

@[expose] public section

example {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}).IsPrime ∧
    IsPrincipalIdealRing (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) ∧
    IsLocalRing (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) ∧
    Irreducible (Ideal.Quotient.mk
      (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)})
      (PowerSeries.C ϖ)) :=
  PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ e he

example {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    ∃ maximalIdeal : Ideal (PowerSeries W ⧸
        Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}),
      maximalIdeal = Ideal.span {(Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)})
        (PowerSeries.C ϖ))} := by
  obtain ⟨hdom, hdvr, hirr⟩ :=
    PowerSeries.isDiscreteValuationRing_quotient_span_X_sub_C_pow_of_irreducible
      ϖ hϖ e he
  let _ : IsDomain (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) := hdom
  let _ : IsDiscreteValuationRing (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) := hdvr
  exact ⟨IsLocalRing.maximalIdeal _, hirr.maximalIdeal_eq⟩

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (PowerSeries O ⧸
        Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsDiscreteValuationRing (PowerSeries O ⧸
        Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsAdicComplete
        (IsLocalRing.maximalIdeal (PowerSeries O ⧸
          Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
        (PowerSeries O ⧸
          Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})),
      Irreducible (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})
        (PowerSeries.C ϖ)) :=
  PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖ

example {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ V : ValuationSubring K, IsPrincipalIdealRing V ∧ V ≠ ⊤ ∧
      ∀ x : K, x ∈ V ↔
        ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r :=
  IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one K p hp
