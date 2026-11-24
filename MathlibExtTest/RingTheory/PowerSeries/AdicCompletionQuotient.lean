/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.AdicCompletionQuotient

@[expose] public section

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+*
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}),
      ∀ o : O, e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})
          (PowerSeries.C o) :=
  PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C ϖ hϖ

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+*
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}),
      e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) ϖ) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})
          (PowerSeries.X : PowerSeries O) := by
  obtain ⟨e, he⟩ :=
    PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C ϖ hϖ
  refine ⟨e, ?_⟩
  rw [he ϖ, Ideal.Quotient.eq,
    show PowerSeries.C ϖ - (PowerSeries.X : PowerSeries O) =
      -((PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ) by ring]
  exact neg_mem (Ideal.subset_span rfl)
