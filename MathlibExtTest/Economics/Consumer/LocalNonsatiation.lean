/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.ExpenditureDuality
public import MathlibExt.Economics.SecondWelfareTheorem

@[expose] public section

/-! Local nonsatiation has one definition. The consumer name `Economics.Consumer.LocallyNonsatiated`
is the same constant, and the second-welfare predicate is its specialization to `ℝ^L_+`, so a
hypothesis from either API feeds the other without conversion. -/

/-- The consumer-theory name is an alias of the shared constant, not a second definition. -/
example : @Economics.Consumer.LocallyNonsatiated =
    @MathlibExt.Economics.Consumer.LocallyNonsatiated := rfl

namespace MathlibExtTest.Economics.Consumer.LocalNonsatiation

/-- The second-welfare predicate is the shared predicate on `consumptionSet L`. -/
theorem secondWelfare_locallyNonsatiated_iff {L : Type*} [Fintype L] (v : (L → ℝ) → ℝ) :
    MathlibExt.Economics.SecondWelfareTheorem.LocallyNonsatiated v ↔
      MathlibExt.Economics.Consumer.LocallyNonsatiated v
        (MathlibExt.Economics.SecondWelfareTheorem.consumptionSet L) :=
  Iff.rfl

/-- Composition: a local-nonsatiation hypothesis stated with the second-welfare API proves
expenditure duality on the consumption set `ℝ^L_+` directly. -/
theorem expenditure_indirectUtility_eq_of_secondWelfare {L : Type*} [Fintype L]
    {u : (L → ℝ) → ℝ} {p : L → ℝ} {w : ℝ} {x : L → ℝ}
    (hLNS : MathlibExt.Economics.SecondWelfareTheorem.LocallyNonsatiated u)
    (hx : _root_.Economics.Consumer.IsMarshallianDemand u
      (MathlibExt.Economics.SecondWelfareTheorem.consumptionSet L) p w x) :
    _root_.Economics.Consumer.expenditure u
        (MathlibExt.Economics.SecondWelfareTheorem.consumptionSet L) p
        (_root_.Economics.Consumer.indirectUtility u
          (MathlibExt.Economics.SecondWelfareTheorem.consumptionSet L) p w) = w :=
  _root_.Economics.Consumer.expenditure_indirectUtility_eq hLNS hx

/-- Composition in the other direction: a consumer-theory hypothesis on `ℝ^L_+` is a
second-welfare hypothesis. -/
example {L : Type*} [Fintype L] {v : (L → ℝ) → ℝ}
    (h : MathlibExt.Economics.Consumer.LocallyNonsatiated v
      (MathlibExt.Economics.SecondWelfareTheorem.consumptionSet L)) :
    MathlibExt.Economics.SecondWelfareTheorem.LocallyNonsatiated v := h

section BothOpen

open _root_.Economics.Consumer MathlibExt.Economics.Consumer

/-- With both consumer namespaces open, `LocallyNonsatiated` is unambiguous: both names resolve
to the one constant. -/
example {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ) (X : Set (ι → ℝ))
    (h : LocallyNonsatiated u X) : MathlibExt.Economics.Consumer.LocallyNonsatiated u X := h

end BothOpen

end MathlibExtTest.Economics.Consumer.LocalNonsatiation
