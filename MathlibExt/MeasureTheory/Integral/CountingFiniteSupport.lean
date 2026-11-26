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

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Counting integral of a finitely supported vector function

Let `X` be measurable with measurable singletons and `E` a real Banach space. If `f : X → E`
vanishes outside a finite set `s`, then `∫ f dcount=Σ_x∈s f(x)`.

The source may be uncountable; no topology or global sigma-finiteness is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace MeasureTheory

universe uX uE

variable {X : Type uX} [MeasurableSpace X] [MeasurableSingletonClass X]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Finite sum formula for a counting integral.** Let `X` be a measurable space with
measurable singletons, `E` a complete real normed space, `f : X → E` and `s : Finset X`.
If `f(x)=0` outside `s`, then `∫ f dcount=Σ_x∈s f(x)`, without countability of `X`. -/
theorem integral_count_eq_finset_sum (f : X → E) (s : Finset X)
    (hsupport : ∀ x : X, x ∉ s → f x = 0) :
    (∫ x : X, f x ∂Measure.count) = ∑ x ∈ s, f x := by
  classical
  have hFinite (t : Finset X) : IntegrableOn f (t : Set X) Measure.count := by
    induction t using Finset.induction_on with
    | empty => simp only [Finset.coe_empty, integrableOn_empty]
    | insert x t _ ht =>
      have hSet : ((insert x t : Finset X) : Set X) = ({x} : Set X) ∪ (t : Set X) := by
        ext y
        simp only [Finset.mem_coe, Finset.mem_insert, Set.mem_union, Set.mem_singleton_iff]
      rw [hSet]
      apply integrableOn_union.mpr
      refine ⟨?_, ht⟩
      exact integrableOn_singleton (μ := Measure.count) (f := f) (x := x)
        (hx := by rw [Measure.count_singleton]; exact ENNReal.one_lt_top)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hsupport x hx),
    setIntegral_finset s (hFinite s)]
  simp only [count_real_singleton, one_smul]

end MeasureTheory
