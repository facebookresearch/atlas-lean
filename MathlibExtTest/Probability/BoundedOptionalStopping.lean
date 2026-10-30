/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BoundedOptionalStopping

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace MathlibExtTest.Probability.BoundedOptionalStopping

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m} [SigmaFiniteFiltration μ ℱ]
  {f : ℕ → Ω → ℝ} {L M : Ω → ℕ∞}

/-- The submartingale conditional inequality restates with the exact public
signature. -/
example (hsub : Submartingale f ℱ μ)
    (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M) (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | hL.measurableSpace] :=
  hsub.stoppedValue_le_condExp_stoppedValue hL hM hLM hbdd

/-- The supermartingale conditional inequality restates with the exact public
signature. -/
example (hsup : Supermartingale f ℱ μ)
    (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M) (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    μ[stoppedValue f M | hL.measurableSpace] ≤ᵐ[μ] stoppedValue f L :=
  hsup.condExp_stoppedValue_le_stoppedValue hL hM hLM hbdd

/-- Taking `L = M`: the stopped value at a bounded stopping time is almost
surely at most its own conditional expectation given `ℱ_τ` (in fact equal
to it, since it is `ℱ_τ`-measurable). -/
example (hsub : Submartingale f ℱ μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime ℱ τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] :
    stoppedValue f τ ≤ᵐ[μ] μ[stoppedValue f τ | hτ.measurableSpace] :=
  hsub.stoppedValue_le_condExp_stoppedValue hτ hτ le_rfl hbdd

/-- For a martingale, the two inequalities combine to the optional-sampling
equality `stoppedValue f L =ᵐ[μ] μ[stoppedValue f M | ℱ_L]`, recovering
Mathlib's `stoppedValue_ae_eq_condExp_of_le` in the bounded case. -/
example (hmart : Martingale f ℱ μ)
    (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M) (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    stoppedValue f L =ᵐ[μ] μ[stoppedValue f M | hL.measurableSpace] :=
  (hmart.submartingale.stoppedValue_le_condExp_stoppedValue hL hM hLM hbdd).antisymm
    (hmart.supermartingale.condExp_stoppedValue_le_stoppedValue hL hM hLM hbdd)

/-- Concrete instance: the constant process `fun _ => c` is a martingale, so
the inequality applies to it at any two bounded stopping times. -/
example (c : ℝ)
    (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M) (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N)
    [SigmaFinite (μ.trim hL.measurableSpace_le)] :
    stoppedValue (fun _ : ℕ => fun _ : Ω => c) L ≤ᵐ[μ]
      μ[stoppedValue (fun _ : ℕ => fun _ : Ω => c) M | hL.measurableSpace] :=
  (martingale_const ℱ μ c).submartingale.stoppedValue_le_condExp_stoppedValue
    hL hM hLM hbdd

/-- Concrete instance with constant stopping times: for the constant process,
stopped values are both `c`, and the inequality is `c ≤ᵐ[μ] μ[c | ℱ_0]`. -/
example (c : ℝ) {N : ℕ} :
    stoppedValue (fun _ : ℕ => fun _ : Ω => c) (fun _ => ((0 : ℕ) : ℕ∞)) ≤ᵐ[μ]
      μ[stoppedValue (fun _ : ℕ => fun _ : Ω => c) (fun _ => ((N : ℕ) : ℕ∞)) |
        (isStoppingTime_const ℱ 0).measurableSpace] :=
  (martingale_const ℱ μ c).submartingale.stoppedValue_le_condExp_stoppedValue
    (isStoppingTime_const ℱ 0) (isStoppingTime_const ℱ N)
    (fun _ => Nat.cast_le.mpr (Nat.zero_le N)) (fun _ => le_rfl)

end MathlibExtTest.Probability.BoundedOptionalStopping
