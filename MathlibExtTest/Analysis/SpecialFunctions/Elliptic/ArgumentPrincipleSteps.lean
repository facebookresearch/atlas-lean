/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ArgumentPrincipleSteps

/-!
# Tests for the steps towards the argument principle for elliptic functions

Compile-time examples exercising `PeriodPair.IsEllipticFunction.logDeriv`,
`parallelogramBoundaryIntegral` with its vanishing for periodic integrands, and the finiteness of
zeros and poles in a closed parallelogram.
-/

@[expose] public section

namespace PeriodPair

/-- The logarithmic derivative of a constant function is elliptic. -/
example (L : PeriodPair) (c : ℂ) : L.IsEllipticFunction (logDeriv fun _ : ℂ ↦ c) :=
  (IsEllipticFunction.const L c).logDeriv

/-- The logarithmic derivative of a constant function is the zero function. -/
example (c : ℂ) : logDeriv (fun _ : ℂ ↦ c) = fun _ ↦ 0 := by
  funext z
  simp [logDeriv_apply]

/-- The derivative of the Weierstrass function is elliptic. -/
example (L : PeriodPair) : L.IsEllipticFunction (deriv L.weierstrassP) :=
  IsEllipticFunction.deriv ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

/-- The logarithmic derivative of the Weierstrass function is elliptic. -/
example (L : PeriodPair) : L.IsEllipticFunction (logDeriv L.weierstrassP) :=
  IsEllipticFunction.logDeriv ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

/-- The boundary integral of the constant function `1` over a period parallelogram is zero. -/
example (L : PeriodPair) (z₀ : ℂ) :
    parallelogramBoundaryIntegral (fun _ ↦ (1 : ℂ)) z₀ L.ω₁ L.ω₂ = 0 :=
  (isLatticePeriodic_const L 1).parallelogramBoundaryIntegral_eq_zero z₀

/-- The boundary integral of a constant over any parallelogram is zero, for arbitrary sides. -/
example (c z₀ ω₁ ω₂ : ℂ) : parallelogramBoundaryIntegral (fun _ ↦ c) z₀ ω₁ ω₂ = 0 :=
  Function.Periodic.parallelogramBoundaryIntegral_eq_zero (fun _ ↦ rfl) (fun _ ↦ rfl) z₀

/-- The boundary integral of the Weierstrass function over a period parallelogram is zero, for
every vertex `z₀`, including `z₀ = 0`, where all four vertices are poles of the Weierstrass
function (the integral is then the totalised sum of four interval integrals). -/
example (L : PeriodPair) (z₀ : ℂ) :
    parallelogramBoundaryIntegral L.weierstrassP z₀ L.ω₁ L.ω₂ = 0 :=
  IsLatticePeriodic.parallelogramBoundaryIntegral_eq_zero L.periodic_weierstrassP z₀

/-- A nonzero constant has finitely many zeros and poles (in fact none) in any closed period
parallelogram; the example checks the finiteness statement. -/
example (L : PeriodPair) (c z₀ : ℂ) (hc : c ≠ 0) :
    {P : ℂ | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      P = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂ ∧ meromorphicOrderAt (fun _ ↦ c) P ≠ 0}.Finite :=
  (IsEllipticFunction.const L c).finite_closedParallelogram_inter_order_ne_zero
    (fun z ↦ by simp [meromorphicOrderAt_const, hc]) z₀

/-- The identity function has finitely many zeros and poles in every closed parallelogram. -/
example (z₀ ω₁ ω₂ : ℂ) :
    {P : ℂ | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      P = z₀ + t₁ • ω₁ + t₂ • ω₂ ∧ meromorphicOrderAt (fun z : ℂ ↦ z) P ≠ 0}.Finite :=
  Meromorphic.finite_closedParallelogram_inter_order_ne_zero
    (fun z ↦ analyticAt_id.meromorphicAt)
    (fun P ↦ by
      by_cases hP : P = 0
      · subst hP
        simp
      · exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
          analyticAt_id.meromorphicAt).2
          ((continuousAt_id.eventually_ne hP).filter_mono nhdsWithin_le_nhds)) z₀ ω₁ ω₂

end PeriodPair
