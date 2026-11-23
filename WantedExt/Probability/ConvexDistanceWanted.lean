/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.ConvexDistance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Talagrand's convex-distance inequality: wanted

For a probability space `(Ω, μ)`, the product probability `P = μ^{⊗N}` on `Ω^N` and a measurable
set `A ⊆ Ω^N`, Talagrand's Theorem 4.1.1 states
`∫ exp(f_c(A, x)² / 4) dP(x) ≤ 1 / P(A)`, hence `P(f_c(A, ·) ≥ t) ≤ exp(-t² / 4) / P(A)`,
where `f_c` is the convex distance (`MathlibExt.Probability.ConvexDistance.convexDistance`). The
bound does not depend on `N` or on `μ`. It is the source of the concentration inequality for
convex Lipschitz functions of independent bounded variables recorded in
`MathlibExt.Probability.TalagrandConcentrationWanted`.

Measurability. The source treats `f_c(A, ·)` as measurable and otherwise reads the integral as
an upper integral and the probability as an outer probability (its Section 2.1). Below, the
integral is Mathlib's lower Lebesgue integral `∫⁻` (at most the upper integral, so the statement
is implied by the source's), and `P` applied to the possibly non-measurable superlevel set is
Mathlib's outer measure, as in the source.

## References

* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205, Theorem 4.1.1, inequalities (4.1.2) and (4.1.3).
-/

@[expose] public section

namespace MathlibExt.Probability.ConvexDistanceWanted

open MeasureTheory MathlibExt.Probability.ConvexDistance
open scoped ENNReal

/-- **Talagrand's convex-distance inequality** (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Theorem 4.1.1,
(4.1.2)). For every probability measure `μ` on `Ω`, every `N` and every measurable
`A ⊆ Ω^N`, with `P = μ^{⊗N}`: `∫ exp(f_c(A, x)² / 4) dP(x) ≤ 1 / P(A)`. -/
theorem_wanted lintegral_exp_convexDistance_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) {A : Set (Fin N → Ω)}
    (hA : MeasurableSet A) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (convexDistance A x ^ 2 / 4)) ∂Measure.pi (fun _ => μ) ≤
      (Measure.pi (fun _ => μ) A)⁻¹

/-- **Tail form of the convex-distance inequality** (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Theorem 4.1.1,
(4.1.3)). Under the hypotheses of `lintegral_exp_convexDistance_sq_le`, for every `t ≥ 0`,
`P(f_c(A, ·) ≥ t) ≤ exp(-t² / 4) / P(A)`. -/
theorem_wanted measure_le_convexDistance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) {A : Set (Fin N → Ω)}
    (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t) :
    Measure.pi (fun _ => μ) {x | t ≤ convexDistance A x} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / 4)) * (Measure.pi (fun _ => μ) A)⁻¹

end MathlibExt.Probability.ConvexDistanceWanted
