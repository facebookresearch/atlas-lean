/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Debye–Smoluchowski diffusion-limited rate constant

Debye (1942, Appendix and equation (5)): molecules `B` diffuse with relative diffusion coefficient
`D` in an interaction potential `U(r)` around a molecule `A`, and react on contact at distance `R`
(absorbing boundary `n(R) = 0`), with bulk number density `n(r) → n₀` as `r → ∞`. In the steady
state the radial current through every sphere of radius `r ≥ R`,

  `J = 4π r² D (n'(r) + n(r) U'(r) / k_B T)`,

is constant and equals `J = 4π D β n₀`, where `1/β = ∫_R^∞ e^{U(r)/k_B T} r^{-2} dr`. For
arbitrary real `n₀` (without imposing `n ≥ 0`), this is a linear steady-profile current identity
(with `J = 0` when `n₀ = 0`). In the physical regime of a nonnegative density with positive bulk
density `n₀ > 0`, dividing by `n₀` gives the diffusion-limited rate constant `k_D = J / n₀`:

  `k_D = 4π D β`,  `1/β = ∫_R^∞ e^{U(r)/k_B T} r^{-2} dr`;

for `U = 0` this is Smoluchowski's `k_D = 4π D R` (1917). Debye writes the result as a collision
frequency with the Stokes–Einstein diffusion coefficient; the diffusion-coefficient form stated here
is the specific current of his Appendix before the friction constants are substituted.

The potential is assumed differentiable on `[R, ∞)` with `U(r) → 0` as `r → ∞` and
`e^{U/k_B T} r^{-2}` integrable on `[R, ∞)`. A steady profile is a function `n` with a derivative
within `[R, ∞)` at every `r ≥ R` for which the current above is a constant `J`. Not recorded here:
the finite-intrinsic-rate formula `k = 4π D β k_r / (k_r + 4π D β e^{U(R)/k_B T})` (the
Collins–Kimball radiation boundary condition), whose source is not held.

Sources: P. Debye, "Reaction rates in ionic solutions", Transactions of the Electrochemical
Society 82 (1942) 265–272, equations (4′), (5) and Appendix; M. v. Smoluchowski, "Versuch einer
mathematischen Theorie der Koagulationskinetik kolloider Lösungen", Zeitschrift für physikalische
Chemie 92 (1917) 129–168.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Biophysics.DiffusionLimitedRate
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace WantedExt.Biology.Biophysics.DiffusionLimitedRateWanted

open MeasureTheory Filter Topology Set

/-- `1/β = ∫_R^∞ e^{U(r)/kT} r^{-2} dr`. -/
noncomputable def invBeta (kT R : ℝ) (U : ℝ → ℝ) : ℝ :=
  ∫ r in Ioi R, Real.exp (U r / kT) / r ^ 2

/-- **Steady radial current with an interaction potential** (Debye 1942): let `D, kT, R > 0`, let
`U` have derivative `U'(r)` within `[R, ∞)` at every `r ≥ R`, let `U(r) → 0` as `r → ∞`, and let
`r ↦ e^{U(r)/kT} r^{-2}` be integrable on `(R, ∞)`. For every real asymptotic value `n₀` (without
restricting `n` to be nonnegative), there is a steady radial profile `n` with some current `J`,
`n(R) = 0` and `n(r) → n₀`, and every such profile satisfies `J = 4π D β n₀` with
`1/β = ∫_R^∞ e^{U(r)/kT} r^{-2} dr` (so `J = 0` at `n₀ = 0`). When `n` is a nonnegative density
with positive bulk density `n₀ > 0`, the quotient `k_D = J / n₀ = 4π D β` is the
diffusion-limited rate constant.

Source: Debye (1942), equation (5) and Appendix. -/
public theorem_wanted current_eq (D kT R : ℝ) (hD : 0 < D) (hkT : 0 < kT) (hR : 0 < R)
    (U U' : ℝ → ℝ) (hU : ∀ r, R ≤ r → HasDerivWithinAt U (U' r) (Ici R) r)
    (hU0 : Tendsto U atTop (𝓝 0))
    (hint : IntegrableOn (fun r => Real.exp (U r / kT) / r ^ 2) (Ioi R)) (n₀ : ℝ) :
    (∃ (n : ℝ → ℝ) (J : ℝ), IsSteadyProfile D kT R U' n J ∧ n R = 0 ∧
        Tendsto n atTop (𝓝 n₀)) ∧
      ∀ (n : ℝ → ℝ) (J : ℝ), IsSteadyProfile D kT R U' n J → n R = 0 →
        Tendsto n atTop (𝓝 n₀) → J = 4 * Real.pi * D * n₀ / invBeta kT R U

end WantedExt.Biology.Biophysics.DiffusionLimitedRateWanted
