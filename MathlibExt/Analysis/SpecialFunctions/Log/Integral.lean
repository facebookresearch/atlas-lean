/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Logarithmic integral (normalized principal value)

Classical lowercase logarithmic integral `li(x) := ∫₀ˣ dt / log t` in the
normalization used by arXiv:2306.14073v1 and arXiv:2309.16007v1. The real-valued
interpretation is the Cauchy principal value at the non-integrable singularity
`t = 1`. The function is defined on `{x : ℝ // 0 ≤ x ∧ x ≠ 1}`; the point
`x = 1` is excluded because `1 / log t` has a non-integrable singularity
there. At `x = 0` the value is `0`, as the integral over a degenerate interval
vanishes. For `x > 1` the principal value is represented by the paired form
symmetric about `1`, not by the raw interval integral `∫₀ˣ`, which Mathlib
totalizes via `inv 0 = 0` and Lebesgue measure-zero modifications at isolated
points. The paired symmetric integral is Lebesgue-equivalent to
`lim_{ε → 0⁺} (∫₀^{1-ε} + ∫_{1+ε}²)`.
-/

@[expose] public section

namespace Real

/-- **Domain of the logarithmic integral.** The domain of the logarithmic integral is the set of
real numbers $x$ with $x \ge 0$ and $x \ne 1$.

The point $1$ is excluded because $1 / \log t$ is singular at $t = 1$; the classical integral
$\int_0^x dt / \log t$ has no finite real value at $x = 1$ and is understood as a Cauchy
principal value for $x \ne 1$.

Source: arXiv:2306.14073v1 and arXiv:2309.16007v1, classical `li(x) := PV ∫₀ˣ dt/log t`
with lower limit `0` and principal value at `t = 1`. -/
abbrev LogarithmicIntegralDomain : Type :=
  { x : ℝ // 0 ≤ x ∧ x ≠ 1 }

/-- **Logarithmic integral.** For a real number $x$ in the domain of the logarithmic integral
(that is, $x \ge 0$ and $x \ne 1$), the logarithmic integral $\mathrm{li}(x)$ is
$\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ if $x < 1$, and if $x > 1$ it is
$$
\mathrm{li}(x) = \int_0^1 \Big(\frac{1}{\log(1-u)} + \frac{1}{\log(1+u)}\Big) du +
\int_2^x \frac{dt}{\log t}.
$$

The first integral in the second case is the Cauchy principal value
$\mathrm{PV}\int_0^2 \frac{dt}{\log t}$, rewritten by the substitutions $t = 1 - u$ and
$t = 1 + u$, so that $\mathrm{li}(x)$ is the principal value
$\mathrm{PV}\int_0^x \frac{dt}{\log t}$. In particular $\mathrm{li}(0) = 0$.

Source: arXiv:2306.14073v1 and arXiv:2309.16007v1, normalized lower limit `0`
and Cauchy principal value at `t = 1` via symmetric pairing. -/
noncomputable def logarithmicIntegral (x : LogarithmicIntegralDomain) : ℝ :=
  if x.val < 1 then
    ∫ t in (0 : ℝ)..x.val, (Real.log t)⁻¹
  else
    (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
      ∫ t in (2 : ℝ)..x.val, (Real.log t)⁻¹

/-- **The logarithmic integral vanishes at zero.** The logarithmic integral $\mathrm{li}$
satisfies $\mathrm{li}(0) = 0$; here $0$ lies in its domain since $0 \ge 0$ and $0 \ne 1$.

Source: `∫₀⁰ = 0` for Lebesgue interval integrals; holds for any domain
proof `hx` with `x = 0`. -/
@[simp]
theorem logarithmicIntegral_zero {hx : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≠ (1 : ℝ)} :
    logarithmicIntegral ⟨(0 : ℝ), hx⟩ = 0 := by
  simp [logarithmicIntegral]

/-- **The logarithmic integral below $1$.** For every real number $x$ with $0 \le x < 1$, the
logarithmic integral $\mathrm{li}$ satisfies $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$.

Source: Direct unfolding of the `x < 1` branch of the piecewise definition. -/
theorem logarithmicIntegral_of_lt_one {x : LogarithmicIntegralDomain} (hx : x.val < 1) :
    logarithmicIntegral x = ∫ t in (0 : ℝ)..x.val, (Real.log t)⁻¹ := by
  simp [logarithmicIntegral, hx]

/-- **The logarithmic integral above $1$.** For every real number $x > 1$, the logarithmic
integral $\mathrm{li}$ satisfies
$$
\mathrm{li}(x) = \int_0^1 \Big(\frac{1}{\log(1-u)} + \frac{1}{\log(1+u)}\Big) du +
\int_2^x \frac{dt}{\log t}.
$$

The paired integral over $[0, 1]$ is the symmetric principal value
$\mathrm{PV}\int_0^2 \frac{dt}{\log t}$.

Source: Direct unfolding of the `x > 1` branch; `¬ x < 1` from `1 < x`. -/
theorem logarithmicIntegral_of_one_lt {x : LogarithmicIntegralDomain} (hx : 1 < x.val) :
    logarithmicIntegral x =
      (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
        ∫ t in (2 : ℝ)..x.val, (Real.log t)⁻¹ := by
  have h : ¬ x.val < 1 := not_lt.mpr hx.le
  simp [logarithmicIntegral, h]

end Real
