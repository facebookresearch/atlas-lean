/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Amari's bumps in lateral-inhibition neural fields

Amari (1977) studies the one-dimensional neural field
`u_t(x, t) = -u(x, t) + ∫ w(x - y) H(u(y, t) - h) dy + s` with Heaviside firing `H`, threshold
`h`, constant input `s` and an even lateral-inhibition kernel `w`, and writes
`W(a) = ∫_0^a w`. A bump of width `a > 0` is a stationary solution whose excited region
`{u > h}` is an interval of length `a`. Every such bump satisfies `W(a) + s = h` and has the
profile `U(x) = W(x) - W(x - a) + s`. For a solution whose excited region is a moving interval
`(x₁(t), x₂(t))` with nonzero slopes at its ends, the width obeys Amari's interface equation
`a'(t) = (W(a) + s - h) (1/c₁ + 1/c₂)`, where `c₁, c₂ > 0` are the absolute slopes at the two
ends; hence a bump of width `a*` attracts nearby widths when `w(a*) < 0` and repels them when
`w(a*) > 0`.

Recorded here: the necessary condition and profile, the interface equation, and the stability
criterion it yields. The sufficiency direction of existence needs shape conditions on the
lateral-inhibition kernel that the statement used for this module does not fix, so it is not
stated.

Sources: S. Amari, "Dynamics of pattern formation in lateral-inhibition type neural fields",
Biol. Cybern. 27 (1977) 77–87.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Neuroscience.AmariBump
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace WantedExt.Biology.Neuroscience.AmariBumpWanted

open MeasureTheory

/-- **Necessary condition and bump profile** (Amari 1977). Let `w` be continuous, even and
integrable, `h, s ∈ ℝ`, `a > 0`, and let `U : ℝ → ℝ` be continuous with `U x = fieldInput w h s U x`
for every `x` (a stationary solution) and excited region `{x | h < U x} = (0, a)`. Then
`W(a) + s = h` and `U x = W(x) - W(x - a) + s` for every `x`.

Source: S. Amari, "Dynamics of pattern formation in lateral-inhibition type neural fields",
Biol. Cybern. 27 (1977) 77–87. -/
public theorem_wanted bump_condition_and_profile {w : ℝ → ℝ} (hw : IsKernel w) (h s a : ℝ)
    (ha : 0 < a) (U : ℝ → ℝ) (hU : Continuous U) (hstat : ∀ x, U x = fieldInput w h s U x)
    (hex : {x | h < U x} = Set.Ioo 0 a) :
    kernelPrimitive w a + s = h ∧
      ∀ x, U x = kernelPrimitive w x - kernelPrimitive w (x - a) + s

/-- **Amari's stability criterion for bump widths** (Amari 1977). Let `w` be continuous, even and
integrable, and let `a* > 0` satisfy `W(a*) + s = h`. If `w(a*) < 0`, there is `δ > 0` such that
every width `a` with `0 < |a - a*| < δ` has `(a - a*) (W(a) + s - h) < 0`, so the interface
equation moves `a` towards `a*`; if `w(a*) > 0`, there is `δ > 0` such that every such `a` has
`(a - a*) (W(a) + s - h) > 0`, so it moves `a` away from `a*`.

Source: S. Amari, "Dynamics of pattern formation in lateral-inhibition type neural fields",
Biol. Cybern. 27 (1977) 77–87. -/
public theorem_wanted width_stability {w : ℝ → ℝ} (hw : IsKernel w) {h s a₀ : ℝ} (ha₀ : 0 < a₀)
    (hbump : kernelPrimitive w a₀ + s = h) :
    (w a₀ < 0 → ∃ δ > 0, ∀ a, 0 < |a - a₀| → |a - a₀| < δ →
        (a - a₀) * (kernelPrimitive w a + s - h) < 0) ∧
      (0 < w a₀ → ∃ δ > 0, ∀ a, 0 < |a - a₀| → |a - a₀| < δ →
        0 < (a - a₀) * (kernelPrimitive w a + s - h))

end WantedExt.Biology.Neuroscience.AmariBumpWanted
