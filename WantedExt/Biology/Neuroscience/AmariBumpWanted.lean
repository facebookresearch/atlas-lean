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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace WantedExt.Biology.Neuroscience.AmariBumpWanted

open MeasureTheory

/-- `W(a) = ∫_0^a w(x) dx`. -/
noncomputable def kernelPrimitive (w : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, w x

/-- The Heaviside firing function `H(z) = 1` for `z > 0` and `0` otherwise. -/
noncomputable def heaviside (z : ℝ) : ℝ :=
  if 0 < z then 1 else 0

/-- The field input `∫ w(x - y) H(u(y) - h) dy + s` at position `x` for the state `u`. -/
noncomputable def fieldInput (w : ℝ → ℝ) (h s : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y, w (x - y) * heaviside (u y - h)) + s

/-- Standing hypotheses on the kernel: `w` is continuous, even and integrable. -/
structure IsKernel (w : ℝ → ℝ) : Prop where
  continuous : Continuous w
  even : ∀ x, w (-x) = w x
  integrable : Integrable w

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

/-- **Amari's interface equation** (Amari 1977). Let `w` be continuous, even and integrable and
`h, s ∈ ℝ`. Let `u : ℝ → ℝ → ℝ` be `C¹` in `(x, t)` and solve
`∂_t u(x, t) = -u(x, t) + fieldInput w h s (u · t) x` for all `x, t`. Let `x₁, x₂ : ℝ → ℝ` be
differentiable with `x₁ t < x₂ t` and `{x | h < u x t} = (x₁ t, x₂ t)` for all `t`, and let the
slopes `c₁ t = ∂_x u(x₁ t, t)` and `c₂ t = -∂_x u(x₂ t, t)` be positive for all `t`. Then for every
`t` the width `a = x₂ - x₁` has derivative `(W(a(t)) + s - h) (1 / c₁ t + 1 / c₂ t)` at `t`.

Source: S. Amari, "Dynamics of pattern formation in lateral-inhibition type neural fields",
Biol. Cybern. 27 (1977) 77–87. -/
public theorem_wanted hasDerivAt_width {w : ℝ → ℝ} (hw : IsKernel w) (h s : ℝ)
    (u : ℝ → ℝ → ℝ) (hu : ContDiff ℝ 1 (fun p : ℝ × ℝ => u p.1 p.2))
    (heq : ∀ x t, HasDerivAt (fun t => u x t) (-u x t + fieldInput w h s (fun y => u y t) x) t)
    (x₁ x₂ : ℝ → ℝ) (hx₁ : Differentiable ℝ x₁) (hx₂ : Differentiable ℝ x₂)
    (hlt : ∀ t, x₁ t < x₂ t) (hex : ∀ t, {x | h < u x t} = Set.Ioo (x₁ t) (x₂ t))
    (hc₁ : ∀ t, 0 < deriv (fun x => u x t) (x₁ t)) (hc₂ : ∀ t, deriv (fun x => u x t) (x₂ t) < 0)
    (t : ℝ) :
    HasDerivAt (fun t => x₂ t - x₁ t)
      ((kernelPrimitive w (x₂ t - x₁ t) + s - h) *
        (1 / deriv (fun x => u x t) (x₁ t) + 1 / -deriv (fun x => u x t) (x₂ t))) t

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
