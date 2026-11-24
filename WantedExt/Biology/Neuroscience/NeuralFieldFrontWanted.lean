/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ermentrout–McLeod: travelling fronts in a bistable neural field

For the scalar neural field `u_t = -u + ∫ w(x - y) f(u(y, t)) dy` with a nonnegative, even,
normalized kernel `w` and a smooth increasing firing rate `f` such that `u = f(u)` has exactly
three solutions `u₁ < u₂ < u₃`, the outer two stable (`f'(uᵢ) < 1`) and the middle one unstable
(`f'(u₂) > 1`), Ermentrout and McLeod (1993) proved that there is a monotone travelling front
`u(x, t) = U(x - ct)` connecting the two stable states, unique up to translation, with a unique
speed `c`, whose sign is the sign of `∫_{u₁}^{u₃} (f(u) - u) du`.

Conventions fixed here: the profile `U` is nonincreasing with `U(-∞) = u₃` and `U(+∞) = u₁`, so
`c > 0` means the upper state invades the lower one. Regularity assumptions are explicit and
declared: `w` continuous with a finite first moment, `f` continuously differentiable with
`f' > 0`. This is the bistable front problem, not the monostable Fisher–KPP speed result of
`Domains.Biology.Dynamics.FisherKPP`.

Sources: G. B. Ermentrout and J. B. McLeod, "Existence and uniqueness of travelling waves for a
neural network", Proc. Roy. Soc. Edinburgh Sect. A 123 (1993) 461–478.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace WantedExt.Biology.Neuroscience.NeuralFieldFrontWanted

open MeasureTheory Filter Topology

/-- Standing hypotheses on the kernel: `w` is continuous, nonnegative, even, integrable with
`∫ w = 1`, and has a finite first moment `∫ |x| w(x) dx < ∞`. -/
structure IsNeuralKernel (w : ℝ → ℝ) : Prop where
  continuous : Continuous w
  nonneg : ∀ x, 0 ≤ w x
  even : ∀ x, w (-x) = w x
  integrable : Integrable w
  integral_eq_one : ∫ x, w x = 1
  integrable_moment : Integrable (fun x => |x| * w x)

/-- Standing hypotheses on the firing rate: `f` is `C¹` with `f' > 0`, and `u = f(u)` has exactly
the three solutions `u₁ < u₂ < u₃`, with `f'(u₁) < 1`, `f'(u₃) < 1` and `f'(u₂) > 1`. -/
structure IsBistable (f : ℝ → ℝ) (u₁ u₂ u₃ : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 f
  deriv_pos : ∀ u, 0 < deriv f u
  lt₁₂ : u₁ < u₂
  lt₂₃ : u₂ < u₃
  fixed₁ : f u₁ = u₁
  fixed₂ : f u₂ = u₂
  fixed₃ : f u₃ = u₃
  fixed_only : ∀ u, f u = u → u = u₁ ∨ u = u₂ ∨ u = u₃
  stable₁ : deriv f u₁ < 1
  unstable₂ : 1 < deriv f u₂
  stable₃ : deriv f u₃ < 1

/-- `U` is the profile of a **travelling front** with speed `c` from `u₃` to `u₁`: `U` is
nonincreasing, `U(x) → u₃` as `x → -∞` and `U(x) → u₁` as `x → +∞`, and `u(x, t) = U(x - ct)`
solves `u_t = -u + ∫ w(x - y) f(u(y, t)) dy` for all `x, t`. -/
def IsTravellingFront (w f : ℝ → ℝ) (u₁ u₃ c : ℝ) (U : ℝ → ℝ) : Prop :=
  Antitone U ∧ Tendsto U atBot (𝓝 u₃) ∧ Tendsto U atTop (𝓝 u₁) ∧
    ∀ x t, HasDerivAt (fun t => U (x - c * t))
      (-U (x - c * t) + ∫ y, w (x - y) * f (U (y - c * t))) t

/-- **Existence and uniqueness of the bistable front** (Ermentrout and McLeod 1993). Let `w` be
continuous, nonnegative, even and integrable with `∫ w = 1` and `∫ |x| w(x) dx < ∞`, and let `f`
be `C¹` with `f' > 0` whose fixed points are exactly `u₁ < u₂ < u₃`, with `f'(u₁) < 1`,
`f'(u₃) < 1`, `f'(u₂) > 1`. Then there are a speed `c` and a profile `U` of a travelling front
from `u₃` to `u₁`; every travelling front from `u₃` to `u₁`, with speed `c'` and profile `U'`, has
`c' = c` and `U' = U(· + ξ)` for some `ξ`; and `c > 0 ↔ ∫_{u₁}^{u₃} (f(u) - u) du > 0` and
`c = 0 ↔ ∫_{u₁}^{u₃} (f(u) - u) du = 0`.

Source: Ermentrout and McLeod (1993). -/
public theorem_wanted existsUnique_travellingFront {w f : ℝ → ℝ} {u₁ u₂ u₃ : ℝ}
    (hw : IsNeuralKernel w) (hf : IsBistable f u₁ u₂ u₃) :
    ∃ c : ℝ, ∃ U : ℝ → ℝ, IsTravellingFront w f u₁ u₃ c U ∧
      (∀ c' : ℝ, ∀ U' : ℝ → ℝ, IsTravellingFront w f u₁ u₃ c' U' →
        c' = c ∧ ∃ ξ : ℝ, ∀ x, U' x = U (x + ξ)) ∧
      (0 < c ↔ 0 < ∫ u in u₁..u₃, (f u - u)) ∧ (c = 0 ↔ ∫ u in u₁..u₃, (f u - u) = 0)

end WantedExt.Biology.Neuroscience.NeuralFieldFrontWanted
