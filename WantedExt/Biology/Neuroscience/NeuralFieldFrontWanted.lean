/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ermentrout–McLeod: travelling fronts in a bistable neural field

For the scalar neural field `u_t = -u + ∫ w(x - y) f(u(y, t)) dy` with a nonnegative, bounded, even,
normalized spatial kernel `w` that is absolutely continuous with an integrable derivative, and a
smooth firing rate `f` that is increasing on `[u₁, u₃]`, where `u = f(u)` has exactly the three
solutions `u₁ < u₂ < u₃` in `[u₁, u₃]`, with the two endpoints stable (`f'(uᵢ) < 1`), Ermentrout and
McLeod (1993) proved that there is a monotone travelling front `u(x, t) = U(x - ct)` connecting the
two stable states, unique up to translation, with a unique speed `c`, whose sign is the sign of
`∫_{u₁}^{u₃} (f(u) - u) du`.

Conventions fixed here: the profile `U` is nonincreasing with `U(-∞) = u₃` and `U(+∞) = u₁`, so
`c > 0` means the upper state invades the lower one. The firing rate is assumed continuously
differentiable, with `f' > 0` on `[u₁, u₃]`. In the source the response to past input is a general
temporal kernel with a finite first moment; this module is its specialization to the exponential
kernel, which gives the equation above. This is the bistable front problem, not the monostable
Fisher–KPP speed result of `Domains.Biology.Dynamics.FisherKPP`.

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

/-- Standing hypotheses on the spatial kernel (Ermentrout and McLeod 1993): `w` is nonnegative,
bounded, even and integrable with `∫ w = 1`, and absolutely continuous with an integrable
derivative, written as `w x = w 0 + ∫_0^x w'` for an integrable `w'`. -/
structure IsNeuralKernel (w : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ w x
  bounded : ∃ M, ∀ x, |w x| ≤ M
  even : ∀ x, w (-x) = w x
  integrable : Integrable w
  integral_eq_one : ∫ x, w x = 1
  absolutelyContinuous : ∃ w' : ℝ → ℝ, Integrable w' ∧ ∀ x, w x = w 0 + ∫ y in (0 : ℝ)..x, w' y

/-- Standing hypotheses on the firing rate (Ermentrout and McLeod 1993): `f` is `C¹`, and on the
state interval `[u₁, u₃]` it has `f' > 0` and exactly the three fixed points `u₁ < u₂ < u₃`, with
the endpoints stable: `f'(u₁) < 1` and `f'(u₃) < 1`. Nothing is assumed about `f'(u₂)` or about
fixed points outside `[u₁, u₃]`. -/
structure IsBistable (f : ℝ → ℝ) (u₁ u₂ u₃ : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 f
  deriv_pos : ∀ u ∈ Set.Icc u₁ u₃, 0 < deriv f u
  lt₁₂ : u₁ < u₂
  lt₂₃ : u₂ < u₃
  fixed₁ : f u₁ = u₁
  fixed₂ : f u₂ = u₂
  fixed₃ : f u₃ = u₃
  fixed_only : ∀ u ∈ Set.Icc u₁ u₃, f u = u → u = u₁ ∨ u = u₂ ∨ u = u₃
  stable₁ : deriv f u₁ < 1
  stable₃ : deriv f u₃ < 1

/-- `U` is the profile of a **travelling front** with speed `c` from `u₃` to `u₁`: `U` is
nonincreasing, `U(x) → u₃` as `x → -∞` and `U(x) → u₁` as `x → +∞`, and `u(x, t) = U(x - ct)`
solves `u_t = -u + ∫ w(x - y) f(u(y, t)) dy` for all `x, t`. -/
def IsTravellingFront (w f : ℝ → ℝ) (u₁ u₃ c : ℝ) (U : ℝ → ℝ) : Prop :=
  Antitone U ∧ Tendsto U atBot (𝓝 u₃) ∧ Tendsto U atTop (𝓝 u₁) ∧
    ∀ x t, HasDerivAt (fun t => U (x - c * t))
      (-U (x - c * t) + ∫ y, w (x - y) * f (U (y - c * t))) t

/-- **Existence and uniqueness of the bistable front** (Ermentrout and McLeod 1993). Let `w` be
nonnegative, bounded, even and integrable with `∫ w = 1`, and absolutely continuous with an
integrable derivative (`w x = w 0 + ∫_0^x w'`, `w'` integrable), and let `f` be `C¹` with `f' > 0`
on `[u₁, u₃]` and with exactly the fixed points `u₁ < u₂ < u₃` in `[u₁, u₃]`, where `f'(u₁) < 1` and
`f'(u₃) < 1`. Then there are a speed `c` and a profile `U` of a travelling front from `u₃` to `u₁`;
every travelling front from `u₃` to `u₁`, with speed `c'` and profile `U'`, has `c' = c` and
`U' = U(· + ξ)` for some `ξ`; and `c > 0 ↔ ∫_{u₁}^{u₃} (f(u) - u) du > 0` and
`c = 0 ↔ ∫_{u₁}^{u₃} (f(u) - u) du = 0`.

Source: G. B. Ermentrout and J. B. McLeod, "Existence and uniqueness of travelling waves for a
neural network", Proc. Roy. Soc. Edinburgh Sect. A 123 (1993) 461–478. -/
public theorem_wanted existsUnique_travellingFront {w f : ℝ → ℝ} {u₁ u₂ u₃ : ℝ}
    (hw : IsNeuralKernel w) (hf : IsBistable f u₁ u₂ u₃) :
    ∃ c : ℝ, ∃ U : ℝ → ℝ, IsTravellingFront w f u₁ u₃ c U ∧
      (∀ c' : ℝ, ∀ U' : ℝ → ℝ, IsTravellingFront w f u₁ u₃ c' U' →
        c' = c ∧ ∃ ξ : ℝ, ∀ x, U' x = U (x + ξ)) ∧
      (0 < c ↔ 0 < ∫ u in u₁..u₃, (f u - u)) ∧ (c = 0 ↔ ∫ u in u₁..u₃, (f u - u) = 0)

end WantedExt.Biology.Neuroscience.NeuralFieldFrontWanted
