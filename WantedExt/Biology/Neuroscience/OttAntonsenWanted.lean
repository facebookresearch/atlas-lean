/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Ott–Antonsen invariant manifold for globally coupled phase oscillators

In the continuum Kuramoto model with coupling `K`, the density `f(ω, θ, t)` of oscillators with
natural frequency `ω` and phase `θ` obeys the continuity equation
`∂f/∂t + ∂/∂θ [v f] = 0` with velocity `v = ω + (K / (2i)) (r e^{-iθ} - r̄ e^{iθ})` and order
parameter `r = ∫∫ f e^{iθ} dθ dω` (Ott and Antonsen 2008, Eqs. (4)–(5)). With an external drive
`Λ sin(Ω t - θ)`, in the frame rotating at `Ω`, the velocity becomes
`v = (ω - Ω) + Im (F e^{-iθ})` with `F = K r + Λ` (Eq. (13)). Ott and Antonsen observe that
densities whose Fourier coefficients are the powers `α^n` of a single function `α(ω, t)`, that
is (for `|α| < 1`) the Poisson kernels

  `f = (g(ω) / (2π)) (1 - |α|²) / |1 - α e^{iθ}|²`  (Eq. (8)),

solve the continuity equation exactly when `α' = -(1/2)(F α² - F̄) - i (ω - Ω) α` (Eq. (6) in the
rotating frame), that `|α| < 1` is preserved (Eq. (9)), and that for the Lorentzian frequency
density `g_L(ω) = (Δ / π) / ((ω - ω₀)² + Δ²)` the self-consistency condition `r̄ = ∫ α g_L dω`
closes at the pole `ω₀ - iΔ` when `α(·, t)` extends boundedly and holomorphically to the lower
half-plane: then `r̄(t) = α(ω₀ - iΔ, t)` obeys the two-real-dimensional equation (14), which for
`Λ = 0`, `Ω = ω₀` is Eq. (10), `ρ' = -(1 - K/2) ρ - (K/2) ρ³` for `ρ = |r|`. The invariance of the
Lorentzian manifold is stated for the strict-real-boundary subclass `Admissible` of their invariant
manifold, whose functions have modulus `< 1` on the real axis; the manifold itself (Section III)
asks only `|α(ω, t)| ≤ 1` for real `ω` and contains their example `k e^{-iωc}` with `k = c = 1`,
of modulus `1` on the whole real axis, whose angular distribution is a singular measure rather
than a density. The angular density is Mathlib's Poisson kernel `poissonKernel` of the unit disk,
and the Lorentzian density is the Cauchy density `ProbabilityTheory.cauchyPDFReal`. The printed
closed-form solution Eq. (11) of the arXiv version is inconsistent with Eq. (10) and is not used.
Attractivity of the manifold, non-Lorentzian frequency densities and finite-`N` statements are not
claimed.

Sources: E. Ott and T. M. Antonsen, "Low dimensional behavior of large systems of globally
coupled oscillators", Chaos 18 (2008) 037113, Eqs. (4)–(10), (13)–(14), Sections III and IV.b
(arXiv:0806.0004).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Probability.Distributions.Cauchy

@[expose] public section

namespace WantedExt.Biology.Neuroscience.OttAntonsenWanted

open Complex Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The Poisson-kernel density of Eq. (8) (the density `f / g` on the ansatz manifold):
Mathlib's Poisson kernel of the unit disk at the point `ᾱ`, evaluated at `e^{iθ}`, divided by
`2π`. It equals `(1 - |α|²) / (2π |1 - α e^{iθ}|²)`, since `|e^{iθ} - ᾱ| = |1 - α e^{iθ}|`, and
`(1 - |α|²) / (2π ((1 - |α|)² + 4 |α| sin² ((θ - ψ)/2)))` for `α = |α| e^{-iψ}`. -/
noncomputable def poissonDensity (α : ℂ) (θ : ℝ) : ℝ :=
  poissonKernel 0 ((starRingEnd ℂ) α) (exp (θ * I)) / (2 * Real.pi)

/-- The phase velocity `(ω - Ω) + Im (F e^{-iθ})` of an oscillator with natural frequency `ω`
in the frame rotating at `Ω`, under the mean-field forcing `F = K r + Λ` (Eq. (13)). -/
noncomputable def velocity (ω Ω : ℝ) (F : ℂ) (θ : ℝ) : ℝ :=
  (ω - Ω) + (F * exp (-(θ * I))).im

/-- The right-hand side of the ansatz equation (6) in the rotating frame, for a (possibly
complex) frequency `w` and forcing `F`: `-(1/2)(F α² - F̄) - i (w - Ω) α`. -/
noncomputable def ansatzField (Ω : ℝ) (w F α : ℂ) : ℂ :=
  -(1 / 2) * (F * α ^ 2 - (starRingEnd ℂ) F) - I * (w - Ω) * α

/-- The right-hand side of the order-parameter equation (14) for the Lorentzian frequency density
with `Δ = 1` centred at `ω₀`, with coupling `K` and drive `Λ` at frequency `Ω`:
`-(1/2)((K r + Λ)‾ r² - (K r + Λ)) - (1 + i (Ω - ω₀)) r`. -/
noncomputable def orderField (K Λ Ω ω₀ : ℝ) (r : ℂ) : ℂ :=
  -(1 / 2) * ((starRingEnd ℂ) (K * r + Λ) * r ^ 2 - (K * r + Λ)) - (1 + I * (Ω - ω₀)) * r

/-- The strict-real-boundary subclass of the functions on Ott and Antonsen's invariant manifold
(Section III): bounded by `1` and continuous on the closed lower half-plane, holomorphic on the
open lower half-plane, of modulus `< 1` on the real axis, and tending to `0` as `Im w → -∞`,
uniformly in `Re w`. The manifold itself asks only `|α(ω, t)| ≤ 1` for real `ω`: their example
`k e^{-iωc}` with `k = c = 1` is holomorphic, tends to `0` as `Im ω → -∞` and has modulus `1` on
the real axis, so it lies on the manifold but not in this subclass. -/
structure Admissible (β : ℂ → ℂ) : Prop where
  norm_le_one : ∀ w : ℂ, w.im ≤ 0 → ‖β w‖ ≤ 1
  continuousOn : ContinuousOn β {w | w.im ≤ 0}
  differentiableOn : DifferentiableOn ℂ β {w | w.im < 0}
  norm_lt_one_real : ∀ x : ℝ, ‖β x‖ < 1
  tendsto_zero : Tendsto β (comap im atBot ⊓ 𝓟 {w | w.im ≤ 0}) (𝓝 0)

/-- **The ansatz solves the continuity equation** (Ott and Antonsen 2008, Eqs. (6)–(8), in the
driven, rotating-frame form of Eq. (13)). Let `ω, Ω` be real, `F : ℝ → ℂ` a forcing, and
`α : ℝ → ℂ` with `‖α t‖ < 1` and derivative `ansatzField Ω ω (F t) (α t)` at `t`. Then for every
`θ` the density `p(θ, s) = poissonDensity (α s) θ` satisfies the continuity equation at `(θ, t)`:
there are `a` and `b` with `∂p/∂t = a` at `t`, `∂(v p)/∂θ = b` at `θ` for the velocity
`v = velocity ω Ω (F t)`, and `a + b = 0`.

Source: Ott and Antonsen (2008), Eqs. (6)–(8) and (13). -/
theorem_wanted continuity_poissonDensity (ω Ω : ℝ) (F α : ℝ → ℂ) (t θ : ℝ)
    (hα : HasDerivAt α (ansatzField Ω ω (F t) (α t)) t) (hα1 : ‖α t‖ < 1) :
    ∃ a b : ℝ, HasDerivAt (fun s => poissonDensity (α s) θ) a t ∧
      HasDerivAt (fun φ => velocity ω Ω (F t) φ * poissonDensity (α t) φ) b θ ∧ a + b = 0

/-- **Density and order-parameter moment** (Ott and Antonsen 2008, Eqs. (7)–(8)). For `‖α‖ < 1`
the density `poissonDensity α` is nonnegative, has integral `1` over `[0, 2π]`, and its first
moment `∫_0^{2π} poissonDensity α θ e^{iθ} dθ` equals `ᾱ`. The sentence after Eq. (8) prints
`∫ dθ f = g(ω)/2π`; the unit mass of `f / g` stated here follows instead from Section II's
normalization `∫_0^{2π} f dθ = g(ω)` and from the constant coefficient `g(ω)/(2π)` of the Fourier
expansion of `f` before Eq. (6), whose other modes integrate to zero over `[0, 2π]`.

Source: Ott and Antonsen (2008), Section II, the Fourier expansion before Eq. (6), and
Eqs. (7)–(8). -/
theorem_wanted poissonDensity_moments (α : ℂ) (hα : ‖α‖ < 1) :
    (∀ θ, 0 ≤ poissonDensity α θ) ∧ ∫ θ in (0 : ℝ)..2 * Real.pi, poissonDensity α θ = 1 ∧
      ∫ θ in (0 : ℝ)..2 * Real.pi, (poissonDensity α θ : ℂ) * exp (θ * I) = (starRingEnd ℂ) α

/-- **The unit disk is invariant** (Ott and Antonsen 2008, Eq. (9)). Let `K, Λ, Ω` be real, let
`r : ℝ → ℂ` be continuous, and let `w` be a frequency with `Im w ≤ 0` and `‖α₀‖ < 1`. Then the
ansatz equation `α' = ansatzField Ω w (K r(t) + Λ) α` has a solution `α` on `[0, ∞)` with
`α 0 = α₀` (derivative within `[0, ∞)` at every `t ≥ 0`, one-sided at `0`), it satisfies
`‖α t‖ < 1` for all `t ≥ 0`, and any other such solution agrees with it on `[0, ∞)`.

Source: Ott and Antonsen (2008), Eq. (9) and Section III. -/
theorem_wanted exists_unique_ansatz_solution (K Λ Ω : ℝ) (r : ℝ → ℂ) (hr : Continuous r)
    (w α₀ : ℂ) (hw : w.im ≤ 0) (hα₀ : ‖α₀‖ < 1) :
    ∃ α : ℝ → ℂ, α 0 = α₀ ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt α (ansatzField Ω w (K * r t + Λ) (α t)) (Set.Ici 0) t) ∧
      (∀ t, 0 ≤ t → ‖α t‖ < 1) ∧
      ∀ β : ℝ → ℂ, β 0 = α₀ →
        (∀ t, 0 ≤ t → HasDerivWithinAt β (ansatzField Ω w (K * r t + Λ) (β t)) (Set.Ici 0) t) →
        ∀ t, 0 ≤ t → β t = α t

/-- **Lorentzian evaluation** (Ott and Antonsen 2008, Section III, the closure at the pole). Let
`ω₀` be real and `Δ > 0`, and let `β` be bounded by `1` and continuous on the closed lower
half-plane and holomorphic on the open lower half-plane. Then
`∫ β(ω) g_L(ω) dω = β(ω₀ - iΔ)`, where `g_L(ω) = Δ / (π ((ω - ω₀)² + Δ²))` is the Lorentzian
(Cauchy) density `cauchyPDFReal ω₀ Δ` of location `ω₀` and scale `Δ`.

Source: Ott and Antonsen (2008), Section III. -/
theorem_wanted integral_mul_lorentzian (ω₀ : ℝ) (Δ : ℝ≥0) (hΔ : 0 < Δ) (β : ℂ → ℂ)
    (hβ1 : ∀ w : ℂ, w.im ≤ 0 → ‖β w‖ ≤ 1) (hβc : ContinuousOn β {w | w.im ≤ 0})
    (hβd : DifferentiableOn ℂ β {w | w.im < 0}) :
    ∫ ω : ℝ, β ω * (cauchyPDFReal ω₀ Δ ω : ℂ) = β (ω₀ - (Δ : ℝ) * I)

/-- **The Lorentzian ansatz manifold is invariant and closes on the order parameter** (Ott and
Antonsen 2008, Sections III and IV.b and Eq. (14)). Let `K, Λ, Ω, ω₀` be real and let `α₀` lie in
the strict-real-boundary subclass `Admissible` of their invariant manifold (modulus `< 1` on the
real axis, where the manifold allows modulus `≤ 1`). Then there is a solution `r` of the
order-parameter equation (14) (`r' = orderField K Λ Ω ω₀ r`, derivative within `[0, ∞)` at every
`t ≥ 0`, one-sided at `0`) on `[0, ∞)` with `r 0 = conj (α₀ (ω₀ - i))`, such that:
* there is a family `α(w, t)` that, for each `w` with `Im w ≤ 0`, solves the ansatz equation
  `α(w, ·)' = ansatzField Ω w (K r(t) + Λ) α(w, ·)` on `[0, ∞)` (derivative within `[0, ∞)` at
  every `t ≥ 0`, one-sided at `0`) with `α(w, 0) = α₀ w`; and
* every such family satisfies, for every `t ≥ 0`: `α(·, t)` stays in the subclass `Admissible`,
  and `conj (r t) = ∫ α(ω, t) g_L(ω) dω` for the Lorentzian density `g_L = cauchyPDFReal ω₀ 1`
  with `Δ = 1` centred at `ω₀` (self-consistency, Eq. (7)).

Source: Ott and Antonsen (2008), Sections III and IV.b and Eq. (14). -/
theorem_wanted exists_order_parameter_invariant (K Λ Ω ω₀ : ℝ) (α₀ : ℂ → ℂ)
    (hα₀ : Admissible α₀) :
    ∃ r : ℝ → ℂ, r 0 = (starRingEnd ℂ) (α₀ (ω₀ - I)) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt r (orderField K Λ Ω ω₀ (r t)) (Set.Ici 0) t) ∧
      (∃ α : ℂ → ℝ → ℂ, ∀ w : ℂ, w.im ≤ 0 → α w 0 = α₀ w ∧ ∀ t, 0 ≤ t →
          HasDerivWithinAt (α w) (ansatzField Ω w (K * r t + Λ) (α w t)) (Set.Ici 0) t) ∧
      ∀ α : ℂ → ℝ → ℂ, (∀ w : ℂ, w.im ≤ 0 → α w 0 = α₀ w ∧ ∀ t, 0 ≤ t →
          HasDerivWithinAt (α w) (ansatzField Ω w (K * r t + Λ) (α w t)) (Set.Ici 0) t) →
        ∀ t, 0 ≤ t → Admissible (fun w => α w t) ∧
          (starRingEnd ℂ) (r t) = ∫ ω : ℝ, α ω t * (cauchyPDFReal ω₀ 1 ω : ℂ)

/-- **The Kuramoto reduction** (Ott and Antonsen 2008, Eq. (10)). Let `K` and `ω₀` be real, and
let `r` solve Eq. (14) without drive and in the frame rotating at `ω₀`
(`r' = orderField K 0 ω₀ ω₀ r` at `t`), with `r t ≠ 0`. Then `ρ = |r|` satisfies
`ρ' = -(1 - K/2) ρ - (K/2) ρ³` at `t`, and the phase `r / |r|` has derivative `0` at `t`.

Source: Ott and Antonsen (2008), Eq. (10). -/
theorem_wanted hasDerivAt_norm_order (K ω₀ : ℝ) (r : ℝ → ℂ) (t : ℝ)
    (hr : HasDerivAt r (orderField K 0 ω₀ ω₀ (r t)) t) (hr0 : r t ≠ 0) :
    HasDerivAt (fun s => ‖r s‖) (-(1 - K / 2) * ‖r t‖ - K / 2 * ‖r t‖ ^ 3) t ∧
      HasDerivAt (fun s => r s / (‖r s‖ : ℂ)) 0 t

end WantedExt.Biology.Neuroscience.OttAntonsenWanted
