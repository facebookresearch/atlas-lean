/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Control.NonlinearControl
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Wanted: the Rashevskii–Chow theorem and Brockett's condition

Two central theorems on finite-dimensional nonlinear control systems, recorded as
`theorem_wanted`:

* the Rashevskii–Chow theorem: the Lie algebra rank condition implies global controllability of
  driftless control-affine systems (Coron, *Control and Nonlinearity*, AMS 2007, Theorem 3.18);
* Brockett's necessary condition for local asymptotic stabilisation by continuous stationary
  feedback (Coron, Theorem 11.1).
-/

open Set
open scoped ContDiff

@[expose] public section

namespace MathlibExt.Analysis.Control.NonlinearControlWanted

/-- **Rashevskii–Chow theorem** (Rashevskii 1938, Chow 1939; Coron, *Control and Nonlinearity*,
AMS 2007, Theorem 3.18). Let `Ω` be a connected nonempty open subset of a finite-dimensional real
space `E` and let `f_1, …, f_m` be vector fields of class `C^∞` on `Ω` such that the Lie algebra
rank condition holds at every point of `Ω`. Then for all `x₀, x₁ ∈ Ω` and every `T > 0` there is a
bounded measurable control `u` whose trajectory of the driftless system `ẋ = ∑ u_i f_i(x)`
starting at `x₀` stays in `Ω` on `[0, T]` and ends at `x₁`. Trajectories are taken in the
Carathéodory sense: `x(t) = x₀ + ∫₀ᵗ ∑ u_i(s) f_i(x(s)) ds`. -/
theorem_wanted rashevskii_chow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (f : Fin m → E → E) {Ω : Set E} (hΩ : IsOpen Ω)
    (hconn : IsConnected Ω) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω)
    (hLie : ∀ x ∈ Ω, accessibilitySpace f x = ⊤) {x₀ x₁ : E} (hx₀ : x₀ ∈ Ω) (hx₁ : x₁ ∈ Ω)
    {T : ℝ} (hT : 0 < T) :
    ∃ u : ℝ → Fin m → ℝ, Measurable u ∧ (∃ C, ∀ t ∈ Icc 0 T, ‖u t‖ ≤ C) ∧
      ∃ x : ℝ → E, ContinuousOn x (Icc 0 T) ∧ (∀ t ∈ Icc 0 T, x t ∈ Ω) ∧ x 0 = x₀ ∧
        x T = x₁ ∧ ∀ t ∈ Icc 0 T, x t = x₀ + ∫ s in (0 : ℝ)..t, ∑ i, u s i • f i (x s)

/-- **Brockett's necessary condition for stabilisation** (Brockett 1983; Coron, *Control and
Nonlinearity*, AMS 2007, Theorem 11.1). Let `f : ℝⁿ × ℝᵐ → ℝⁿ` be of class `C^∞` with
`f(0, 0) = 0`. If `ẋ = f(x, u)` is locally asymptotically stabilisable by continuous stationary
feedback laws, then the image under `f` of every neighbourhood of `(0, 0)` is a neighbourhood of
`0`. (Coron allows `f` to be defined only on an open neighbourhood of `(0, 0)`; this is the case
where `f` is defined and smooth everywhere.) -/
theorem_wanted brockettCondition_of_isLocallyAsymptoticallyStabilizable {E U : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    (f : E × U → E) (hf : ContDiff ℝ ∞ f) (h0 : f (0, 0) = 0)
    (hstab : IsLocallyAsymptoticallyStabilizable f) :
    BrockettCondition f

end MathlibExt.Analysis.Control.NonlinearControlWanted
