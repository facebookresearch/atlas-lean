/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Short asymptotic paths of entire functions of finite order (Erdős Problem 1115)

Erdős Problem 1115: let `f` be an entire function of finite order and `Γ` a rectifiable path on
which `f(z) → ∞`, with `ℓ(r)` the length of `Γ` in `|z| < r`. Find a path for which `ℓ(r)` grows as
slowly as possible. In particular, can such a path be found for which `ℓ(r) ≪ r`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.EntireAsymptoticPathLengthErdosProblem1115Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1115, https://www.erdosproblems.com/1115 (status
SOLVED). UnsolvedMath record UM-30007165 (`EP-1115`), dataset ulamai/UnsolvedMath v1.8.0.

Only the yes/no question is formalized. `f` is non-constant, since a constant has no path with `f →
∞`. Finite order is `log M(r) = O(r^ρ)`. A rectifiable path to `∞`, parametrized by arc length, is a
`1`-Lipschitz `γ` on `[0, ∞)`; for such `γ` the length inside `|z| < r` is at most the measure of
`{t ≥ 0 : |γ(t)| < r}`, with equality for unit speed, so bounding that measure by `C r` for some
such `γ` is the same as `ℓ(r) ≪ r` for some path.
-/

/-- `f` has finite order: `log M(r) = O(r^ρ)` for some `ρ`, written `|f(z)| ≤ exp(C (1 + |z|)^ρ)`.
-/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ C : ℝ, ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)

/-- Erdős Problem 1115, the question "can such a path be found with `ℓ(r) ≪ r`": every non-constant
entire function of finite order tends to `∞` along a rectifiable path `Γ` whose length `ℓ(r)` inside
`|z| < r` is `O(r)`. Paths are parametrized by arc length, so `Γ` is a `1`-Lipschitz map `γ` on
`[0, ∞)` and `ℓ(r)` is at most the measure of `{t ≥ 0 : |γ(t)| < r}`, with equality for unit
speed. -/
def asymptoticPathOfLinearLength : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → HasFiniteOrder f → (∃ z w, f z ≠ f w) →
    ∃ γ : ℝ → ℂ, LipschitzWith 1 γ ∧
      Filter.Tendsto (fun t => ‖f (γ t)‖) Filter.atTop Filter.atTop ∧
      ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
        MeasureTheory.volume {t : ℝ | 0 ≤ t ∧ ‖γ t‖ < r} ≤ ENNReal.ofReal (C * r)

/--
Resolved false: Gol'dberg and Erëmenko constructed entire functions of finite order (indeed with
`log M(r) ≪ φ(r) (log r)²` for any `φ → ∞`) admitting no path `Γ` with `f → ∞` and `ℓ(r) ≪ r`,
answering Hayman's question (which he proved has a positive answer when `log M(r) ≪ (log r)²`).
erdosproblems.com/1115 records the disproof. Source: T. F. Bloom, Erdős Problems, Problem #1115,
https://www.erdosproblems.com/1115 (status SOLVED); resolution: A. A. Gol'dberg and A. È. Erëmenko,
Asymptotic curves of entire functions of finite order, Mat. Sb. (N.S.) (1979), 555-581, for every
φ(r) → ∞ there is an entire f with log M(r) ≪ φ(r) (log r)² and no path Γ with f → ∞ and ℓ(r) ≪ r;
also of any prescribed finite order (erdosproblems.com/1115), https://www.erdosproblems.com/1115.
-/
public theorem_wanted asymptoticPathOfLinearLength_refuted : ¬ asymptoticPathOfLinearLength

end MathlibExt.Analysis.EntireAsymptoticPathLengthErdosProblem1115Wanted
