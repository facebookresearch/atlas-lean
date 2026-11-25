/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual local log thresholds of affine hypersurfaces

The density is the literal real function |f(z)|^(-2c) on complex affine
space with its native Lebesgue measure. For a nonzero polynomial, the
threshold is the extended nonnegative supremum of c for which that density
is integrable on an actual neighborhood of the chosen point. A unit has
infinite threshold. Values assigned on its null zero set do not affect
integration. The zero polynomial has threshold zero by explicit convention.

Order at the point is computed from the actual translated polynomial:
the smallest total exponent with nonzero coefficient. No valuation,
threshold or integrability oracle is supplied.

Reference: Mustaţă, *IMPANGA lecture notes on log canonical thresholds*,
https://arxiv.org/abs/1107.2676, analytic description and order bounds.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineLogThresholds

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- The density `|f(z)|^(-2c)` on `ℂⁿ`. On the zero set of `f` and for `c ≠ 0` its value is `0`
(the convention `0 ^ x = 0` for real powers); for nonzero `f` this set is Lebesgue-null. -/
def density {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (c : ℝ)
    (z : Fin n → ℂ) : ℝ := ‖MvPolynomial.eval z f‖ ^ (-2 * c)

/-- `|f|^(-2c)` is Lebesgue integrable on some neighbourhood of `p`. -/
def IntegrableNear {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (c : ℝ)
    (p : Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin n → ℂ), U ∈ 𝓝 p ∧ IntegrableOn (density f c) U volume

/-- The log canonical threshold of `f` at `p`: the supremum of the `c ≥ 0` for which `|f|^(-2c)`
is integrable near `p`, in `[0, ∞]`. It is `∞` when `f(p) ≠ 0`, and `0` for `f = 0` by
convention. -/
def localThreshold {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (p : Fin n → ℂ) : ℝ≥0∞ := by
  classical
  exact if f = 0 then 0 else
    sSup {c : ℝ≥0∞ | ∃ r : ℝ, 0 ≤ r ∧ c = ENNReal.ofReal r ∧ IntegrableNear f r p}

/-- The translate `f(X + p)`, whose coefficients are the Taylor coefficients of `f` at `p`. -/
def translated {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i ↦ MvPolynomial.X i + MvPolynomial.C (p i)) f

/-- The order of vanishing of `f` at `p`: the least total degree of a monomial with nonzero
coefficient in `f(X + p)`. For `f = 0` the set is empty and the value is `0` by the `sInf`
convention, so this is only meaningful for `f ≠ 0`. -/
def orderAt {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ) : ℕ :=
  sInf {m : ℕ | ∃ a : Fin n →₀ ℕ,
    (translated f p).coeff a ≠ 0 ∧ (∑ i, a i) = m}

end MathlibExt.AlgebraicGeometry.AffineLogThresholds
