/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `L¹` norm of real-rooted trigonometric polynomials (Erdős Problem 225)

Erdős Problem 225: let `f(θ) = ∑_{0 ≤ k ≤ n} c_k e^{ikθ}` be a trigonometric polynomial all of whose
roots are real, with `max_{θ ∈ [0, 2π]} |f(θ)| = 1`. Then `∫_0^{2π} |f(θ)| dθ ≤ 4`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MathlibExt.Analysis.RealRootedTrigPolynomialIntegralErdosProblem225Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #225, https://www.erdosproblems.com/225 (status
PROVED). UnsolvedMath record UM-30006777 (`EP-225`), dataset ulamai/UnsolvedMath v1.8.0.

Roots are zeros of `f` as an entire function of complex `θ`. The statement adds that `f` has a root:
a polynomial without roots is `c e^{imθ}`, for which `∫ |f| = 2π > 4`. Writing `∑ c_k z^k = z^m
Q(z)` with `Q(0) ≠ 0`, the roots of `f` correspond to the roots of `Q`, so the hypotheses say that
`Q` is nonconstant with all roots on the unit circle, the setting of Saff and Sheil-Small. Compared
with the formal-conjectures statement `ErdosProblems/225.lean` (normalized by `n ≥ 1`, `c₀ c_n ≠ 0`,
equivalent; no code imported).
-/

/-- The trigonometric polynomial `f(θ) = ∑_{k=0}^n c_k e^{ikθ}`, as a function of complex `θ`. -/
noncomputable def trigPoly (n : ℕ) (c : ℕ → ℂ) (θ : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), c k * Complex.exp (Complex.I * k * θ)

/-- Erdős Problem 225: if the trigonometric polynomial `f(θ) = ∑_{k=0}^n c_k e^{ikθ}` has roots and
all of them are real, and `max_{θ ∈ [0, 2π]} |f(θ)| = 1`, then `∫_0^{2π} |f(θ)| dθ ≤ 4`. -/
def realRootedTrigPolynomialIntegralLeFour : Prop :=
  ∀ (n : ℕ) (c : ℕ → ℂ), (∃ θ : ℂ, trigPoly n c θ = 0) →
    (∀ θ : ℂ, trigPoly n c θ = 0 → θ.im = 0) →
    (∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖trigPoly n c θ‖ ≤ 1) →
    (∃ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖trigPoly n c θ‖ = 1) →
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigPoly n c θ‖ ≤ 4

/--
Resolved true: Saff and Sheil-Small proved the bound for complex coefficients (Kristiansen
independently for real coefficients); equality holds for `f(θ) = (e^{iθ} - 1) / 2`.
erdosproblems.com/225 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#225, https://www.erdosproblems.com/225 (status PROVED); resolution: E. B. Saff and T. Sheil-Small,
Coefficient and integral mean estimates for algebraic and trigonometric polynomials with restricted
zeros, J. London Math. Soc. (2) 9 (1974), 16-22, erdosproblems.com/225: solved by Saff and
Sheil-Small for complex c_k (Kristiansen for real c_k), https://doi.org/10.1112/jlms/s2-9.1.16.
-/
public theorem_wanted realRootedTrigPolynomialIntegralLeFour_holds :
    realRootedTrigPolynomialIntegralLeFour

end MathlibExt.Analysis.RealRootedTrigPolynomialIntegralErdosProblem225Wanted
