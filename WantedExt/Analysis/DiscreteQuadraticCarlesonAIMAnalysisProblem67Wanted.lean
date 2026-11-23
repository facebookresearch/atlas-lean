/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The discrete quadratic Carleson operator on ℓ² (AIM multilinear operators workshop, Question 8)

AIM workshop Carleson theorems and multilinear operators, Question 8 (Anderson, Pierce): the
discrete analogue of the Stein-Wainger polynomial Carleson theorem, `‖sup_λ |∑_m f(n - m) e^{iλm²} /
m|‖_{ℓ²_n} ≲ ‖f‖_{ℓ²}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace MathlibExt.Analysis.DiscreteQuadraticCarlesonAIMAnalysisProblem67Wanted

/-!
Source: AIM workshop Carleson theorems and multilinear operators (2015), open problems compiled by
S. Guo, https://aimath.org/pastworkshops/multilinopsproblems.pdf, Question 8 (T. Anderson, L.
Pierce). UnsolvedMath record UM-20000535 (`AIM-ANALYSIS-0067`), dataset ulamai/UnsolvedMath v1.8.0.

The `m = 0` term is omitted (it is undefined). The estimate is stated on finitely supported `f`,
which are dense in `ℓ²(ℤ)` and make every inner sum finite; the supremum over `λ ∈ ℝ` is linearized
by an arbitrary choice `λ = t(n)` for each `n`, and the `ℓ²` sum is bounded on every window `|n| ≤
N`, which together are equivalent to the displayed bound. The phase `e^{iλm²}` is Krause and Roos's
`e(λ m²) = e^{2πiλm²}` after rescaling `λ`, which does not change the supremum over `λ ∈ ℝ`.
-/

/-- `∑_{m ≠ 0} f(n - m) e^{i t m²} / m` for a finitely supported `f : ℤ → ℂ`, written as a sum
over `k = n - m` in the support of `f`. -/
noncomputable def quadraticModulatedHilbert (f : ℤ →₀ ℂ) (n : ℤ) (t : ℝ) : ℂ :=
  ∑ k ∈ f.support.filter (· ≠ n),
    f k * Complex.exp (Complex.I * t * ((n - k : ℤ) : ℂ) ^ 2) / ((n - k : ℤ) : ℂ)

/-- The AIM question (Carleson theorems and multilinear operators, Problem 8, L. Pierce): the
discrete quadratic Carleson operator `f ↦ sup_t |∑_{m ≠ 0} f(n - m) e^{i t m²} / m|` is bounded
on `ℓ²(ℤ)`, stated on finitely supported `f` with the supremum linearized (an arbitrary
`t = t(n)` for each `n`) and over the finite windows `|n| ≤ N`. -/
def discreteQuadraticCarleson : Prop :=
  ∃ C : ℝ, ∀ (f : ℤ →₀ ℂ) (t : ℤ → ℝ) (N : ℕ),
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖quadraticModulatedHilbert f n (t n)‖ ^ 2 ≤
      C * ∑ k ∈ f.support, ‖f k‖ ^ 2

/--
Resolved true: Krause and Roos proved `ℓ²(ℤⁿ)` bounds for `sup_λ |∑_{y ≠ 0} f(x - y) e(λ|y|^{2d})
K(y)|`; the case `n = d = 1`, `K(y) = 1/y` (`Ω = sign`, mean zero on `S⁰`) is this question, which
they credit to Lillian Pierce at the 2015 AIM workshop. Source: AIM workshop Carleson theorems and
multilinear operators (2015), open problems compiled by S. Guo,
https://aimath.org/pastworkshops/multilinopsproblems.pdf, Question 8 (T. Anderson, L. Pierce);
resolution: B. Krause and J. Roos, Discrete analogues of maximally modulated singular integrals of
Stein-Wainger type, J. Eur. Math. Soc. 24 (2022), 3183-3213, arXiv:1907.00405, Theorem 1.1:
sup_{λ∈R} |Σ_{y∈Z^n∖{0}} f(x - y) e(λ|y|^{2d}) K(y)| is bounded on ℓ^2(Z^n) for a homogeneous
Calderón-Zygmund kernel K(x) = Ω(x)/|x|^n (Ω smooth, degree 0, mean zero on the sphere); n = d = 1,
K(y) = 1/y is the case Lillian Pierce asked at the 2015 AIM workshop,
https://doi.org/10.4171/jems/1160.
-/
public theorem_wanted discreteQuadraticCarleson_holds : discreteQuadraticCarleson

end MathlibExt.Analysis.DiscreteQuadraticCarlesonAIMAnalysisProblem67Wanted
