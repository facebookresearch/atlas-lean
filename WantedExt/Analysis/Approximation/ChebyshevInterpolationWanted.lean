/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Approximation.ChebyshevLebesgue
public import MathlibExt.Analysis.Approximation.ChebyshevSeries
public import MathlibExt.Analysis.Approximation.Equioscillation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Chebyshev series and Chebyshev interpolation (wanted)

The convergence theory of Chebyshev series and Chebyshev interpolants on `[-1, 1]`, as in
L. N. Trefethen, *Approximation Theory and Approximation Practice* (ATAP), SIAM, 2013.

For `f : [-1, 1] → ℂ` the Chebyshev coefficients are
`a_k = (2/π) ∫_0^π f(cos θ) cos(k θ) dθ` for `k ≥ 1`, with `2/π` replaced by `1/π` for `k = 0`
(ATAP Chapter 3, after the substitution `x = cos θ`); `chebCoeff`. The Chebyshev projection
is the truncation `f_n = ∑_{k ≤ n} a_k T_k` (`chebProj`) and the Chebyshev interpolant `p_n` is
the polynomial of degree `≤ n` interpolating `f` at the `n + 1` Chebyshev points
`x_j = cos(j π / n)`, `0 ≤ j ≤ n` (`chebInterp`; Mathlib's `Polynomial.Chebyshev.node`).

The open Bernstein ellipse `E_ρ`, `ρ > 1`, is the open region bounded by the ellipse with foci
`±1` and semi-axis sum `ρ`, i.e. `{z : |z - 1| + |z + 1| < ρ + ρ⁻¹}` (ATAP Chapter 8);
`bernsteinEllipse`.

The definitions above and the convergence theorem for Lipschitz functions are provided by
`MathlibExt.Analysis.Approximation.ChebyshevSeries`.

The Lebesgue constant bound `sum_abs_lagrange_basis_chebyshev_le` (ATAP Theorem 15.2) is
provided by `MathlibExt.Analysis.Approximation.ChebyshevLebesgue`.

Wanted statements:

* `norm_chebCoeff_le_of_analytic` (ATAP Theorem 8.1): if `f` is analytic in `E_ρ` with
  `|f| ≤ M` there, then `|a_0| ≤ M` and `|a_k| ≤ 2 M ρ^{-k}` for `k ≥ 1`.
* `norm_sub_chebProj_le_of_analytic`, `norm_sub_chebInterp_le_of_analytic` (ATAP Theorem 8.2):
  under the same hypotheses `‖f - f_n‖ ≤ 2 M ρ^{-n} / (ρ - 1)` and
  `‖f - p_n‖ ≤ 4 M ρ^{-n} / (ρ - 1)` on `[-1, 1]`.
* `exists_equioscillates_of_continuousOn` (ATAP Theorem 10.1, the existence and necessity half
  of Chebyshev's equioscillation theorem): a continuous function on `[a, b]` has a polynomial
  approximation of degree `≤ n` that equioscillates at `n + 2` points. The sufficiency and
  uniqueness halves are proved in `MathlibExt.Analysis.Approximation.Equioscillation`
  (`not_lt_of_equioscillates`, `eq_of_equioscillates`).
* `abs_sub_chebInterp_le_of_near_best` (ATAP Theorem 16.1): Chebyshev interpolants are near-best,
  `‖f - p_n‖ ≤ (2 + (2/π) log(n + 1)) ‖f - q‖` for every polynomial `q` of degree `≤ n`.

The interpolation statements are recorded for `n ≥ 1`, where the Chebyshev points are distinct.

For the minimax property `2^{1-n} T_n` that underlies these bounds see
`MathlibExt.Analysis.Approximation.ChebyshevMinimax` (proved), and for best approximation
`MathlibExt.Analysis.Approximation.Equioscillation`.

## References

* L. N. Trefethen, *Approximation Theory and Approximation Practice*, SIAM, 2013 (extended
  edition 2019), Theorems 3.1, 8.1, 8.2, 10.1, 15.2 and 16.1.
* A. Townsend, lecture notes for Cornell Math 6220 (2020, notes by D. Lim),
  https://cptq.github.io/other/math_6220.pdf, Lectures 1–3 (statements of ATAP Theorems 3.1,
  7.2, 8.1–8.2 and the near-best bound).
-/

@[expose] public section

open Polynomial Real

namespace MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted

/-- **Chebyshev coefficients of analytic functions** (ATAP Theorem 8.1): if `f` is analytic in the
open Bernstein ellipse `E_ρ`, `ρ > 1`, with `|f| ≤ M` there, then `|a_0| ≤ M` and
`|a_k| ≤ 2 M ρ^{-k}` for `k ≥ 1`. -/
theorem_wanted norm_chebCoeff_le_of_analytic {ρ M : ℝ} (hρ : 1 < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (bernsteinEllipse ρ))
    (hM : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) :
    ‖chebCoeff (fun x => f x) 0‖ ≤ M ∧
      ∀ k : ℕ, 1 ≤ k → ‖chebCoeff (fun x => f x) k‖ ≤ 2 * M * (ρ ^ k)⁻¹

/-- **Convergence of Chebyshev projections for analytic functions** (ATAP Theorem 8.2, first
bound): under the hypotheses of Theorem 8.1, `|f(x) - f_n(x)| ≤ 2 M ρ^{-n} / (ρ - 1)` on
`[-1, 1]`. -/
theorem_wanted norm_sub_chebProj_le_of_analytic {ρ M : ℝ} (hρ : 1 < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (bernsteinEllipse ρ))
    (hM : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    ‖f x - chebProj (fun y => f y) n x‖ ≤ 2 * M * (ρ ^ n)⁻¹ / (ρ - 1)

/-- **Convergence of Chebyshev interpolants for analytic functions** (ATAP Theorem 8.2, second
bound): under the hypotheses of Theorem 8.1, `|f(x) - p_n(x)| ≤ 4 M ρ^{-n} / (ρ - 1)` on
`[-1, 1]`, for `n ≥ 1`. -/
theorem_wanted norm_sub_chebInterp_le_of_analytic {ρ M : ℝ} (hρ : 1 < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (bernsteinEllipse ρ))
    (hM : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    ‖f x - (chebInterp (fun y => f y) n).eval (x : ℂ)‖ ≤ 4 * M * (ρ ^ n)⁻¹ / (ρ - 1)

/-- **Existence and equioscillation of the best approximation** (ATAP Theorem 10.1, the
existence and necessity half of Chebyshev's equioscillation theorem): if `f` is continuous on
`[a, b]` with `a < b`, there are a polynomial `p` of degree `≤ n`, an amplitude `E`, a sign
`σ = ±1` and points `x_0 < ⋯ < x_{n+1}` in `[a, b]` at which `f - p` equioscillates with
`|f - p| ≤ E` on `[a, b]`. By `Equioscillation.not_lt_of_equioscillates` and
`Equioscillation.eq_of_equioscillates`, this `p` is the unique best approximation. -/
theorem_wanted exists_equioscillates_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (n : ℕ) :
    ∃ (p : ℝ[X]) (E σ : ℝ) (x : ℕ → ℝ),
      MathlibExt.Analysis.Approximation.Equioscillation.Equioscillates f a b n p E σ x

/-- **Chebyshev interpolants are near-best** (ATAP Theorem 16.1): for `n ≥ 1`, if a polynomial
`q` of degree `≤ n` satisfies `|f - q| ≤ E` on `[-1, 1]`, then the Chebyshev interpolant
`p_n` of the real function `f` satisfies `|f - p_n| ≤ (2 + (2/π) log(n + 1)) E` there.
Taking `q` the best approximation gives the usual form `‖f - p_n‖ ≤ (2 + (2/π) log(n + 1))
‖f - p_n^*‖`. -/
theorem_wanted abs_sub_chebInterp_le_of_near_best {f : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    {q : ℝ[X]} (hq : q.natDegree ≤ n) {E : ℝ}
    (hE : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |f y - q.eval y| ≤ E) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    |f x - (Lagrange.interpolate (Finset.univ : Finset (Fin (n + 1)))
        (fun j => Chebyshev.node n j) (fun j => f (Chebyshev.node n j))).eval x| ≤
      (2 + 2 / π * Real.log (n + 1)) * E

end MathlibExt.Analysis.Approximation.ChebyshevInterpolationWanted
