/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximum term versus maximum modulus (Erdős Problem 227)

Erdős Problem 227: let `f = ∑_{n ≥ 0} a_n zⁿ` be an entire function that is not a polynomial. If
`lim_{r → ∞} max_n |a_n rⁿ| / max_{|z| = r} |f(z)|` exists, must it be `0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.MaximumTermRatioLimitErdosProblem227Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #227, https://www.erdosproblems.com/227 (status
DISPROVED). UnsolvedMath record UM-30006779 (`EP-227`), dataset ulamai/UnsolvedMath v1.8.0.

An entire function is a power series converging on `ℂ`, and not a polynomial means infinitely many
nonzero coefficients. The maximum term `μ(r)` and the maximum modulus `M(r)` are real suprema,
defined for arbitrary coefficients and every real `r`; when the series converges on `ℂ` and
`r ≥ 0` both are attained, so they are the classical maxima.
-/

open Filter Topology

/-- The real supremum `μ(r) = sup_n |a_n| r^n`, for arbitrary coefficients `a` and real `r`: `0`
when the family is not bounded above, and not attained in general (for `r = 1` and
`a_n = 1 - 1/(n+2)` it is `1`, which no term equals). When the power series `∑ a_n z^n` converges
on `ℂ` and `r ≥ 0`, the terms are nonnegative and tend to `0`, so the supremum is attained and is
the maximum term `max_n |a_n| r^n`. -/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖a n‖ * r ^ n

/-- The real supremum `M(r) = sup_{|z| = r} |∑' n, a_n z^n|` over the circle of radius `r`, where
the unconditional sum is `0` where the series does not converge and the supremum of an empty family
or of one not bounded above is `0`; in particular `M(r) = 0` for `r < 0`. When the series
converges on `ℂ` (`f(z) = ∑ a_n z^n` entire) and `r ≥ 0`, `|f|` is continuous on the compact
circle, so the supremum is attained and is the maximum modulus `max_{|z| = r} |f(z)|`. -/
noncomputable def maxModulus (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) r, ‖∑' n : ℕ, a n * (z : ℂ) ^ n‖

/-- Erdős Problem 227: for every entire `f(z) = ∑ a_n z^n` that is not a polynomial (the series
converges everywhere and infinitely many `a_n ≠ 0`), if `μ(r) / M(r)` has a limit as `r → ∞`, the
limit is `0`. -/
def maximumTermRatioLimitIsZero : Prop :=
  ∀ a : ℕ → ℂ, (∀ z : ℂ, Summable (fun n => a n * z ^ n)) → {n | a n ≠ 0}.Infinite →
    ∀ L : ℝ, Tendsto (fun r => maxTerm a r / maxModulus a r) atTop (𝓝 L) → L = 0

/--
Resolved false: Clunie and Hayman showed that for transcendental entire `f(z) = ∑ a_n z^n` the limit
of `μ(r) / M(r)` as `r → ∞` can take any value in `[0, 1/2]`, so any such `f` with a nonzero limit
is a counterexample. (The answer yes when all `a_n ≥ 0` is an unpublished result attributed to
Clunie, not a published proof.) erdosproblems.com/227 lists the problem as disproved. Source:
T. F. Bloom, Erdős Problems, Problem #227, https://www.erdosproblems.com/227
(status DISPROVED); resolution: J. Clunie and W. K. Hayman, The maximum term of a power series, J.
Analyse Math. 12 (1964), 143-186, erdosproblems.com/227: disproved by Clunie and Hayman, who showed
that the limit can take any value in [0, 1/2], https://doi.org/10.1007/BF02807433.
-/
public theorem_wanted maximumTermRatioLimitIsZero_refuted : ¬ maximumTermRatioLimitIsZero

end MathlibExt.Analysis.MaximumTermRatioLimitErdosProblem227Wanted
