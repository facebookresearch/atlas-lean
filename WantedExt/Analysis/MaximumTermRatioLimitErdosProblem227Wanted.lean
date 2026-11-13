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
nonzero coefficients. The maximum term `μ(r)` and the maximum modulus `M(r)` are real suprema, both
attained.
-/

open Filter Topology

/-- The maximum term `μ(r) = max_n |a_n| r^n` of the power series `∑ a_n z^n`. -/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖a n‖ * r ^ n

/-- The maximum modulus `M(r) = max_{|z| = r} |f(z)|` of `f(z) = ∑ a_n z^n`. -/
noncomputable def maxModulus (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) r, ‖∑' n : ℕ, a n * (z : ℂ) ^ n‖

/-- Erdős Problem 227: for every entire `f(z) = ∑ a_n z^n` that is not a polynomial (the series
converges everywhere and infinitely many `a_n ≠ 0`), if `μ(r) / M(r)` has a limit as `r → ∞`, the
limit is `0`. -/
def maximumTermRatioLimitIsZero : Prop :=
  ∀ a : ℕ → ℂ, (∀ z : ℂ, Summable (fun n => a n * z ^ n)) → {n | a n ≠ 0}.Infinite →
    ∀ L : ℝ, Tendsto (fun r => maxTerm a r / maxModulus a r) atTop (𝓝 L) → L = 0

/--
Resolved false: Clunie and Hayman showed that the limit of `μ(r) / M(r)` can take any value in `[0,
1/2]` (Clunie had proved the answer yes when all `a_n ≥ 0`); erdosproblems.com/227 lists the problem
as disproved. Source: T. F. Bloom, Erdős Problems, Problem #227, https://www.erdosproblems.com/227
(status DISPROVED); resolution: J. Clunie and W. K. Hayman, The maximum term of a power series, J.
Analyse Math. 12 (1964), 143-186, erdosproblems.com/227: disproved by Clunie and Hayman, who showed
that the limit can take any value in [0, 1/2], https://doi.org/10.1007/BF02807433.
-/
public theorem_wanted maximumTermRatioLimitIsZero_refuted : ¬ maximumTermRatioLimitIsZero

end MathlibExt.Analysis.MaximumTermRatioLimitErdosProblem227Wanted
