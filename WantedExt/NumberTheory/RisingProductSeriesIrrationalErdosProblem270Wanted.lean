/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irrationality of rising-product series (Erdős Problem 270)

Erdős Problem 270: let `f(n) → ∞`. Is `∑_{n ≥ 1} 1/((n + 1) ⋯ (n + f(n)))` irrational?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.RisingProductSeriesIrrationalErdosProblem270Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #270, https://www.erdosproblems.com/270 (status
DISPROVED (LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial
number theory (1980), p. 66. UnsolvedMath record UM-30006800 (`EP-270`), dataset ulamai/UnsolvedMath
v1.8.0.

`f : ℕ → ℕ` with `f n → ∞`; the term with index `m` is the source's term `n = m + 1`, i.e. `1 / ∏_{i
= n + 1}^{n + f n} i`. Since `f n ≥ 2` eventually, the series converges, so the `tsum` is the actual
sum. Compared with the formal-conjectures statement `ErdosProblems/270.lean` (equivalent; no code
imported).
-/

open Filter

/-- The series `∑_{n ≥ 1} 1 / ((n + 1)(n + 2) ⋯ (n + f n))`; the term with index `m` is the
source's term `n = m + 1`. -/
noncomputable def risingProductSeries (f : ℕ → ℕ) : ℝ :=
  ∑' m : ℕ, 1 / ∏ i ∈ Finset.Ioc (m + 1) (m + 1 + f (m + 1)), (i : ℝ)

/-- Erdős Problem 270: if `f n → ∞` then `∑_{n ≥ 1} 1 / ((n + 1) ⋯ (n + f n))` is irrational. -/
def risingProductSeriesIrrational : Prop :=
  ∀ f : ℕ → ℕ, Tendsto f atTop atTop → Irrational (risingProductSeries f)

/--
Resolved false: Crmarić and Kovač showed that for every `α ∈ (0, ∞)` some `f` with `f(n) → ∞` gives
`∑_{n ≥ 1} 1/((n + 1) ⋯ (n + f(n))) = α`; taking `α = 1` gives a rational sum (the non-decreasing
case remains open). erdosproblems.com/270 lists the problem as disproved. Source: T. F. Bloom, Erdős
Problems, Problem #270, https://www.erdosproblems.com/270 (status DISPROVED (LEAN)); P. Erdős and R.
L. Graham, Old and new problems and results in combinatorial number theory (1980), p. 66;
resolution: T. Crmarić and V. Kovač, On the irrationality of certain super-polynomially decaying
series, arXiv:2504.18712 (2025), abstract: negative answer to the Erdős-Graham question;
erdosproblems.com/270: for every α ∈ (0, ∞) some f : ℕ → ℕ with f(n) → ∞ makes the series equal to
α, https://arxiv.org/abs/2504.18712.
-/
public theorem_wanted risingProductSeriesIrrational_refuted : ¬ risingProductSeriesIrrational

end MathlibExt.NumberTheory.RisingProductSeriesIrrationalErdosProblem270Wanted
