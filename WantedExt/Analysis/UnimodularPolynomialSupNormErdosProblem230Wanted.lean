/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sup norm of unimodular polynomials (Erdős Problem 230)

Erdős Problem 230 (Erdős and Newman): let `P(z) = ∑_{1 ≤ k ≤ n} a_k z^k` with `|a_k| = 1`. Is there
`c > 0` such that `max_{|z| = 1} |P(z)| ≥ (1 + c) √n` for all `n ≥ 2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.UnimodularPolynomialSupNormErdosProblem230Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #230, https://www.erdosproblems.com/230 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006782 (`EP-230`), dataset ulamai/UnsolvedMath v1.8.0.

Coefficients are `a : ℕ → ℂ` with `|a_k| = 1` for `1 ≤ k ≤ n`; the maximum over the unit circle is a
real supremum. Compared with the formal-conjectures statement `ErdosProblems/230.lean` (equivalent;
no code imported).
-/

/-- `max_{|z| = 1} |∑_{k=1}^n a_k z^k|`. -/
noncomputable def circleSupNorm (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖∑ k ∈ Finset.Icc 1 n, a k * (z : ℂ) ^ k‖

/-- Erdős Problem 230 (Erdős and Newman): there is `c > 0` such that every polynomial
`P(z) = ∑_{k=1}^n a_k z^k` with `|a_k| = 1` and `n ≥ 2` has `max_{|z| = 1} |P(z)| ≥ (1 + c) √n`. -/
def unimodularPolynomialSupNormGap : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ a : ℕ → ℂ, (∀ k ∈ Finset.Icc 1 n, ‖a k‖ = 1) →
    (1 + c) * Real.sqrt n ≤ circleSupNorm n a

/--
Resolved false: Kahane constructed ultraflat polynomials with unimodular coefficients and `|P(z)| =
(1 + o(1)) √n` uniformly on `|z| = 1`, so no `c > 0` works; erdosproblems.com/230 lists the problem
as disproved. Source: T. F. Bloom, Erdős Problems, Problem #230, https://www.erdosproblems.com/230
(status DISPROVED (LEAN)); resolution: J.-P. Kahane, Sur les polynômes à coefficients unimodulaires,
Bull. London Math. Soc. 12 (1980), 321-342, Kahane's ultraflat polynomials: |P(z)| = (1 + o(1)) √n
uniformly on |z| = 1 (erdosproblems.com/230), https://doi.org/10.1112/blms/12.5.321.
-/
public theorem_wanted unimodularPolynomialSupNormGap_refuted : ¬ unimodularPolynomialSupNormGap

end MathlibExt.Analysis.UnimodularPolynomialSupNormErdosProblem230Wanted
