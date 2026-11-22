/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large components of polynomial lemniscates (Erdős Problem 511)

Erdős Problem 511: for monic `f ∈ ℂ[z]` and every `c > 1`, does `{z : |f(z)| < 1}` (in Erdős's 1961
version `{z : |f(z)| ≤ 1}`) have at most `O_c(1)` connected components of diameter `> c`,
independently of the degree?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.LemniscateLargeComponentsErdosProblem511Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #511, https://www.erdosproblems.com/511 (status
DISPROVED). UnsolvedMath record UM-30006910 (`EP-511`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for the closed lemniscate `{z : |f(z)| ≤ 1}`: erdosproblems.com/511 records that Erdős's 1961
version of the question uses `≤ 1`, and that is the form Pommerenke and Huang refute; the open form
`< 1` printed on the page is not claimed. Components are counted through representatives: points of
the lemniscate in pairwise distinct components of diameter `> c`.
-/

/-- The closed lemniscate `{z : |f(z)| ≤ 1}` of a complex polynomial `f`. -/
def closedLemniscate (f : Polynomial ℂ) : Set ℂ :=
  {z | ‖f.eval z‖ ≤ 1}

/-- Erdős Problem 511, in Erdős's 1961 form: for every `c > 1` there is `K` such that for every
monic `f ∈ ℂ[z]` (of any degree) the closed lemniscate `{|f| ≤ 1}` has at most `K` connected
components of diameter `> c`. Components are counted through representatives: points in pairwise
distinct components, each of diameter `> c`, number at most `K`. -/
def boundedLargeLemniscateComponents : Prop :=
  ∀ c : ℝ, 1 < c → ∃ K : ℕ, ∀ f : Polynomial ℂ, f.Monic → ∀ S : Finset ℂ,
    (∀ z ∈ S, z ∈ closedLemniscate f) →
    (∀ z ∈ S, ∀ w ∈ S, z ≠ w →
      connectedComponentIn (closedLemniscate f) z ≠ connectedComponentIn (closedLemniscate f) w) →
    (∀ z ∈ S, c < Metric.diam (connectedComponentIn (closedLemniscate f) z)) →
    S.card ≤ K

/--
Resolved false: Pommerenke (and independently Huang) proved that for every `0 < d < 4` and `k ≥ 1`
some monic polynomial has `{|f| ≤ 1}` with at least `k` connected components of diameter `≥ d`; any
`d ∈ (c, 4)` refutes the bound for `c ∈ (1, 4)`. Pólya showed no component has diameter `> 4`.
Source: T. F. Bloom, Erdős Problems, Problem #511, https://www.erdosproblems.com/511 (status
DISPROVED); resolution: Ch. Pommerenke, On metric properties of complex polynomials, Michigan Math.
J. (1961), 97-115; L. Huang, Many lemniscates with large diameter, arXiv:2509.11597 (2025),
erdosproblems.com/511 and Huang's abstract: for every 0 < d < 4 and k ≥ 1 some monic f has {|f| ≤ 1}
with at least k connected components of diameter ≥ d (Pommerenke; independently Huang),
https://arxiv.org/abs/2509.11597.
-/
public theorem_wanted boundedLargeLemniscateComponents_refuted : ¬ boundedLargeLemniscateComponents

end MathlibExt.Analysis.LemniscateLargeComponentsErdosProblem511Wanted
