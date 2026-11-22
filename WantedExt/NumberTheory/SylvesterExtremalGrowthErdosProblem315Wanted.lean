/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Growth of Egyptian expansions of 1 other than Sylvester's (Erdős Problem 315)

Erdős Problem 315: let `u₁ = 1`, `u_{n+1} = u_n (u_n + 1)`, so that `∑_{k ≥ 1} 1/(u_k + 1) = 1`, and
`c₀ = lim u_n^{1/2^n} = 1.264085…`. If `a₁ < a₂ < ⋯` is any other sequence with `∑ 1/a_k = 1`, is
`liminf a_n^{1/2^n} < c₀`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.SylvesterExtremalGrowthErdosProblem315Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #315, https://www.erdosproblems.com/315 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 41. UnsolvedMath record UM-30006823 (`EP-315`), dataset ulamai/UnsolvedMath v1.8.0.

Sequences are indexed from `0` (`a i = a_{i+1}`, exponent `1/2^{i+1}`); "any other sequence" means a
strictly increasing sequence of positive integers different from `u_k + 1` (Sylvester's sequence).
`c₀` is `limUnder` of `u_n^{1/2^n}` (the limit exists). `liminf < c₀` is stated as: some `c < c₀`
exceeds `a_n^{1/2^n}` infinitely often, which is the extended-real `liminf` and avoids
`Filter.liminf` junk values. Compared with the formal-conjectures statement `ErdosProblems/315.lean`
(equivalent; no code imported).
-/

open Filter

/-- `u₁ = 1`, `u_{n+1} = u_n (u_n + 1)`, indexed from `0` (`sylvesterPred i = u_{i+1}`):
`1, 2, 6, 42, …`; `u_n + 1` is Sylvester's sequence `2, 3, 7, 43, …`. -/
def sylvesterPred : ℕ → ℕ
  | 0 => 1
  | n + 1 => sylvesterPred n * (sylvesterPred n + 1)

/-- The Vardi constant `c₀ = lim u_n^{1/2^n} = 1.264085…` (term `i` is `u_{i+1}^{1/2^{i+1}}`). -/
noncomputable def vardiConstant : ℝ :=
  limUnder atTop fun i : ℕ => (sylvesterPred i : ℝ) ^ ((1 : ℝ) / 2 ^ (i + 1))

/-- Erdős Problem 315: every strictly increasing sequence of positive integers `a₁ < a₂ < ⋯` with
`∑ 1/a_k = 1`, other than `a_k = u_k + 1`, has `liminf a_n^{1/2^n} < c₀`; stated as: some
`c < c₀` exceeds `a_n^{1/2^n}` for infinitely many `n` (`a i` is `a_{i+1}`). -/
def sylvesterExtremalLiminf : Prop :=
  ∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) → HasSum (fun i => (1 : ℝ) / a i) 1 →
    a ≠ (fun i => sylvesterPred i + 1) →
      ∃ c : ℝ, c < vardiConstant ∧ ∃ᶠ i in atTop, (a i : ℝ) ^ ((1 : ℝ) / 2 ^ (i + 1)) < c

/--
Resolved true: Li and Tang, and independently Kamio, proved that every strictly increasing sequence
of positive integers with `∑ 1/a_k = 1` other than Sylvester's has `liminf a_n^{1/2^n} < c₀`.
erdosproblems.com/315 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#315, https://www.erdosproblems.com/315 (status PROVED (LEAN)); P. Erdős and R. L. Graham, Old and
new problems and results in combinatorial number theory (1980), p. 41; resolution: Z. Li and Q.
Tang, On a conjecture of Erdős and Graham about the Sylvester's sequence, arXiv:2503.12277 (2025);
Y. Kamio, Asymptotic analysis of infinite decompositions of a unit fraction into unit fractions,
arXiv:2503.02317 (2025), Li-Tang, abstract: for any positive integer sequence a_1 < a_2 < ⋯ other
than Sylvester's with ∑ 1/a_i = 1, liminf a_n^{1/2^n} < lim u_n^{1/2^n} = c_0; proved independently
by Kamio, https://arxiv.org/abs/2503.12277.
-/
public theorem_wanted sylvesterExtremalLiminf_holds : sylvesterExtremalLiminf

end MathlibExt.NumberTheory.SylvesterExtremalGrowthErdosProblem315Wanted
