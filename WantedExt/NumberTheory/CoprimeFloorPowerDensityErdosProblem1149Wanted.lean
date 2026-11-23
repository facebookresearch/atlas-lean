/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Density of `n` coprime to `⌊n^α⌋` (Erdős Problem 1149)

Erdős Problem 1149: let `α > 0` be a real number, not an integer. The density of integers `n ≥ 1`
for which `gcd(n, ⌊n^α⌋) = 1` is `6/π²`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.CoprimeFloorPowerDensityErdosProblem1149Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1149, https://www.erdosproblems.com/1149 (status
PROVED). UnsolvedMath record UM-30007190 (`EP-1149`), dataset ulamai/UnsolvedMath v1.8.0.

Natural density is the repository's `Set.HasDensity`. Compared with the formal-conjectures statement
`ErdosProblems/1149.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 1149: for every real `α > 0` that is not an integer, the integers `n ≥ 1` with
`gcd(n, ⌊n^α⌋) = 1` have natural density `6 / π²`. -/
def coprimeFloorPowerDensity : Prop :=
  ∀ α : ℝ, 0 < α → α ∉ Set.range ((↑) : ℤ → ℝ) →
    {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

/--
Resolved true: Bergelson and Richter proved (Theorem 1) that if `f` belongs to a Hardy field, `log t
log₄ t ≺ f(t)` and `t^{j-1} ≺ f(t) ≺ t^j` for some `j ∈ ℕ`, then the `n` with `gcd(n, ⌊f(n)⌋) = 1`
have natural density `6/π²`; `f(t) = t^α` with `α > 0` not an integer satisfies both conditions with
`j = ⌈α⌉`. erdosproblems.com/1149 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #1149, https://www.erdosproblems.com/1149 (status PROVED); resolution: V. Bergelson and F.
K. Richter, On the density of coprime tuples of the form (n, ⌊f_1(n)⌋, ..., ⌊f_k(n)⌋), where f_1,
..., f_k are functions from a Hardy field, in Number Theory - Diophantine Problems, Uniform
Distribution and Applications, Springer (2017), 109-135, Theorem 1 (for f in a Hardy field with log
t log₄ t ≺ f(t) and t^{j-1} ≺ f(t) ≺ t^j for some j ∈ ℕ, the n with gcd(n, ⌊f(n)⌋) = 1 have density
6/π²; f(t) = t^α, α > 0 not an integer, satisfies both conditions with j = ⌈α⌉);
erdosproblems.com/1149, https://arxiv.org/abs/1611.08044.
-/
public theorem_wanted coprimeFloorPowerDensity_holds : coprimeFloorPowerDensity

end MathlibExt.NumberTheory.CoprimeFloorPowerDensityErdosProblem1149Wanted
