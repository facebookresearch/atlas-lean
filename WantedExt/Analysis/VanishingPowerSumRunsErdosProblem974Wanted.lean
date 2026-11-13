/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Power sums with infinitely many runs of zeros (Erdős Problem 974)

Erdős Problem 974: let `z_1, …, z_n ∈ ℂ` be a sequence such that `z_1 = 1`. Suppose that the
sequence of `s_k = ∑_{1 ≤ i ≤ n} z_i^k` contains infinitely many `(n - 1)`-tuples of consecutive
values of `s_k` which are all `0`. Then (essentially) `z_j = e(j/n)`, where `e(x) = e^{2πix}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace MathlibExt.Analysis.VanishingPowerSumRunsErdosProblem974Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #974, https://www.erdosproblems.com/974 (status PROVED
(LEAN)). UnsolvedMath record UM-30007105 (`EP-974`), dataset ulamai/UnsolvedMath v1.8.0.

'Essentially' is made precise by the classification recorded on erdosproblems.com: for odd `n` the
`z_i` are exactly the `n`-th roots of unity; for even `n` they are the vertices of two regular
`(n/2)`-gons with the same circumscribed circle centred at the origin, that is, since `z_1 = 1`, the
`(n/2)`-th roots of `1` together with the `(n/2)`-th roots of some `c ≠ 1` with `‖c‖ = 1`
(`IsTuranConfiguration`). The numbers are indexed by `Fin (n + 1)`, so that there are `n + 1` of
them and the runs have `n` zeros (`s_k = ⋯ = s_{k+n-1} = 0`), which avoids the empty case. Compared
with the formal-conjectures statement `ErdosProblems/974.lean` (`erdos_974`, equivalent; no code
imported).
-/

/-- The configuration in Tijdeman's theorem: if `n` is odd, the `z i` are exactly the `n`-th roots
of unity; if `n` is even, they are the vertices of two distinct regular `(n / 2)`-gons inscribed in
the unit circle, one of them the `(n / 2)`-th roots of unity and the other the `(n / 2)`-th roots of
some `c ≠ 1` with `‖c‖ = 1`. Since these sets have `n` elements, the `z i` are distinct. -/
def IsTuranConfiguration {n : ℕ} (z : Fin n → ℂ) : Prop :=
  (Odd n → Set.range z = {ζ : ℂ | ζ ^ n = 1}) ∧
    (Even n → ∃ c : ℂ, ‖c‖ = 1 ∧ c ≠ 1 ∧
      Set.range z = {ζ : ℂ | ζ ^ (n / 2) = 1} ∪ {ζ : ℂ | ζ ^ (n / 2) = c})

/-- Erdős Problem 974 (Turán's conjecture): if `z₁, …, z_n ∈ ℂ` (here indexed by `Fin (n + 1)`,
so `n + 1` numbers) with `z₁ = 1` and the power sums `s_k = ∑ z_i^k` contain infinitely many runs
of `n` consecutive zeros, then the `z_i` form the configuration of `IsTuranConfiguration`. -/
def vanishingPowerSumRunsConfiguration : Prop :=
  ∀ (n : ℕ) (z : Fin (n + 1) → ℂ), z 0 = 1 →
    {k : ℕ | ∀ j < n, ∑ i, z i ^ (k + j) = 0}.Infinite → IsTuranConfiguration z

/--
Resolved true: already two runs of `n - 1` vanishing power sums force the configuration (the `n`-th
roots of unity for odd `n`, two regular `(n/2)`-gons inscribed in the unit circle for even `n`), as
proved by Tijdeman and, without assuming the `z_i` distinct, by Hu, Tang and Zhang;
erdosproblems.com/974 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#974, https://www.erdosproblems.com/974 (status PROVED (LEAN)); resolution: R. Tijdeman, On a
conjecture of Turán and Erdős, Indag. Math. (1966), 374-383, erdosproblems.com/974: true even with
two such runs; for odd n the z_i are the n-th roots of unity, for even n the vertices of two regular
(n/2)-gons with the same circumscribed circle centred at the origin; first proved by Tijdeman, with
an independent proof by Hu, Tang and Zhang in the comments (whose Proposition 1 removes Tijdeman's
assumption that the z_i are distinct), https://www.erdosproblems.com/974.
-/
public theorem_wanted vanishingPowerSumRunsConfiguration_holds : vanishingPowerSumRunsConfiguration

end MathlibExt.Analysis.VanishingPowerSumRunsErdosProblem974Wanted
