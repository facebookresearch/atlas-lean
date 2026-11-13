/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unimodality of the density of integers with one divisor in an interval (Erdős Problem 692)

Erdős Problem 692: let `δ₁(n, m)` be the density of the set of integers with exactly one divisor in
`(n, m)`. Is `δ₁(n, m)` unimodular for `m > n + 1` (i.e. increases until some `m` then decreases
thereafter)? For fixed `n`, where does `δ₁(n, m)` achieve its maximum?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ExactlyOneDivisorDensityErdosProblem692Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #692, https://www.erdosproblems.com/692 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006981 (`EP-692`), dataset ulamai/UnsolvedMath v1.8.0.

`(n, m)` is the open interval `{n + 1, …, m - 1}`. `δ₁(n, m)` is the natural density, the limit
(`Filter.limUnder`) of the proportion of `x < N` in the set, which exists because the set is
periodic modulo `lcm(n + 1, …, m - 1)`. Unimodal on `m ≥ n + 2` means weakly increasing up to some
index and weakly decreasing from it on. The first question is stated for every `n ≥ 1` and refuted;
Cambie's positive case `n = 1` is a second target; the location of the maximum (second question) is
not formalized.
-/

/-- The set of positive integers with exactly one divisor in the open interval `(n, m)`, i.e.
among `n + 1, …, m - 1`. -/
def exactlyOneDivisorIn (n m : ℕ) : Set ℕ :=
  {x | 0 < x ∧ ((Finset.Ioo n m).filter (· ∣ x)).card = 1}

/-- `δ₁(n, m)`: the natural density of `exactlyOneDivisorIn n m`, the limit of the proportion of
`x < N` in the set. The set is periodic modulo `lcm(n + 1, …, m - 1)`, so the limit exists. -/
noncomputable def deltaOne (n m : ℕ) : ℝ :=
  Filter.limUnder Filter.atTop fun N : ℕ => ((exactlyOneDivisorIn n m ∩ Set.Iio N).ncard : ℝ) / N

/-- A sequence `f` is unimodal on `m ≥ a`: it increases (weakly) up to some index `M` and
decreases (weakly) from `M` on. -/
def UnimodalFrom (f : ℕ → ℝ) (a : ℕ) : Prop :=
  ∃ M : ℕ, (∀ m, a ≤ m → m < M → f m ≤ f (m + 1)) ∧ (∀ m, a ≤ m → M ≤ m → f (m + 1) ≤ f m)

/-- Erdős Problem 692, first question: for every `n ≥ 1` the sequence `δ₁(n, m)`, `m > n + 1`, is
unimodal. -/
def exactlyOneDivisorDensityUnimodal : Prop :=
  ∀ n : ℕ, 1 ≤ n → UnimodalFrom (deltaOne n) (n + 2)

/-- Cambie's positive case `n = 1`: `δ₁(1, m)` is non-increasing in `m ≥ 3`. -/
def exactlyOneDivisorDensityAntitoneAtOne : Prop :=
  ∀ m : ℕ, 3 ≤ m → deltaOne 1 (m + 1) ≤ deltaOne 1 m

/--
Resolved false: Cambie computed `δ₁(3, 6) = 7/20`, `δ₁(3, 7) = 1/3` and `δ₁(3, 8) = 38/105`, so
`δ₁(3, 7) < min(δ₁(3, 6), δ₁(3, 8))` and the sequence `(δ₁(3, m))_{m ≥ 5}` is not unimodal; by
computer it is not unimodal for any `2 ≤ n ≤ 20`, and Cambie's Theorem 3 gives `ω(exp(n^c))` local
maxima for large `n`. erdosproblems.com/692 lists the problem as disproved. Source: T. F. Bloom,
Erdős Problems, Problem #692, https://www.erdosproblems.com/692 (status DISPROVED (LEAN));
resolution: S. Cambie, Resolution of Erdős' problems about unimodularity, arXiv:2501.10333 (2025),
Section 1: δ₁(3, 6) = 7/20, δ₁(3, 7) = 1/3, δ₁(3, 8) = 38/105, so (δ₁(3, m))_{m ≥ 5} is not unimodal
(computer check: not unimodal for 2 ≤ n ≤ 20); Theorem 1: δ₁(1, m) is non-increasing in m; Theorem
3: (δ₁(n, m))_{m ≥ n+2} has ω(exp(n^c)) local maxima, https://arxiv.org/abs/2501.10333.
-/
public theorem_wanted exactlyOneDivisorDensityUnimodal_refuted : ¬ exactlyOneDivisorDensityUnimodal

/--
Resolved true: Cambie's Theorem 1: the sequence `δ₁(1, m)` (the density of integers with exactly one
divisor in `{2, …, m - 1}`) is non-increasing in `m`, hence unimodal; this is the one case in which
Erdős's question has a positive answer. Source: T. F. Bloom, Erdős Problems, Problem #692,
https://www.erdosproblems.com/692 (status DISPROVED (LEAN)); resolution: S. Cambie, Resolution of
Erdős' problems about unimodularity, arXiv:2501.10333 (2025), Section 1: δ₁(3, 6) = 7/20, δ₁(3, 7) =
1/3, δ₁(3, 8) = 38/105, so (δ₁(3, m))_{m ≥ 5} is not unimodal (computer check: not unimodal for 2 ≤
n ≤ 20); Theorem 1: δ₁(1, m) is non-increasing in m; Theorem 3: (δ₁(n, m))_{m ≥ n+2} has ω(exp(n^c))
local maxima, https://arxiv.org/abs/2501.10333.
-/
public theorem_wanted exactlyOneDivisorDensityAntitoneAtOne_holds :
    exactlyOneDivisorDensityAntitoneAtOne

end MathlibExt.NumberTheory.ExactlyOneDivisorDensityErdosProblem692Wanted
