/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Number of favourite sites of planar simple random walk (Erdős Problem 1166)

Erdős Problem 1166: for simple random walk `s₀, s₁, …` on `ℤ²` from the origin, let `f_k(x) = #{0 ≤
l ≤ k : s_l = x}` and let `F(k)` be the set of `x` maximizing `f_k`. Is `|⋃_{k ≤ n} F(k)| ≤ (log
n)^{O(1)}` almost surely, for all but finitely many `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace MathlibExt.Probability.RandomWalkFavouriteSitesErdosProblem1166Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1166, https://www.erdosproblems.com/1166 (status
PROVED). UnsolvedMath record UM-30007207 (`EP-1166`), dataset ulamai/UnsolvedMath v1.8.0.

The walk is given by independent steps `X i`, each uniform on the four unit vectors, on an arbitrary
probability space (the statement quantifies over all such spaces), and `s_k = X 0 + ⋯ + X (k - 1)`.
`(log n)^{O(1)}` is read with a deterministic exponent `C`, the stronger reading. formal-conjectures
has no statement.
-/

open MeasureTheory ProbabilityTheory Filter

/-- The four unit steps of the lattice `ℤ × ℤ`. -/
def unitSteps : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- Position after `k` steps, `s_k = X 0 + ⋯ + X (k - 1)` (so `s_0 = 0`). -/
def walkPosition (X : ℕ → ℤ × ℤ) (k : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range k, X i

/-- Local time `f_k(x)`: the number of `0 ≤ l ≤ k` with `s_l = x`. -/
def localTime (X : ℕ → ℤ × ℤ) (k : ℕ) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (k + 1)).filter fun l => walkPosition X l = x).card

/-- The favourite sites at time `k`: the sites of maximal local time. -/
def favouriteSites (X : ℕ → ℤ × ℤ) (k : ℕ) : Set (ℤ × ℤ) :=
  {x | ∀ y, localTime X k y ≤ localTime X k x}

/-- Erdős Problem 1166: there is `C` such that for simple random walk on `ℤ²` (independent steps,
each uniform on the four unit steps, on any probability space) almost surely, for all large `n`,
at most `(log n)^C` sites are favourite at some time `k ≤ n`. -/
def favouriteSitesPolylogarithmic : Prop :=
  ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℤ × ℤ), (∀ i, Measurable (X i)) → iIndepFun X P →
      (∀ i, ∀ v ∈ unitSteps, P (X i ⁻¹' {v}) = 1 / 4) →
      ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
        ((⋃ k ∈ Finset.range (n + 1), favouriteSites (fun i => X i ω) k).ncard : ℝ) ≤
          Real.log n ^ C

/--
Resolved true: erdosproblems.com/1166 derives `|⋃_{k ≤ n} F(k)| ≪ (log n)²` almost surely from two
theorems: almost surely `|F(n)| ≤ 3` for all large `n` (Hao, Li, Okada and Zheng, Theorem 1.1: in
dimension `2`, `limsup_n |F(n)| = 3` almost surely) and the maximal local time `T_n = max_x f_n(x)`
is almost surely `≪ (log n)²` (Erdős and Taylor; Dembo, Peres, Rosen and Zeitouni: `T_n / (log n)² →
1/π`). While `T_k` stays at a level, favourite sites only accumulate, so each level adds at most `3`
sites once `|F(k)| ≤ 3`; hence `|⋃_{k ≤ n} F(k)| ≤ R + 3 T_n` with `R` almost surely finite, below
`(log n)³` for large `n`. Source: T. F. Bloom, Erdős Problems, Problem #1166,
https://www.erdosproblems.com/1166 (status PROVED); resolution: C. Hao, X. Li, I. Okada and Y.
Zheng, Favorite sites for simple random walk in two and more dimensions, arXiv:2409.00995 (2024); P.
Erdős and S. J. Taylor, Some problems concerning the structure of random walk paths, Acta Math.
Acad. Sci. Hungar. 11 (1960), 137-162; A. Dembo, Y. Peres, J. Rosen and O. Zeitouni, Thick points
for planar Brownian motion and the Erdős-Taylor conjecture on random walk, Acta Math. 186 (2001),
239-270, Hao-Li-Okada-Zheng, Theorem 1.1: in d = 2, a.s. limsup_n |F(n)| = 3; Erdős-Taylor
(sharpened by Dembo-Peres-Rosen-Zeitouni to lim T_n / (log n)² = 1/π a.s.): the maximal local time
T_n is a.s. ≪ (log n)²; erdosproblems.com/1166 combines them into |⋃_{k ≤ n} F(k)| ≪ (log n)² a.s.,
https://arxiv.org/abs/2409.00995.
-/
public theorem_wanted favouriteSitesPolylogarithmic_holds : favouriteSitesPolylogarithmic

end MathlibExt.Probability.RandomWalkFavouriteSitesErdosProblem1166Wanted
