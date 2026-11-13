/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear cover time is exponentially unlikely (Benjamini's conjecture)

I. Benjamini, Random Planar Metrics, Section 4.1: for every `C < ∞` there is `c = c(C) < 1` such
that, for every simple `n`-vertex graph `G`, the probability that simple random walk covers all of
`G` within `Cn` steps is smaller than `cⁿ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace MathlibExt.Probability.LinearCoverTimeExponentiallyUnlikelyAMR99Problem0083Wanted

/-!
Source: I. Benjamini, Random Planar Metrics, Section 4.1 (cover-time conjecture). UnsolvedMath
record UM-10000083 (`AMR-099-0083`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are simple graphs on `Fin n`. The probability of covering within `m` steps from `v` is the
sum over vertex sequences `w 0 = v, …, w m` with consecutive entries adjacent and every vertex
visited of `∏_{i < m} 1 / deg(w i)` (simple random walk; a walk at an isolated vertex cannot move,
so such sequences do not occur), with `m = ⌊C n⌋`. Starting from a fixed vertex covers "any rule for
`X₀`" in Dubroff–Kahn by averaging; the bound `≤ cⁿ` and the source's `< cⁿ` are equivalent up to
enlarging `c`. The bound is required only for `n ≥ n₀`: for `n = 1`, or `G = K₂` with `C ≥ 1/2`, the
walk covers `G` with probability `1 > cⁿ`, so the source's all-`n` wording is false and the
statement is asymptotic, as in Dubroff–Kahn, who "always assume `n` is large enough" (§1, usage
notes).
-/

open Classical in
/-- The probability that simple random walk on `G` started at `v` visits every vertex within `m`
steps: the sum, over vertex sequences `w 0 = v, w 1, …, w m` with consecutive vertices adjacent that
visit every vertex, of `∏_{i < m} 1 / deg(w i)`. -/
noncomputable def coverProb {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (m : ℕ) : ℝ :=
  ∑ w : Fin (m + 1) → Fin n with
      w 0 = v ∧ (∀ i : Fin m, G.Adj (w i.castSucc) (w i.succ)) ∧ Function.Surjective w,
    ∏ i : Fin m, ((Finset.univ.filter (G.Adj (w i.castSucc))).card : ℝ)⁻¹

/-- Benjamini's cover-time conjecture (Random Planar Metrics, §4.1): for every `C > 0` there is
`c < 1` such that, for every large `n`, every simple graph `G` on `n` vertices and every start
vertex, simple random walk covers `G` within `⌊C n⌋` steps with probability at most `cⁿ`. -/
def linearCoverTimeExponentiallyUnlikely : Prop :=
  ∀ C : ℝ, 0 < C → ∃ c : ℝ, c < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (G : SimpleGraph (Fin n)) (v : Fin n),
    coverProb G v ⌊C * n⌋₊ ≤ c ^ n

/--
Resolved true: Dubroff and Kahn proved Benjamini's conjecture: for every `C` there is `ε > 0` with
`Pr({X₀, …, X_{Cn}} = V) < e^{-εn}` for simple random walk on any simple `n`-vertex graph; here `c =
e^{-ε}`, and the bound is asserted for all large `n`. Source: I. Benjamini, Random Planar Metrics,
Section 4.1 (cover-time conjecture); resolution: Q. Dubroff and J. Kahn, Linear cover time is
exponentially unlikely, Ann. Probab. 53 (2025), doi:10.1214/24-AOP1699, arXiv:2109.01237, Theorem
1.1: for any C there is ε > 0 such that for any simple graph G on V of size n and an ordinary random
walk X₀, X₁, … on G (with any rule for X₀), Pr({X₀, …, X_{Cn}} = V) < e^{-εn}; abstract: "Proving a
2009 conjecture of Itai Benjamini", https://arxiv.org/abs/2109.01237.
-/
public theorem_wanted linearCoverTimeExponentiallyUnlikely_holds :
    linearCoverTimeExponentiallyUnlikely

end MathlibExt.Probability.LinearCoverTimeExponentiallyUnlikelyAMR99Problem0083Wanted
