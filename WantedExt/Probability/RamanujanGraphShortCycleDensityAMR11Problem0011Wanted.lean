/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Short cycles seen by random walk on infinite Ramanujan graphs (Abért, Question 11)

M. Abért, Some questions (2010), Question 11: let `G` be an infinite `d`-regular Ramanujan graph
(the Markov operator has the same spectral radius as on the `d`-regular tree). Is it true that for
every `C` the probability that a random walk on `G` ends touching a `C`-cycle tends to zero?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MathlibExt.Probability.RamanujanGraphShortCycleDensityAMR11Problem0011Wanted

/-!
Source: M. Abért, Some questions (2010), Question 11, https://www.renyi.hu/~abert/questions.pdf.
UnsolvedMath record UM-01200011 (`AMR-011-0011`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a connected, infinite, `d`-regular simple graph. Simple random walk from `o` is at `y` at
time `n` with probability `(number of walks of length n from o to y) / dⁿ`, and the spectral radius
is `limsup_n p_n(o, o)^{1/n}` (Lyons–Peres); Ramanujan means it equals `2 √(d - 1) / d`. A vertex
lies on a nontrivial cycle of length at most `L` when some closed walk at it of length in `[1, L]`
never immediately backtracks; this is Lyons–Peres' notion (a closed walk through `x` that is not
erased by iterated backtrack removal can be rotated to start at `x` and then reduced).
-/

/-- The number of walks of length `n` from `o` to `y` in `G`. -/
noncomputable def walkCount {V : Type*} (G : SimpleGraph V) (o y : V) (n : ℕ) : ℕ :=
  Nat.card {w : G.Walk o y // w.length = n}

/-- `x` lies on a nontrivial cycle of length at most `L`: some closed walk at `x` of positive length
at most `L` never immediately backtracks (iterated removal of backtracks leaves an edge). -/
def OnShortNontrivialCycle {V : Type*} (G : SimpleGraph V) (L : ℕ) (x : V) : Prop :=
  ∃ w : G.Walk x x, 0 < w.length ∧ w.length ≤ L ∧
    ∀ i : ℕ, 0 < i → i < w.length → w.getVert (i - 1) ≠ w.getVert (i + 1)

/-- `G` is Ramanujan of degree `d`: the spectral radius `limsup_n p_n(o, o)^{1/n}` of simple random
walk, with `p_n(o, o) = (number of closed walks of length n at o) / dⁿ`, equals `2 √(d - 1) / d`,
the spectral radius of the `d`-regular tree. -/
def IsRamanujan {V : Type*} (G : SimpleGraph V) (d : ℕ) (o : V) : Prop :=
  Filter.limsup (fun n : ℕ => ((walkCount G o o n : ℝ) / (d : ℝ) ^ n) ^ ((1 : ℝ) / n))
      Filter.atTop = 2 * Real.sqrt ((d : ℝ) - 1) / d

/-- Abért's Question 11, answered: on an infinite connected `d`-regular Ramanujan graph, for every
`L ≥ 1` the probability that simple random walk from `o` is at time `n` on a nontrivial cycle of
length at most `L` tends to `0`. -/
def ramanujanShortCycleProbabilityTendsToZero : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (d : ℕ), Infinite V → G.Connected →
    (∀ v : V, (G.neighborSet v).Finite ∧ (G.neighborSet v).ncard = d) →
    ∀ o : V, IsRamanujan G d o → ∀ L : ℕ, 1 ≤ L →
      Filter.Tendsto
        (fun n : ℕ => (Nat.card {p : (y : V) × G.Walk o y //
            p.2.length = n ∧ OnShortNontrivialCycle G L p.1} : ℝ) / (d : ℝ) ^ n)
        Filter.atTop (nhds 0)

/--
Resolved true: Lyons and Peres proved that on every infinite Ramanujan graph, for each `L ≥ 1`, the
probability that simple random walk at time `n` lies on a nontrivial cycle of length at most `L`
tends to `0`, without unimodularity or transitivity assumptions. Source: M. Abért, Some questions
(2010), Question 11, https://www.renyi.hu/~abert/questions.pdf; resolution: R. Lyons and Y. Peres,
Cycle density in infinite Ramanujan graphs, Ann. Probab. 43 (2015), 3337-3358, arXiv:1310.0489,
Theorem 1.2: for an infinite Ramanujan graph G and L ≥ 1, lim_{n→∞} q_n = 0, where q_n is the
probability that simple random walk at time n lies on a nontrivial cycle of length at most L,
https://arxiv.org/abs/1310.0489.
-/
public theorem_wanted ramanujanShortCycleProbabilityTendsToZero_holds :
    ramanujanShortCycleProbabilityTendsToZero

end MathlibExt.Probability.RamanujanGraphShortCycleDensityAMR11Problem0011Wanted
