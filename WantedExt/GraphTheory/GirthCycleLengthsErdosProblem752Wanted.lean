/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cycle lengths in graphs of large girth (Erdős Problem 752)

Erdős Problem 752 (Erdős, Faudree and Schelp): let `G` be a graph with minimum degree `k` and girth
`> 2s` (i.e. `G` contains no cycles of length `≤ 2s`). Must there be `≫ k^s` many distinct cycle
lengths in `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MathlibExt.GraphTheory.GirthCycleLengthsErdosProblem752Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #752, https://www.erdosproblems.com/752 (status
PROVED). UnsolvedMath record UM-30007012 (`EP-752`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite with a nonempty vertex set; the implied constant may depend on the fixed `s`.
Minimum degree `k ≥ 2` (for `k ≤ 1` a forest is allowed and has no cycles). Cycle lengths are
lengths of closed walks with `Walk.IsCycle`, a finite set.
-/

/-- Erdős Problem 752 (Erdős, Faudree and Schelp): for every `s` there is `c > 0` such that every
finite nonempty graph with minimum degree `k ≥ 2` and girth greater than `2s` (no cycle of length at
most `2s`) has at least `c k^s` distinct cycle lengths. -/
def largeGirthManyCycleLengths : Prop :=
  ∀ s : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (k : ℕ),
    2 ≤ k → (∀ v, k ≤ (G.neighborSet v).ncard) →
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → 2 * s < p.length) →
        c * (k : ℝ) ^ s ≤ {ℓ : ℕ | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = ℓ}.ncard

/--
Resolved true: Sudakov and Verstraëte proved that a graph of average degree `d` and girth `g` has
`Ω(d^{⌊(g - 1)/2⌋})` consecutive even cycle lengths; girth `> 2s` gives `⌊(g - 1)/2⌋ ≥ s`, and
minimum degree `k` gives average degree at least `k`. erdosproblems.com/752 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #752, https://www.erdosproblems.com/752 (status
PROVED); resolution: B. Sudakov and J. Verstraëte, Cycle lengths in sparse graphs, Combinatorica 28
(2008), 357-372, Theorem 1.1 of arXiv:0707.2117: a graph of average degree d and girth g contains
Ω(d^{⌊(g-1)/2⌋}) consecutive even cycle lengths; erdosproblems.com/752: proved by Sudakov and
Verstraëte (Erdős, Faudree and Schelp had the case s = 2), https://arxiv.org/abs/0707.2117.
-/
public theorem_wanted largeGirthManyCycleLengths_holds : largeGirthManyCycleLengths

end MathlibExt.GraphTheory.GirthCycleLengthsErdosProblem752Wanted
