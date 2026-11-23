/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cyclic vertex sets in regular Dirac graphs (Erdős Problem 622)

Erdős Problem 622 (Erdős and Faudree): let `G` be a regular graph with `2n` vertices and degree `n +
1`. Must `G` have `≫ 2^{2n}` subsets that are spanned by a cycle?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MathlibExt.GraphTheory.RegularDiracCyclicSubsetsErdosProblem622Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #622, https://www.erdosproblems.com/622 (status
PROVED). UnsolvedMath record UM-30006956 (`EP-622`), dataset ulamai/UnsolvedMath v1.8.0.

A subset is spanned by a cycle when some cycle of `G` (`Walk.IsCycle`) has exactly that vertex set.
`≫ 2^{2n}` is `∃ c > 0` with at least `c 2^{2n}` such subsets for every `n ≥ 1` and every such `G`,
the form of the question in the resolving paper; regularity is `(G.neighborSet v).ncard = n + 1`
for all `v`. The case `n = 0` is excluded: the graph on no vertices is vacuously `1`-regular and has
no cycle, so it would falsify the statement (`n = 1` is vacuous, no graph on `2` vertices being
`2`-regular).
-/

open Classical in
/-- The number of vertex sets `S` of `G` that are cyclic: some cycle of `G` has vertex set exactly
`S`. -/
noncomputable def cyclicSubsetCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun S : Finset V =>
    ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.support.toFinset = S).card

/-- Erdős Problem 622 (Erdős and Faudree): there is `c > 0` such that for every `n ≥ 1` every
`(n+1)`-regular graph on `2n` vertices has at least `c 2^{2n}` cyclic vertex sets. -/
def regularDiracManyCyclicSubsets : Prop :=
  ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n → ∀ G : SimpleGraph (Fin (2 * n)),
    (∀ v, (G.neighborSet v).ncard = n + 1) → c * 2 ^ (2 * n) ≤ cyclicSubsetCount G

/--
Resolved true: Draganić, Keevash and Müyesser answered the question of Erdős and Faudree (is there
`c > 0` such that every `(n+1)`-regular graph on `2n` vertices has at least `c 2^{2n}` cyclic vertex
sets?) in the affirmative: for large `n` a minimiser is `K_{n-1,n+1}` plus a `2`-factor in the part
of size `n + 1`, so the optimal `c` is `1/2`, that is, at least `(1/2 + o(1)) 2^{2n}` vertex sets
are spanned by a cycle; erdosproblems.com/622 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #622, https://www.erdosproblems.com/622 (status PROVED); resolution: N.
Draganić, P. Keevash and A. Müyesser, Cyclic subsets in regular Dirac graphs, arXiv:2503.01826
(2025), abstract: for n sufficiently large a minimiser is K_{n-1,n+1} plus a 2-factor in the part of
size n+1, so the optimal c is 1/2; erdosproblems.com/622: at least (1/2 + o(1)) 2^{2n} subsets
spanned by a cycle, https://arxiv.org/abs/2503.01826.
-/
public theorem_wanted regularDiracManyCyclicSubsets_holds : regularDiracManyCyclicSubsets

end MathlibExt.GraphTheory.RegularDiracCyclicSubsetsErdosProblem622Wanted
