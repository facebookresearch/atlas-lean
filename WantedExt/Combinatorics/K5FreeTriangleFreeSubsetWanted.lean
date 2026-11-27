/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-533: Large triangle-free sets in dense K5-free graphs. Dense
K5-free graphs contain linear triangle-free sets.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open Filter SimpleGraph

namespace MathlibExt.Combinatorics.K5FreeTriangleFreeSubsetWanted

/-! Source record `EP-533`. -/

open scoped Classical in
/-- **EP-533: linear triangle-free sets in dense $K_5$-free graphs.** The conjecture states that
for every real $\delta > 0$ there is a real $c > 0$ such that, for all sufficiently large $n$,
every $K_5$-free simple graph on $n$ vertices with at least $\delta n^2$ edges has a
triangle-free set of at least $c n$ vertices (a set of vertices no three of which are pairwise
adjacent). -/
def conjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
      δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
        ∃ S : Finset (Fin n), c * (n : ℝ) ≤ (S.card : ℝ) ∧
          G.CliqueFreeOn (S : Set (Fin n)) 3

/--
**EP-533 is false: dense $K_5$-free graphs without linear triangle-free sets.** There is a real
$\delta > 0$ such that for every real $c > 0$ there are infinitely many $n$ for which some
$K_5$-free simple graph on $n$ vertices has at least $\delta n^2$ edges and yet has no
triangle-free set of at least $c n$ vertices (a set of vertices no three of which are pairwise
adjacent). In other words, the EP-533 conjecture fails.

Balogh and Lenz (2011) first gave $K_5$-free graphs of positive density with no linear
triangle-free set; Liu, Reiher, Sharifzadeh and Staden (Theorem 1.1 with $p = 3$, $\ell = 1$)
give $K_5$-free graphs on $2n$ vertices with $(1/3 - o(1))n^2$ edges whose largest
triangle-free set has $o(n)$ vertices, refuting $\delta = 1/24$.

Source: Hong Liu, Christian Reiher, Maryam Sharifzadeh and
Katherine Staden, Geometric constructions for Ramsey–Turán theory, J. Eur. Math. Soc. 28 (2026),
arXiv:2103.10423, https://arxiv.org/abs/2103.10423. Moved from
`OpenConjectures/Combinatorics/K5FreeTriangleFreeSubset`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.K5FreeTriangleFreeSubsetWanted
