/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Scaling `(a, b)`-choosability (Erdős Problem 632)

Erdős Problem 632 (Erdős, Rubin and Taylor): a graph is `(a, b)`-choosable if for any assignment of
a list of `a` colours to each of its vertices there is a subset of `b` colours from each list such
that the subsets of adjacent vertices are disjoint. If `G` is `(a, b)`-choosable, is `G` `(am,
bm)`-choosable for every integer `m ≥ 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.ChoosabilityScalingErdosProblem632Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #632, https://www.erdosproblems.com/632 (status
DISPROVED). UnsolvedMath record UM-30006960 (`EP-632`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite; colours are natural numbers (finitely many lists use finitely many colours, so
the palette loses nothing); `a, b, m` are positive integers, as in the resolving paper.
-/

/-- `G` is `(a, b)`-choosable: for every assignment of a list of `a` colours (natural numbers) to
each vertex, one can choose `b` colours from each list so that adjacent vertices receive disjoint
sets of colours. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = a) →
    ∃ S : V → Finset ℕ, (∀ v, S v ⊆ L v ∧ (S v).card = b) ∧
      ∀ u v, G.Adj u v → Disjoint (S u) (S v)

/-- Erdős Problem 632 (Erdős, Rubin and Taylor): for all positive integers `a, b, m`, every finite
`(a, b)`-choosable graph is `(am, bm)`-choosable. -/
def choosabilityScales : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (a b m : ℕ), 1 ≤ a → 1 ≤ b → 1 ≤ m →
    IsChoosable G a b → IsChoosable G (a * m) (b * m)

/--
Resolved false: Dvořák, Hu and Sereni exhibited a `4`-choosable (that is, `(4, 1)`-choosable) graph
that is not `(8, 2)`-choosable; erdosproblems.com/632 lists the problem as disproved. Source: T. F.
Bloom, Erdős Problems, Problem #632, https://www.erdosproblems.com/632 (status DISPROVED);
resolution: Z. Dvořák, X. Hu and J.-S. Sereni, A 4-choosable graph that is not (8:2)-choosable, Adv.
Comb. (2019), Paper No. 5, abstract: a negative answer to the question of Erdős, Rubin and Taylor
whether every (a:b)-choosable graph is (am:bm)-choosable, by a 4-choosable graph that is not
(8:2)-choosable, https://arxiv.org/abs/1806.03880.
-/
public theorem_wanted choosabilityScales_refuted : ¬ choosabilityScales

end MathlibExt.GraphTheory.ChoosabilityScalingErdosProblem632Wanted
