/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Forcing a 2-regular minor by average degree (OPG-59911)

Every graph of average degree at least `4t/3 - 2` contains every 2-regular
graph on `t` vertices as a minor.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GraphTheory.TwoRegularMinorForcingWanted

/-! Source record `OPG-59911`. -/

/-- **Minor via branch sets.** For finite simple graphs $G$ and $H$, $G$ has $H$ as a minor if
there is a family of vertex sets $B_w$ of $G$, one for each vertex $w$ of $H$, such that each
$B_w$ is nonempty and induces a connected subgraph of $G$, the sets $B_u$ and $B_v$ are disjoint
whenever $u \ne v$, and for every edge $uv$ of $H$ some vertex of $B_u$ is adjacent in $G$ to
some vertex of $B_v$. -/
def HasMinor {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
    (H : SimpleGraph W) : Prop :=
  ∃ branch : W → Finset V,
    (∀ w, (branch w).Nonempty) ∧
      (∀ w, (G.induce (branch w : Set V)).Connected) ∧
      (∀ u v, u ≠ v → Disjoint (branch u) (branch v)) ∧
      ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- **Average-degree conjecture for 2-regular minors.** For every natural number $t$, every
finite simple graph whose average degree is at least $4t/3 - 2$ (the average degree of the graph
with no vertices being taken as $0$) contains every 2-regular simple graph on $t$ vertices as a
minor. -/
def conjecture : Prop :=
  ∀ (t : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ((∑ v : V, (G.degree v : ℚ)) / (Fintype.card V : ℚ) ≥ 4 * (t : ℚ) / 3 - 2) →
    ∀ (H : SimpleGraph (Fin t)) [DecidableRel H.Adj], (∀ v, H.degree v = 2) → HasMinor G H

/--
**Csóka–Lo–Norin–Wu–Yepremyan theorem on 2-regular minors.** For every natural number $t$,
every finite simple graph $G$ whose average degree (the sum of the vertex degrees divided by the
number of vertices, taken to be $0$ when $G$ has no vertices) is at least $4t/3 - 2$ contains
every 2-regular simple graph $H$ on $t$ vertices as a minor: there are nonempty, pairwise
disjoint sets of vertices of $G$, one for each vertex of $H$, each inducing a connected subgraph
of $G$, such that whenever two vertices of $H$ are adjacent, some edge of $G$ joins their sets.

Csoka, Lo, Norin, Wu and Yepremyan proved this, verifying a conjecture of Reed and Wood; the
non-strict threshold follows from the form of their bound in Corollary 8 and Lemma 9.

Source: Endre Csoka, Irene Lo, Sergey Norin, Hehui Wu and Liana
Yepremyan, The extremal function for disconnected minors, Journal of Combinatorial Theory Series
B (2017), arXiv:1509.01185, https://arxiv.org/abs/1509.01185. Moved from
`OpenConjectures/GraphTheory/TwoRegularMinorForcing`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.TwoRegularMinorForcingWanted
