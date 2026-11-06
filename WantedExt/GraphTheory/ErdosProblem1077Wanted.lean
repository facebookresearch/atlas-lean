/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdös Problem 1077
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Balanced

@[expose] public section

open Filter

namespace MathlibExt.GraphTheory.ErdosProblem1077Wanted

/-! Source record `FC-ErdosProblem1077`, ported from FormalConjectures
`ErdosProblems/1077.lean` (`theorem erdos_1077`) and checked against
erdosproblems.com/1077. The historical positive Erdős–Simonovits
proposition is preserved as `mainPositive` (disproved); its negation is the
unregistered companion `disprovedMain`. `SimpleGraph.IsBalanced` is
MathlibExt's. Status: resolved false (formalized in Lean). -/

open Classical in
/-- **Erdős–Simonovits balanced subgraph claim.** For all reals $\varepsilon$ and $\alpha$ with
$0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all sufficiently large real $D$ and then all
sufficiently large $n$, every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ with more
than $n^{1+\alpha}$ edges has a (not necessarily induced) subgraph $H$ with some number $m$ of
vertices such that $H$ is $D$-balanced (its maximum degree is at most $D$ times its minimum
degree), $m > n^{1-\alpha}$, and $H$ has more than $\varepsilon m^{1+\alpha}$ edges.

This claim (Erdős Problem 1077) is false. -/
def mainPositive : Prop :=
  ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 → ∀ᶠ D in atTop, ∀ᶠ n in atTop,
    ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
      ∃ (H : SimpleGraph.Subgraph G),
        letI m := H.verts.ncard
        SimpleGraph.IsBalanced H.coe D ∧
        m > (n : ℝ) ^ (1 - α) ∧
        H.edgeSet.ncard > ε * m ^ (1 + α)

/-- **Negation of the Erdős–Simonovits balanced subgraph claim.** The proposition that the
Erdős–Simonovits balanced subgraph claim fails, that is, that it is not the case that for all
reals $\varepsilon$ and $\alpha$ with $0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all
sufficiently large real $D$ and then all sufficiently large $n$, every simple graph $G$ on the
vertex set $\{0, \dots, n-1\}$ with more than $n^{1+\alpha}$ edges has a (not necessarily
induced) subgraph $H$ with some number $m$ of vertices such that $H$ is $D$-balanced (its maximum
degree is at most $D$ times its minimum degree), $m > n^{1-\alpha}$, and $H$ has more than
$\varepsilon m^{1+\alpha}$ edges. -/
def disprovedMain : Prop := ¬ mainPositive

/--
**The Erdős–Simonovits balanced subgraph claim is false.** It is not the case that for all reals
$\varepsilon$ and $\alpha$ with $0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all sufficiently
large real $D$ and then all sufficiently large $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^{1+\alpha}$ edges has a (not necessarily induced) subgraph
$H$ with some number $m$ of vertices such that $H$ is $D$-balanced (its maximum degree is at most
$D$ times its minimum degree), $m > n^{1-\alpha}$, and $H$ has more than $\varepsilon m^{1+\alpha}$
edges.

The disproof uses a bipartite witness: the requirement $m > n^{1-\alpha}$ is too strong, and the
correct order is $n^{\alpha}$ per Jun Gao and Jiang–Longbrake [JiLo25], per erdosproblems.com/1077.

Source:
External Lean disproof of Erdos Problem 1077, plby/lean-proofs at commit
dfe2d78128b493c572cf525b1b8edf4897fb7664,
https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos1077.lean#L265.
Moved from `OpenConjectures/GraphTheory/ErdosProblem1077`.
-/
public theorem_wanted mainPositive_refuted : ¬ mainPositive

end MathlibExt.GraphTheory.ErdosProblem1077Wanted
