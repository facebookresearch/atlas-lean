/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 574
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Real

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem574Wanted

/-! Source record `EP-574` (Erdős Problem 574). -/

/-- **Graphs without cycles of lengths $2k-1$ and $2k$.** For a natural number $k$, a simple
graph $G$ is free of the cycle lengths $2k-1$ and $2k$ when it contains no copy of the cycle
graph $C_{2k-1}$ and no copy of the cycle graph $C_{2k}$, where a copy is an injective graph
homomorphism, that is, a subgraph that need not be induced.

Here $C_m$ is the cycle graph on $m$ vertices, which has no edges for $m \le 1$ and is a single
edge for $m = 2$, and $2k-1$ is computed in the natural numbers, so it is $0$ when $k = 0$. -/
def IsFreeOf574Cycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧
    (SimpleGraph.cycleGraph (2 * k)).Free G

/-- **Extremal number for cycles of lengths $2k-1$ and $2k$.** For natural numbers $k$ and
$n$, $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the supremum of the numbers of edges of the simple
graphs on the vertex set $\{0, \dots, n-1\}$ that contain no copy of the cycle graph $C_{2k-1}$
and no copy of the cycle graph $C_{2k}$, where the supremum of the empty set is $0$. Here $2k-1$
is computed in the natural numbers, so it is $0$ when $k = 0$. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  sSup { e : ℕ | ∃ G : SimpleGraph (Fin n), IsFreeOf574Cycles G k ∧ G.edgeSet.ncard = e }

/-- **Erdős Problem 574.** The statement that for every natural number $k \ge 2$ the ratio
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) / (n/2)^{1 + 1/k}$ tends to $1$ as $n \to \infty$, that is,
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) = (1 + o(1)) (n/2)^{1 + 1/k}$. Here
$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the extremal number: the supremum of the numbers of
edges of simple graphs on $n$ vertices that contain no copy of the cycle graph $C_{2k-1}$ and no
copy of the cycle graph $C_{2k}$. -/
noncomputable def conjecture : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    Filter.Tendsto
      (fun n : ℕ => (extremalNumber k n : ℝ) / (((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))))
      Filter.atTop (nhds 1)

/--
**Erdős Problem 574 is false.** It is not the case that for every natural number $k \ge 2$ the
ratio $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) / (n/2)^{1 + 1/k}$ tends to $1$ as $n \to \infty$.
Here $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the extremal number: the supremum of the numbers
of edges of simple graphs on $n$ vertices that contain no copy of the cycle graph $C_{2k-1}$ and
no copy of the cycle graph $C_{2k}$.

Lazebnik, Ustimenko and Woldar (Discrete Math. 1999), per Füredi–Simonovits
(arXiv:1306.5167, Construction 4.28), blow up one side of Benson's girth-12 bipartite graph to
get bipartite $C_{10}$-free graphs (hence also $C_9$-free) with
$4(n/5)^{6/5} > 0.5798\, n^{6/5}$ edges for infinitely many $n$, refuting the case $k = 5$.

Source: Zoltán Füredi and Miklós Simonovits, The history of degenerate
(bipartite) extremal graph problems, in Erdős Centennial, Bolyai Soc. Math. Stud. 25 (2013),
arXiv:1306.5167, https://arxiv.org/abs/1306.5167. Moved from
`OpenConjectures/Combinatorics/ErdosProblem574`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ErdosProblem574Wanted
