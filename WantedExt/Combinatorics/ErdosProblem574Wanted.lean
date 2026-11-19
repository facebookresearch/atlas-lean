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
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Real

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem574Wanted

/-! Source record `EP-574` (Erdős Problem 574). -/

/-- A simple graph is free of the two forbidden ordinary cycle lengths
`2 * k - 1` and `2 * k` [EP-574], expressed with Mathlib's ordinary
(non-induced) cycle-containment API: neither `SimpleGraph.cycleGraph
(2 * k - 1)` nor `SimpleGraph.cycleGraph (2 * k)` has a copy in `G`. -/
def IsFreeOf574Cycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧
    (SimpleGraph.cycleGraph (2 * k)).Free G

/-- Extremal number `ex(n; {C_{2k-1}, C_{2k}})` [EP-574]: supremum of edge
counts over `n`-vertex simple graphs free of both cycles. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  sSup { e : ℕ | ∃ G : SimpleGraph (Fin n), IsFreeOf574Cycles G k ∧ G.edgeSet.ncard = e }

/-- Erdős Problem 574 [EP-574]: for `k ≥ 2`, is
`ex(n; {C_{2k-1}, C_{2k}}) = (1 + o(1)) (n / 2)^{1 + 1 / k}` as `n → ∞`,
i.e. does the ratio tend to `1`. -/
noncomputable def conjecture : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    Filter.Tendsto
      (fun n : ℕ => (extremalNumber k n : ℝ) / (((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))))
      Filter.atTop (nhds 1)

/--
Resolved false: Lazebnik, Ustimenko and Woldar (Discrete Math. 1999), per Füredi–Simonovits
(arXiv:1306.5167, Construction 4.28), blow up one side of Benson's girth-12 bipartite graph to
get bipartite C10-free graphs with 4(n/5)^{6/5} > 0.5798 n^{6/5} edges for infinitely many n,
refuting the k=5 case. Source: Zoltán Füredi and Miklós Simonovits, The history of degenerate
(bipartite) extremal graph problems, in Erdős Centennial, Bolyai Soc. Math. Stud. 25 (2013),
arXiv:1306.5167, https://arxiv.org/abs/1306.5167. Moved from
`OpenConjectures/Combinatorics/ErdosProblem574`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.ErdosProblem574Wanted
