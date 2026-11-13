/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thresholds for spanning combs and bounded-degree trees (Oberwolfach Reports 1/2014)

Oberwolfach workshop Combinatorics (2014), E. Lubetzky (with J. Kahn and N. Wormald): is the
threshold for a spanning comb `Comb_n` in `G(n, p)` of order `log n / n`? More generally, is this
the threshold for every `n`-vertex tree of bounded degree?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.SpanningTreeThresholdOWR12861Problem009Wanted

/-!
Source: E. Lubetzky (with J. Kahn and N. Wormald), in Combinatorics, Oberwolfach Reports 11 (2014),
no. 1, pp. 42-43, DOI 10.4171/OWR/2014/01. UnsolvedMath record UM-30002461 (`OWR-12861-009`),
dataset ulamai/UnsolvedMath v1.8.0.

`G(n, p)` is Mathlib's binomial random graph `SimpleGraph.binomialRandom (Fin n) p`; the edge
probability `c log n / n` is clamped to `[0, 1]`. `Comb_n` is the source's comb of order `k = √n` on
`n = k²` vertices: a `k`-vertex path with disjoint `k`-vertex paths beginning at its vertices.
Containment is as a (not necessarily induced) subgraph. Part (b) states the upper bound for all
trees of maximum degree at most `Δ` simultaneously, as Montgomery proves; the lower bound in both
parts is the connectivity bound noted in the source.
-/

open Filter Topology unitInterval

/-- The edge probability `c log n / n`, clamped to `[0, 1]` (only large `n` matter). -/
noncomputable def logEdgeProb (c : ℝ) (n : ℕ) : I :=
  Set.projIcc 0 1 zero_le_one (c * Real.log n / n)

/-- The comb `Comb_n` on `n = k²` vertices `(i, j)`, `i, j < k`: the spine is the path
`(0, 0), (1, 0), …, (k - 1, 0)` and the tooth at `i` is the path `(i, 0), (i, 1), …, (i, k - 1)`,
so `k` disjoint `k`-vertex paths hang from the `k` vertices of the spine. -/
def comb (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  SimpleGraph.fromRel fun a b =>
    (a.2.val = 0 ∧ b.2.val = 0 ∧ a.1.val + 1 = b.1.val) ∨ (a.1 = b.1 ∧ a.2.val + 1 = b.2.val)

/-- Part (a), the Comb Conjecture: the threshold for `G(n, p)`, `n = k²`, to contain a spanning
comb has order `log n / n`: for some `0 < c ≤ C` the probability tends to `0` at
`p = c log n / n` and to `1` at `p = C log n / n`. -/
def combThresholdLogOverN : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    Tendsto (fun k : ℕ => (SimpleGraph.binomialRandom (Fin (k * k)) (logEdgeProb c (k * k))).real
      {G | (comb k).IsContained G}) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => (SimpleGraph.binomialRandom (Fin (k * k)) (logEdgeProb C (k * k))).real
      {G | (comb k).IsContained G}) atTop (𝓝 1)

open Classical in
/-- Part (b), Kahn's conjecture: for every `Δ`, the threshold for `G(n, p)` to contain the
`n`-vertex trees of maximum degree at most `Δ` has order `log n / n`: for some `c > 0`, a.a.s.
`G(n, c log n / n)` contains no such tree, and for some `C`, a.a.s. `G(n, C log n / n)` contains
every such tree. -/
def boundedDegreeTreeThreshold : Prop :=
  ∀ Δ : ℕ, ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    Tendsto (fun n : ℕ => (SimpleGraph.binomialRandom (Fin n) (logEdgeProb c n)).real
      {G | ∃ T : SimpleGraph (Fin n), T.IsTree ∧ (∀ v, T.degree v ≤ Δ) ∧ T.IsContained G})
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (SimpleGraph.binomialRandom (Fin n) (logEdgeProb C n)).real
      {G | ∀ T : SimpleGraph (Fin n), T.IsTree → (∀ v, T.degree v ≤ Δ) → T.IsContained G})
      atTop (𝓝 1)

/--
Resolved true: Kahn, Lubetzky and Wormald proved that `G(n, (2 + ε) log n / n)` contains `Comb_n`
with high probability (Theorem 3 in the source), and below `log n / n` the random graph is
disconnected with high probability, so it contains no spanning tree. Source: E. Lubetzky (with J.
Kahn and N. Wormald), in Combinatorics, Oberwolfach Reports 11 (2014), no. 1, pp. 42-43, DOI
10.4171/OWR/2014/01; resolution: J. Kahn, E. Lubetzky and N. Wormald, Cycle factors and renewal
theory, Comm. Pure Appl. Math. 70 (2017), arXiv:1401.2707, abstract ('we confirm the Comb
Conjecture'), stated in the source as Theorem 3: G(n, (2 + ε) log n / n) contains Comb_n w.h.p., so
its threshold is at p ≍ log n / n (lower bound by connectivity), https://arxiv.org/abs/1401.2707.
-/
public theorem_wanted combThresholdLogOverN_holds : combThresholdLogOverN

/--
Resolved true: Montgomery proved that for every `Δ` there is `C(Δ)` such that `G(n, C log n / n)`
almost surely contains a copy of every `n`-vertex tree of maximum degree at most `Δ`, confirming
Kahn's conjecture; below `log n / n` the random graph is disconnected with high probability. Source:
E. Lubetzky (with J. Kahn and N. Wormald), in Combinatorics, Oberwolfach Reports 11 (2014), no. 1,
pp. 42-43, DOI 10.4171/OWR/2014/01; resolution: R. Montgomery, Spanning trees in random graphs, Adv.
Math. 356 (2019), 106793, arXiv:1810.03299, abstract: for each Δ > 0 there is C = C(Δ) such that
G(n, C log n / n) almost surely contains a copy of every tree with n vertices and maximum degree at
most Δ, confirming a conjecture of Kahn, https://arxiv.org/abs/1810.03299.
-/
public theorem_wanted boundedDegreeTreeThreshold_holds : boundedDegreeTreeThreshold

end MathlibExt.GraphTheory.SpanningTreeThresholdOWR12861Problem009Wanted
