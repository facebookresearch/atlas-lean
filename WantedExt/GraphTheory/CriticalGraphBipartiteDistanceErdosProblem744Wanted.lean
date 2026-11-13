/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Making critical graphs bipartite (Erdős Problem 744)

Erdős Problem 744 (Erdős, Hajnal and Szemerédi): let `k` be a large fixed constant. Let `f_k(n)` be
the minimal `m` such that there exists a graph `G` on `n` vertices with chromatic number `k`, such
that every proper subgraph has chromatic number `< k`, and `G` can be made bipartite by deleting `m`
edges. Is it true that `f_k(n) → ∞` as `n → ∞`? In particular, is it true that `f_4(n) ≫ log n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.CriticalGraphBipartiteDistanceErdosProblem744Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #744, https://www.erdosproblems.com/744 (status
DISPROVED). UnsolvedMath record UM-30007006 (`EP-744`), dataset ulamai/UnsolvedMath v1.8.0.

`k`-critical: chromatic number `k` and every proper subgraph (`G.Subgraph` other than `⊤`) has
smaller chromatic number. "Deleting `m` edges makes `G` bipartite" is: some `2`-colouring has at
most `m` monochromatic edges (ordered pairs counted twice). Bounds on `f_k(n)` are stated over all
`k`-critical graphs on `n` vertices, so `n` without such graphs impose nothing. The main question is
read for every large `k` (`∃ K, ∀ k ≥ K`). A third target states the exact value found by Rödl and
Tuza.
-/

/-- `G` is `k`-critical: it has chromatic number `k` and every proper subgraph has chromatic
number less than `k`. (MathlibExt's `SimpleGraph.IsCritical` is the weaker vertex-critical notion,
deleting any vertex lowers the chromatic number, so it is not used here.) -/
def IsCritical {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ H : G.Subgraph, H ≠ ⊤ → H.coe.chromaticNumber < k

open Classical in
/-- The number of ordered pairs of adjacent vertices of `G` with the same colour under the
`2`-colouring `c`, i.e. twice the number of monochromatic edges; `G` can be made bipartite by
deleting `m` edges iff some `c` makes this at most `2 m`. -/
noncomputable def monochromaticPairs {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) : ℕ :=
  (Finset.univ.offDiag.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ c p.1 = c p.2).card

/-- Erdős Problem 744, main question: for every large fixed `k`, `f_k(n) → ∞`, where `f_k(n)` is
the least number of edges whose deletion makes some `k`-critical graph on `n` vertices bipartite;
i.e. for every `M`, for all large `n`, every `k`-critical graph on `n` vertices needs at least `M`
deletions. -/
def criticalBipartiteDistanceTendsToInfinity : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ M : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    IsCritical G k → ∀ c : Fin n → Bool, 2 * M ≤ monochromaticPairs G c

/-- Erdős Problem 744, "in particular": `f_4(n) ≫ log n`. -/
def fourCriticalBipartiteDistanceLogLower : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n), IsCritical G 4 →
    ∀ c : Fin n → Bool, C * Real.log n ≤ (monochromaticPairs G c : ℝ) / 2

/-- Rödl and Tuza: for every `k ≥ 4` and all sufficiently large `n`, `f_k(n) = C(k - 1, 2)`: some
`k`-critical graph on `n` vertices becomes bipartite after deleting `C(k - 1, 2)` edges, and none
after deleting fewer. -/
def criticalBipartiteDistanceEventuallyBinomial : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in Filter.atTop,
    (∃ G : SimpleGraph (Fin n), IsCritical G k ∧
      ∃ c : Fin n → Bool, monochromaticPairs G c ≤ 2 * (k - 1).choose 2) ∧
    ∀ G : SimpleGraph (Fin n), IsCritical G k → ∀ c : Fin n → Bool,
      2 * (k - 1).choose 2 ≤ monochromaticPairs G c

/--
Resolved false: Rödl and Tuza proved that `f_k(n) = C(k - 1, 2)` for every `k ≥ 4` and all
sufficiently large `n`, so `f_k(n)` is eventually constant; erdosproblems.com/744 lists the problem
as disproved. Source: T. F. Bloom, Erdős Problems, Problem #744, https://www.erdosproblems.com/744
(status DISPROVED); resolution: V. Rödl and Z. Tuza, On color critical graphs, J. Combin. Theory
Ser. B 38 (1985), 204-213, erdosproblems.com/744: Rödl and Tuza proved f_k(n) = C(k-1, 2) for all
sufficiently large n; A. V. Kostochka and B. M. Reiniger, European J. Combin. 46 (2015), 89-94,
Section 1: Rödl and Tuza showed that for all sufficiently large n there are n-vertex (k +
1)-critical graphs that are bipartite plus C(k, 2) edges, and that this is best possible: for n
large enough no n-vertex (k + 1)-critical graph is bipartite plus fewer than C(k, 2) edges,
https://doi.org/10.1016/j.ejc.2014.12.002.
-/
public theorem_wanted criticalBipartiteDistanceTendsToInfinity_refuted :
    ¬ criticalBipartiteDistanceTendsToInfinity

/--
Resolved false: by Rödl and Tuza, `f_4(n) = C(3, 2) = 3` for all large `n`, so `f_4(n) ≫ log n`
fails. Source: T. F. Bloom, Erdős Problems, Problem #744, https://www.erdosproblems.com/744 (status
DISPROVED); resolution: V. Rödl and Z. Tuza, On color critical graphs, J. Combin. Theory Ser. B 38
(1985), 204-213, erdosproblems.com/744: Rödl and Tuza proved f_k(n) = C(k-1, 2) for all sufficiently
large n; A. V. Kostochka and B. M. Reiniger, European J. Combin. 46 (2015), 89-94, Section 1: Rödl
and Tuza showed that for all sufficiently large n there are n-vertex (k + 1)-critical graphs that
are bipartite plus C(k, 2) edges, and that this is best possible: for n large enough no n-vertex (k
+ 1)-critical graph is bipartite plus fewer than C(k, 2) edges,
https://doi.org/10.1016/j.ejc.2014.12.002.
-/
public theorem_wanted fourCriticalBipartiteDistanceLogLower_refuted :
    ¬ fourCriticalBipartiteDistanceLogLower

/--
Resolved true: Rödl and Tuza proved that for `k ≥ 4` and all sufficiently large `n` there are
`k`-critical graphs on `n` vertices that become bipartite after deleting `C(k - 1, 2)` edges, and
that no `k`-critical graph on `n` vertices becomes bipartite after deleting fewer (as quoted by
Kostochka and Reiniger with `k + 1` for `k`). Source: T. F. Bloom, Erdős Problems, Problem #744,
https://www.erdosproblems.com/744 (status DISPROVED); resolution: V. Rödl and Z. Tuza, On color
critical graphs, J. Combin. Theory Ser. B 38 (1985), 204-213, erdosproblems.com/744: Rödl and Tuza
proved f_k(n) = C(k-1, 2) for all sufficiently large n; A. V. Kostochka and B. M. Reiniger, European
J. Combin. 46 (2015), 89-94, Section 1: Rödl and Tuza showed that for all sufficiently large n there
are n-vertex (k + 1)-critical graphs that are bipartite plus C(k, 2) edges, and that this is best
possible: for n large enough no n-vertex (k + 1)-critical graph is bipartite plus fewer than C(k, 2)
edges, https://doi.org/10.1016/j.ejc.2014.12.002.
-/
public theorem_wanted criticalBipartiteDistanceEventuallyBinomial_holds :
    criticalBipartiteDistanceEventuallyBinomial

end MathlibExt.GraphTheory.CriticalGraphBipartiteDistanceErdosProblem744Wanted
