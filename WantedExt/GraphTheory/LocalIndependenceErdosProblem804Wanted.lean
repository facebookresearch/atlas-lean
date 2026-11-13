/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local versus global independence number (Erdős Problem 804)

Erdős Problem 804 (Erdős and Hajnal): let `f(m, n)` be maximal such that any graph on `n` vertices
in which every induced subgraph on `m` vertices has an independent set of size at least `log n`
contains an independent set of size at least `f(m, n)`. Is `f((log n)², n) ≥ n^{1/2 - o(1)}`? Is
`f((log n)³, n) ≫ (log n)³`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.LocalIndependenceErdosProblem804Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #804, https://www.erdosproblems.com/804 (status
DISPROVED). UnsolvedMath record UM-30007042 (`EP-804`), dataset ulamai/UnsolvedMath v1.8.0.

`f(m, n)` is the least independence number of a graph satisfying the local condition, so each
question is stated directly as a lower bound on the independence number of every such graph. The
parameters are rounded as `m = ⌊(log n)^j⌋` and `t = ⌈log n⌉` with the natural logarithm (Alon and
Sudakov: 'all logarithms are in the natural base e', floor and ceiling signs omitted). The
open-ended 'estimate `f`' is answered on the page by Alon and Sudakov's bounds and is not
formalized. Compared with the formal-conjectures statement `ErdosProblems/804.lean` (equivalent; no
code imported).
-/

/-- Every induced subgraph of `G` on `m` vertices has an independent set of size at least `t`. -/
def HasLocalIndependence {n : ℕ} (G : SimpleGraph (Fin n)) (m t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m → ∃ I ⊆ S, t ≤ I.card ∧ G.IsIndepSet (I : Set (Fin n))

/-- Erdős Problem 804, first question: `f((log n)², n) ≥ n^{1/2 - o(1)}`. -/
def localIndependenceSquareLog : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    HasLocalIndependence G ⌊Real.log n ^ 2⌋₊ ⌈Real.log n⌉₊ →
      ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧
        (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ I.card

/-- Erdős Problem 804, second question: `f((log n)³, n) ≫ (log n)³`. -/
def localIndependenceCubeLog : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    HasLocalIndependence G ⌊Real.log n ^ 3⌋₊ ⌈Real.log n⌉₊ →
      ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧ c * Real.log n ^ 3 ≤ I.card

/--
Resolved false: Alon and Sudakov proved `f((log n)², n) ≪ (log n)²`, far below `n^{1/2 - ε}`;
erdosproblems.com/804 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#804, https://www.erdosproblems.com/804 (status DISPROVED); resolution: N. Alon and B. Sudakov, On
graphs with subgraphs having large independence numbers, J. Graph Theory 56 (2007), 149-157, Section
1, (1) and (2): if every induced subgraph on log² n vertices has an independent set of size log n,
the guaranteed independence number f(n) satisfies Ω(log² n/log log n) ≤ f(n) ≤ O(log² n), and for
induced subgraphs on log³ n vertices it is q(n) = Θ(log² n/log log n) ('all logarithms are in the
natural base e', floor and ceiling signs omitted),
https://web.math.princeton.edu/~nalon/PDFS/erdoshajnal4.pdf.
-/
public theorem_wanted localIndependenceSquareLog_refuted : ¬ localIndependenceSquareLog

/--
Resolved false: Alon and Sudakov proved `f((log n)³, n) ≍ (log n)² / log log n`, which is `o((log
n)³)`; erdosproblems.com/804 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems,
Problem #804, https://www.erdosproblems.com/804 (status DISPROVED); resolution: N. Alon and B.
Sudakov, On graphs with subgraphs having large independence numbers, J. Graph Theory 56 (2007),
149-157, Section 1, (1) and (2): if every induced subgraph on log² n vertices has an independent set
of size log n, the guaranteed independence number f(n) satisfies Ω(log² n/log log n) ≤ f(n) ≤ O(log²
n), and for induced subgraphs on log³ n vertices it is q(n) = Θ(log² n/log log n) ('all logarithms
are in the natural base e', floor and ceiling signs omitted),
https://web.math.princeton.edu/~nalon/PDFS/erdoshajnal4.pdf.
-/
public theorem_wanted localIndependenceCubeLog_refuted : ¬ localIndependenceCubeLog

end MathlibExt.GraphTheory.LocalIndependenceErdosProblem804Wanted
