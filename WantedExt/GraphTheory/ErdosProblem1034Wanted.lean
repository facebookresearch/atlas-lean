/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
# Erdős Problem 1034
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open Filter

namespace MathlibExt.GraphTheory.ErdosProblem1034Wanted

/-! Source record `FC-ErdosProblem1034`, ported from FormalConjectures
`ErdosProblems/1034.lean` (`def JoinedToTwo`, `theorem erdos_1034`,
`lower_bound`, `upper_bound`, `k4_free`) and checked against
erdosproblems.com/1034. A conjecture of Erdős and Faudree (stronger than
[905]). Status: resolved false (Ma–Tang; formalized in Lean). The
historical positive claim is preserved as `conjecture` (disproved); its
negation is the unregistered companion `disprovedForm`. The book lower
bound and the Ma–Tang and K₄-free upper bounds are unregistered
established companions. -/

/-- **Vertices joined to two vertices of a set.** Let $G$ be a simple graph on a vertex type $V$
and let $T$ and $Y$ be finite sets of vertices. The set $Y$ is joined to two vertices of $T$ in
$G$ if every vertex $y \in Y$ is adjacent in $G$ to two distinct vertices $u, v \in T$. -/
def JoinedToTwo {V : Type*} (G : SimpleGraph V) (T Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ G.Adj y u ∧ G.Adj y v

/-- **Erdős–Faudree triangle conjecture.** For every real $\varepsilon > 0$ the following holds
for all sufficiently large $n$: every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ with
more than $n^2/4$ edges contains a triangle $T$ and a set $Y$ of vertices, each adjacent in $G$
to two distinct vertices of $T$, with $|Y| > (1/2 - \varepsilon)n$.

This claim (Erdős Problem 1034) was disproved by Ma and Tang. -/
def conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
        JoinedToTwo G T Y ∧ (1 / 2 - ε) * (n : ℝ) < (Y.card : ℝ)

/-- **Negation of the Erdős–Faudree triangle conjecture.** The proposition that the
Erdős–Faudree triangle conjecture fails, that is, that it is not the case that for every real
$\varepsilon > 0$ and all sufficiently large $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges contains a triangle $T$ and a set $Y$ of
vertices, each adjacent in $G$ to two distinct vertices of $T$, with $|Y| > (1/2 - \varepsilon)n$.
-/
def disprovedForm : Prop := ¬ conjecture

/-- **Book lower bound for Erdős Problem 1034.** For every real $\varepsilon > 0$ the following
holds for all sufficiently large $n$: every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges contains a triangle $T$ and a set $Y$ of
vertices, each adjacent in $G$ to two distinct vertices of $T$, with
$|Y| \ge (1/6 - \varepsilon)n$. -/
def bookLowerBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

/-- **Ma–Tang upper bound for Erdős Problem 1034.** For every real $\varepsilon > 0$ the following
holds for all sufficiently large $n$: there is a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges such that for every triangle $T$ of $G$, every
set $Y$ of vertices each adjacent in $G$ to two distinct vertices of $T$ satisfies
$|Y| \le (2 - \sqrt{5/2} + \varepsilon)n$. -/
def maTangUpperBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y →
          (Y.card : ℝ) ≤ (2 - Real.sqrt (5 / 2) + ε) * (n : ℝ)

/-- **$K_4$-free upper bound for Erdős Problem 1034.** For every real $\varepsilon > 0$ the
following holds for all sufficiently large $n$: there is a simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ that contains no $K_4$ and has more than $n^2/4$ edges, such that for every
triangle $T$ of $G$, every set $Y$ of vertices each adjacent in $G$ to two distinct vertices of
$T$ satisfies $|Y| \le (2\sqrt{3} - 3 + \varepsilon)n$. -/
def k4FreeUpperBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y →
          (Y.card : ℝ) ≤ (2 * Real.sqrt 3 - 3 + ε) * (n : ℝ)

/--
**The Erdős–Faudree triangle conjecture is false.** It is not true that for every real
$\varepsilon > 0$ and all sufficiently large $n$, every simple graph on the vertex set
$\{0, \dots, n-1\}$ with more than $n^2/4$ edges contains a triangle $T$ and a set of more than
$(1/2 - \varepsilon)n$ vertices, each adjacent to two distinct vertices of $T$.

Source: Ma and Tang (disproof with upper bound (2-√(5/2)+o(1))n; K₄-free sketch with
(2√3-3+o(1))n), per erdosproblems.com/1034, https://www.erdosproblems.com/1034. Moved from
`OpenConjectures/GraphTheory/ErdosProblem1034`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.ErdosProblem1034Wanted
