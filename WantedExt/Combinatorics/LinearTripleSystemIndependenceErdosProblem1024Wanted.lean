/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independence number of linear triple systems (Erdős Problem 1024)

Erdős Problem 1024: let `f(n)` be such that every `3`-uniform linear hypergraph on `n` vertices
contains an independent set on `f(n)` vertices. Estimate `f(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1024, https://www.erdosproblems.com/1024 (status
SOLVED). UnsolvedMath record UM-30007131 (`EP-1024`), dataset ulamai/UnsolvedMath v1.8.0.

`f(n)` is read as the largest such size, which is finite since independent sets have at most `n`
vertices. A linear hypergraph has edges of size `3` meeting pairwise in at most one vertex; an
independent set contains no edge. The estimate is stated as `f(n) ≍ (n log n)^{1/2}`
(`Asymptotics.IsTheta`). Compared with the formal-conjectures statement `ErdosProblems/1024.lean`
(equivalent; no code imported).
-/

/-- **Linear triple systems.** A finite family $H$ of subsets of $\{0, \dots, n-1\}$ is a linear
triple system (a $3$-uniform linear hypergraph, or partial Steiner triple system) when every
member of $H$ has exactly three elements and any two distinct members of $H$ share at most one
element. -/
def IsLinearTripleSystem {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = 3) ∧ ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (e ∩ e').card ≤ 1

/-- **Independence number of linear triple systems.** For $n \in \mathbb{N}$, $f(n)$ is the largest
$m \in \mathbb{N}$ such that every linear triple system $H$ on the vertex set $\{0, \dots, n-1\}$
has an independent set of size at least $m$: a set $I$ of at least $m$ vertices such that no
triple of $H$ is a subset of $I$. The largest such $m$ exists because $m = 0$ qualifies and no
such $m$ exceeds $n$. -/
noncomputable def linearTripleIndependence (n : ℕ) : ℕ :=
  sSup {m | ∀ H : Finset (Finset (Fin n)), IsLinearTripleSystem H →
    ∃ I : Finset (Fin n), m ≤ I.card ∧ ∀ e ∈ H, ¬ e ⊆ I}

/-- **Erdős Problem 1024: the Phelps–Rödl asymptotic.** For $n \in \mathbb{N}$ let $f(n)$ be the
independence number of linear triple systems on $n$ vertices: the largest $m$ such that every
linear triple system on $n$ vertices has an independent set (a set of vertices containing no
triple of the system) of at least $m$ vertices. This is the statement that
$f(n) = \Theta(\sqrt{n \log n})$ as $n \to \infty$, that is, $f(n) = O(\sqrt{n \log n})$ and
$\sqrt{n \log n} = O(f(n))$. -/
def linearTripleIndependenceAsymp : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (linearTripleIndependence n : ℝ))
    (fun n : ℕ => Real.sqrt (n * Real.log n))

/--
**Phelps–Rödl theorem on independence in linear triple systems.** For $n \in \mathbb{N}$ let
$f(n)$ be the largest $m$ such that every linear triple system on $\{0, \dots, n-1\}$ (a family
of $3$-element sets, any two distinct ones sharing at most one element) has an independent set of
at least $m$ vertices, that is, a set of at least $m$ vertices containing no triple of the system.
Then $f(n) = \Theta(\sqrt{n \log n})$ as $n \to \infty$: there are constants $c, C > 0$ such that
$c \sqrt{n \log n} \le f(n) \le C \sqrt{n \log n}$ for all sufficiently large $n$.

Erdős had shown $n^{1/2} \ll f(n) \ll n^{2/3}$.

Source: T. F. Bloom, Erdős Problems, Problem #1024,
https://www.erdosproblems.com/1024 (status SOLVED); resolution: K. T. Phelps and V. Rödl, Steiner
triple systems with minimum independence number, Ars Combin. (1986), 167-172, f(n) ≍ (n log n)^{1/2}
(erdosproblems.com/1024), https://www.erdosproblems.com/1024.
-/
public theorem_wanted linearTripleIndependenceAsymp_holds : linearTripleIndependenceAsymp

end MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
