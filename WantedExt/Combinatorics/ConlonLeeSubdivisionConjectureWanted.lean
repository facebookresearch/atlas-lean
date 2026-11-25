/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OWR-16931-006`
# The Conlon–Lee conjecture on extremal numbers of subdivisions

Combinatorics, Probability and Computing (2020), Oberwolfach Reports, DOI 10.4171/owr/2019/19, pp.
1113--1189.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ConlonLeeSubdivisionConjectureWanted

/-- **The $(k-1)$-subdivision of a graph.** For a simple graph $H$ on the vertex set
$\{0, \dots, m - 1\}$ and a natural number $k \ge 2$, the $(k-1)$-subdivision $H^{k-1}$ is the
graph obtained from $H$ by replacing each edge $ij$ with $i < j$ by a path
$i, (ij, 0), (ij, 1), \dots, (ij, k - 2), j$ of length $k$ through $k - 1$ new vertices, the paths
of different edges sharing no new vertices. For $k \le 1$ there are no new vertices and the
resulting graph has no edges. -/
def subdivision {m : ℕ} (H : SimpleGraph (Fin m)) (k : ℕ) :
    SimpleGraph (Fin m ⊕ ({p : Fin m × Fin m // p.1 < p.2 ∧ H.Adj p.1 p.2} × Fin (k - 1))) :=
  SimpleGraph.fromRel fun u v => match u, v with
    | .inl i, .inr (e, t) => e.1.1 = i ∧ (t : ℕ) = 0
    | .inr (e, t), .inr (e', t') => e = e' ∧ (t' : ℕ) = t + 1
    | .inr (e, t), .inl j => e.1.2 = j ∧ (t : ℕ) = k - 2
    | _, _ => False

/-- **Containing a copy of a graph.** A simple graph $G$ contains a copy of a simple graph $F$ if
there is an injective map $f$ from the vertices of $F$ to the vertices of $G$ such that $f(u)$ and
$f(v)$ are adjacent in $G$ whenever $u$ and $v$ are adjacent in $F$; the copy need not be induced.
-/
def ContainsCopy {V W : Type} (F : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ f : V ↪ W, ∀ u v, F.Adj u v → G.Adj (f u) (f v)

open Classical in
/-- **The extremal number of a graph.** For a natural number $n$ and a simple graph $F$, the
extremal number $\mathrm{ex}(n, F)$ is the maximum number of edges of a simple graph on the vertex
set $\{0, \dots, n - 1\}$ that contains no copy of $F$. It is $0$ when every simple graph on these
$n$ vertices contains a copy of $F$. -/
noncomputable def ex {V : Type} (n : ℕ) (F : SimpleGraph V) : ℕ :=
  sSup {e | ∃ G : SimpleGraph (Fin n), ¬ ContainsCopy F G ∧ G.edgeFinset.card = e}

/-- **The Conlon–Lee subdivision conjecture.** For a simple graph $H$ and a natural number $k$,
write $H^{k-1}$ for the $(k-1)$-subdivision of $H$, and for a simple graph $F$ and a natural
number $n$ write $\mathrm{ex}(n, F)$ for the extremal number of $F$ on $n$ vertices. The
conjecture is the statement that for every even natural number $k \ge 2$, every natural number
$m$ and every simple graph $H$ on the vertex set $\{0, \dots, m - 1\}$, there are real numbers
$\delta > 0$ and $C$ such that $\mathrm{ex}(n, H^{k-1}) \le C \cdot n^{1 + 1/k - \delta}$ for
every natural number $n$. In other words, $\mathrm{ex}(n, H^{k-1}) = O(n^{1 + 1/k - \delta})$
for some $\delta > 0$. -/
def conjecture : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 2 ≤ k → Even k → ∃ δ > (0 : ℝ), ∃ C : ℝ, ∀ n : ℕ,
    (ex n (subdivision H k) : ℝ) ≤ C * (n : ℝ) ^ (1 + 1 / (k : ℝ) - δ)

-- Carried source audit `OWR-16931-006` (see the Moved/ record).

/-- **The Conlon–Lee subdivision conjecture holds.** For a simple graph $F$ and a natural number
$n$, let $\mathrm{ex}(n, F)$ be the maximum number of edges of a simple graph on $n$ vertices
that contains no copy of $F$ (not necessarily induced), or $0$ if there is no such graph. For a
simple graph $H$ and a natural number $k \ge 2$, let $H^{k-1}$ be the graph obtained from $H$ by
replacing each edge with a path of length $k$ through $k - 1$ new vertices (internally disjoint
for different edges). Then for every even natural number $k \ge 2$, every natural number $m$ and
every simple graph $H$ on the vertex set $\{0, \dots, m - 1\}$, there are real numbers
$\delta > 0$ and $C$ such that $\mathrm{ex}(n, H^{k-1}) \le C \cdot n^{1 + 1/k - \delta}$ for
every natural number $n$.

This was proved by Janzer (Bull. London Math. Soc. 53 (2021) 108–118, Theorem 1.7).

Source: O. Janzer, The extremal number of longer subdivisions, Bull. London
Math. Soc. 53 (2021) 108-118, arXiv:1905.08001, https://doi.org/10.1112/blms.12404. Moved from
`OpenConjectures/Combinatorics/ConlonLeeSubdivisionConjecture`. -/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ConlonLeeSubdivisionConjectureWanted
