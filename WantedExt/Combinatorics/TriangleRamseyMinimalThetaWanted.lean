/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum degree of triangle-Ramsey-minimal graphs

`AIM-COMBINATORICS-0060` (AIM Graph Ramsey theory, Ramsey minimal
graphs, item 13): `s_r(3) = Θ(r² log r)` as `r → ∞`, where `s_r(3)`
is the least minimum degree of an `r`-Ramsey-minimal graph for the
triangle.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Basic.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleRamseyMinimalThetaWanted

/-- **Ramsey graphs for the triangle.** A graph $G$ on the vertex set $\{0, \dots, n - 1\}$ is
$r$-Ramsey for the triangle when every colouring $c$ of the ordered pairs of vertices with $r$
colours that is symmetric ($c(a, b) = c(b, a)$) admits three distinct vertices $u, v, w$ that form
a triangle in $G$ with $c(u, v) = c(v, w) = c(w, u)$.

For $r \ge 1$ this says that every colouring of the edges of $G$ with $r$ colours has a
monochromatic triangle.

Source: [AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13,
Section Ramsey minimal graphs, Workshop Graph Ramsey theory. -/
def IsTriangleRamsey (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Fin r,
    (∀ a : Fin n, ∀ b : Fin n, c a b = c b a) →
      ∃ u : Fin n, ∃ v : Fin n, ∃ w : Fin n,
        u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧
          c u v = c v w ∧ c v w = c w u

/-- **Ramsey property for the triangle after deleting a vertex.** Let $G$ be a graph on the vertex
set $\{0, \dots, n - 1\}$, $r$ a natural number and $x$ a vertex. The property holds when every
colouring $c$ of the ordered pairs of vertices with $r$ colours that is symmetric
($c(a, b) = c(b, a)$) admits three distinct vertices $u, v, w$, all different from $x$, that form a
triangle in $G$ with $c(u, v) = c(v, w) = c(w, u)$.

Source: [AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13,
Section Ramsey minimal graphs, Workshop Graph Ramsey theory. -/
def IsTriangleRamseyDeleteVertex (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ)
    (x : Fin n) : Prop :=
  ∀ c : Fin n → Fin n → Fin r,
    (∀ a : Fin n, ∀ b : Fin n, c a b = c b a) →
      ∃ u : Fin n, ∃ v : Fin n, ∃ w : Fin n,
        u ≠ x ∧ v ≠ x ∧ w ≠ x ∧
          u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧
          c u v = c v w ∧ c v w = c w u

/-- **Ramsey-minimal graphs for the triangle.** A graph $G$ on the vertex set $\{0, \dots, n - 1\}$
is $r$-Ramsey-minimal for the triangle when $G$ is $r$-Ramsey for the triangle, no proper spanning
subgraph of $G$ (a graph on the same vertices whose edges are edges of $G$, missing at least one
of them) is $r$-Ramsey for the triangle, and for every vertex $x$ it is false that every symmetric
colouring of the ordered pairs of vertices with $r$ colours admits a triangle of $G$ avoiding $x$
whose three edges have the same colour.

Given the first two conditions, the last one says exactly that $G$ has no isolated vertices.

Source: [AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13,
Section Ramsey minimal graphs, Workshop Graph Ramsey theory. -/
def IsRamseyMinimal (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  IsTriangleRamsey n G r ∧
    (∀ H : SimpleGraph (Fin n),
      (∀ u : Fin n, ∀ v : Fin n, H.Adj u v → G.Adj u v) →
        (∃ u : Fin n, ∃ v : Fin n, G.Adj u v ∧ ¬ H.Adj u v) →
          ¬ IsTriangleRamsey n H r) ∧
    ∀ x : Fin n, ¬ IsTriangleRamseyDeleteVertex n G r x

/-- **Minimum degree of a finite graph.** A graph $G$ on the vertex set $\{0, \dots, n - 1\}$ has
minimum degree $d$ when every vertex of $G$ has at least $d$ neighbours and some vertex of $G$ has
exactly $d$ neighbours; in particular $n \ge 1$.

Source: [AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13,
Section Ramsey minimal graphs, Workshop Graph Ramsey theory. -/
def HasMinDegree (n : ℕ) (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  (∀ v : Fin n, d ≤ Set.ncard { w : Fin n | G.Adj v w }) ∧
    ∃ v : Fin n, Set.ncard { w : Fin n | G.Adj v w } = d

/-- **Least minimum degree of Ramsey-minimal graphs for the triangle.** For a natural number $r$,
$s_r(K_3)$ is the least natural number $d$ such that, for some $n$, some graph on the vertex set
$\{0, \dots, n - 1\}$ is $r$-Ramsey-minimal for the triangle and has minimum degree $d$; if no
such graph exists, $s_r(K_3) = 0$.

Source: [AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13,
Section Ramsey minimal graphs, Workshop Graph Ramsey theory, Conjecture
`$s_r(3) = \Theta(r^2 \log r)$`. -/
noncomputable def sRamsey (r : ℕ) : ℕ := by
  classical
  exact if h : ∃ d : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      IsRamseyMinimal n G r ∧ HasMinDegree n G d then Nat.find h else 0

/-- **Minimum-degree conjecture for minimal Ramsey graphs of the triangle.** The statement that
$s_r(K_3) = \Theta(r^2 \log r)$ as the natural number $r$ tends to infinity, where $s_r(K_3)$ is
the least minimum degree of a graph that is $r$-Ramsey-minimal for the triangle ($0$ if there is
none) and $\log$ is the natural logarithm: there are constants $c, C > 0$ such that
$c \, r^2 \log r \le s_r(K_3) \le C \, r^2 \log r$ for all sufficiently large $r$.

Source: [AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13,
Section Ramsey minimal graphs, Workshop Graph Ramsey theory, Canonical tag conjecture. -/
def conjecture : Prop :=
  Asymptotics.IsTheta Filter.atTop
    (fun r : ℕ => (sRamsey r : ℝ))
    (fun r : ℕ => (r : ℝ) ^ 2 * Real.log (r : ℝ))

/-- **Minimum degree of minimal Ramsey graphs for the triangle (Guo–Warnke).** Let $s_r(K_3)$ be
the least minimum degree of a graph that is $r$-Ramsey-minimal for the triangle, with
$s_r(K_3) = 0$ if there is no such graph, as defined for the conjecture. Then
$s_r(K_3) = \Theta(r^2 \log r)$ as the natural number $r$ tends to infinity, where $\log$ is the
natural logarithm: there are constants $c, C > 0$ such that
$c \, r^2 \log r \le s_r(K_3) \le C \, r^2 \log r$ for all sufficiently large $r$.

Resolved true: Guo and Warnke (Packing nearly optimal Ramsey R(3,t) graphs, arXiv:1711.05877)
prove this, confirming the conjecture of Fox, Grinshpun, Liebenau, Person and Szabó.

Source: H. Guo and L. Warnke, Packing nearly optimal
Ramsey R(3,t) graphs, arXiv:1711.05877, https://arxiv.org/abs/1711.05877. Moved from
`OpenConjectures/Combinatorics/TriangleRamseyMinimalTheta`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.TriangleRamseyMinimalThetaWanted
