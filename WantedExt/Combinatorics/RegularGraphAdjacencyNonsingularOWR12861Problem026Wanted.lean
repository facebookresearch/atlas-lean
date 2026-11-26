/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nonsingularity of adjacency matrices of random regular graphs (Oberwolfach Reports 01/2014)

Oberwolfach workshop Combinatorics (2014), problem session, V. Vu, problem (1): let `A(n, d)` be the
adjacency matrix of the random regular graph `G(n, d)`, `d > 2`; then `A(n, d)` is non-singular with
probability tending to `1` as `n` tends to infinity.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.RegularGraphAdjacencyNonsingularOWR12861Problem026Wanted

/-!
Source: V. Vu, problem (1) of the problem session, in Combinatorics, Oberwolfach Reports 11 (2014),
Report 01/2014, pp. 84-85, DOI 10.4171/OWR/2014/01. UnsolvedMath record UM-30002475
(`OWR-12861-026`), dataset ulamai/UnsolvedMath v1.8.0.

`G(n, d)` is the uniformly random `d`-regular simple graph on `n` labeled vertices, so the
probability is the proportion of `d`-regular graphs on `Fin n` whose adjacency matrix has nonzero
determinant (over `ℚ`, equivalently over `ℝ`). The limit runs along the `n` with `n d` even, the
only `n` for which `d`-regular graphs on `n` vertices exist. The record's two further questions (the
limiting distributions of the permanent of a random `±1` matrix and of the determinant of a random
symmetric `±1` matrix) are not formalized.
-/

open Filter Topology

open Classical in
/-- **Proportion of regular graphs with nonsingular adjacency matrix.** For natural numbers $d$
and $n$, this is the real number obtained by dividing the number of $d$-regular simple graphs on
the vertex set $\{0, 1, \ldots, n-1\}$ whose adjacency matrix has nonzero determinant over
$\mathbb{Q}$ by the number of all $d$-regular simple graphs on that vertex set; it is $0$ when
there is no $d$-regular simple graph on that vertex set. It is the probability that the adjacency
matrix of the uniformly random $d$-regular graph $G(n, d)$ is nonsingular.

Nonsingularity over $\mathbb{Q}$ is the same as nonsingularity over $\mathbb{R}$. -/
noncomputable def nonsingularFraction (d n : ℕ) : ℝ :=
  (Nat.card {G : SimpleGraph (Fin n) // G.IsRegularOfDegree d ∧ (G.adjMatrix ℚ).det ≠ 0} : ℝ) /
    Nat.card {G : SimpleGraph (Fin n) // G.IsRegularOfDegree d}

/-- **Vu's problem on nonsingular adjacency matrices of random regular graphs.** This is the
statement that for every natural number $d \ge 3$, the probability that the adjacency matrix of
the uniformly random $d$-regular simple graph on $n$ labeled vertices is nonsingular tends to $1$
as $n \to \infty$, where $n$ runs over the natural numbers with $nd$ even. Here the probability is
the proportion of the $d$-regular simple graphs on $\{0, 1, \ldots, n-1\}$ whose adjacency matrix
has nonzero determinant over $\mathbb{Q}$.

The restriction to $nd$ even is natural: $d$-regular graphs on $n$ vertices exist only for such
$n$. -/
def regularGraphAdjacencyNonsingular : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    Tendsto (fun n => nonsingularFraction d n) (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1)

/--
**Nonsingularity of adjacency matrices of random regular graphs.** For every natural number
$d \ge 3$, the probability that the adjacency matrix of the uniformly random $d$-regular simple
graph on $n$ labeled vertices has nonzero determinant (over $\mathbb{Q}$, equivalently over
$\mathbb{R}$) tends to $1$ as $n \to \infty$ along the natural numbers $n$ with $nd$ even.

Huang proved more: for every fixed $d \ge 3$ there is $c > 0$ such that the adjacency matrix of a
random $d$-regular directed or undirected graph on $n$ vertices is singular with probability at
most $n^{-c}$ for all large $n$, in the configuration model and, by contiguity, in the uniform
model.

Source: V. Vu, problem (1) of the problem session, in Combinatorics, Oberwolfach
Reports 11 (2014), Report 01/2014, pp. 84-85, DOI 10.4171/OWR/2014/01; resolution: J. Huang,
Invertibility of adjacency matrices for random d-regular graphs, Duke Math. J. 170 (2021), no. 18,
3977-4032, DOI 10.1215/00127094-2021-0006, arXiv:1807.06465, Theorem 1.3: for fixed d ≥ 3, P(A is
singular in R) ≤ n^(-c) for n sufficiently large (directed and undirected d-regular graphs); Section
1.1: by a contiguity argument the results hold for the uniform model,
https://arxiv.org/abs/1807.06465.
-/
public theorem_wanted regularGraphAdjacencyNonsingular_holds : regularGraphAdjacencyNonsingular

end MathlibExt.Combinatorics.RegularGraphAdjacencyNonsingularOWR12861Problem026Wanted
