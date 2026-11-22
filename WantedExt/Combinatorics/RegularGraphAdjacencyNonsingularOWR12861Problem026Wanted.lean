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
/-- The proportion, among the `d`-regular simple graphs on the vertex set `Fin n`, of those whose
adjacency matrix is nonsingular (over `ℚ`, equivalently over `ℝ`). This is the probability that the
adjacency matrix of the uniformly random `d`-regular graph `G(n, d)` is nonsingular. -/
noncomputable def nonsingularFraction (d n : ℕ) : ℝ :=
  (Nat.card {G : SimpleGraph (Fin n) // G.IsRegularOfDegree d ∧ (G.adjMatrix ℚ).det ≠ 0} : ℝ) /
    Nat.card {G : SimpleGraph (Fin n) // G.IsRegularOfDegree d}

/-- Vu's problem (Oberwolfach Report 01/2014): for every fixed `d > 2`, the adjacency matrix of the
uniformly random `d`-regular graph on `n` vertices is nonsingular with probability tending to `1`
as `n → ∞` (along the `n` with `n d` even, for which `d`-regular graphs on `n` vertices exist). -/
def regularGraphAdjacencyNonsingular : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    Tendsto (fun n => nonsingularFraction d n) (atTop ⊓ 𝓟 {n | Even (n * d)}) (𝓝 1)

/--
Resolved true: Huang proved that for every fixed `d ≥ 3` the adjacency matrix of a random
`d`-regular directed or undirected graph on `n` vertices is singular with probability at most
`n^(-c)` for some `c > 0` and all large `n`, in the configuration model and, by contiguity, in the
uniform model. Source: V. Vu, problem (1) of the problem session, in Combinatorics, Oberwolfach
Reports 11 (2014), Report 01/2014, pp. 84-85, DOI 10.4171/OWR/2014/01; resolution: J. Huang,
Invertibility of adjacency matrices for random d-regular graphs, Duke Math. J. 170 (2021), no. 18,
3977-4032, DOI 10.1215/00127094-2021-0006, arXiv:1807.06465, Theorem 1.3: for fixed d ≥ 3, P(A is
singular in R) ≤ n^(-c) for n sufficiently large (directed and undirected d-regular graphs); Section
1.1: by a contiguity argument the results hold for the uniform model,
https://arxiv.org/abs/1807.06465.
-/
public theorem_wanted regularGraphAdjacencyNonsingular_holds : regularGraphAdjacencyNonsingular

end MathlibExt.Combinatorics.RegularGraphAdjacencyNonsingularOWR12861Problem026Wanted
