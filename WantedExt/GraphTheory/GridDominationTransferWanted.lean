/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import MathlibExt.Combinatorics.SimpleGraph.GridDominationTransfer

/-!
# Transfer matrices for domination polynomials of grids, cylinders and tori

Statements from Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the
Torus, and the King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 2.

A row of width `m` is the path graph `pathGraph m` (grid) or the cycle graph `cycleGraph m`
(cylinder and torus); the `m × n` grid, cylinder and torus are the box products
`pathGraph m □ pathGraph n`, `cycleGraph m □ pathGraph n` and `cycleGraph m □ cycleGraph n`,
with rows indexed by the second coordinate.  Signatures, compatibility and the transfer matrix
are stated for an arbitrary row graph `R`; for `R = pathGraph m` (resp. `R = cycleGraph m`)
they are the paper's (cyclic) signatures, Definitions 3, 5 and 6.
-/

open Polynomial SimpleGraph

namespace MetaMathlibExt

@[expose] public section

open DominationState

open scoped Classical in
/-- **Transfer-matrix formula for the domination polynomial of the grid.** For all natural
numbers $m$ and $n$, let $P_k$ denote the path on the vertices $0, \dots, k - 1$, let $A$ be the
domination transfer matrix of the row graph $P_m$, indexed by the signatures of $P_m$, and let
$\sigma_\bullet$ be the all-covered signature. Then the domination polynomial of the grid
$P_m \mathbin{\square} P_n$ is

$$\sum_\sigma (A^n)_{\sigma, \sigma_\bullet},$$

the sum running over the signatures $\sigma$ of $P_m$ with no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
public theorem_wanted dominationPolynomial_grid_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (pathGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (pathGraph m) ^ n) σ (allCoveredSignature _)

open scoped Classical in
/-- **Transfer-matrix formula for the domination polynomial of the cylinder.** For all natural
numbers $m$ and $n$, let $C_m$ be the cycle graph on the vertices $0, \dots, m - 1$, in which
distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod m$, and let $P_n$ be the path on
the vertices $0, \dots, n - 1$. Let $\bar A$ be the domination transfer matrix of the row graph
$C_m$, indexed by the signatures of $C_m$, and let $\sigma_\bullet$ be the all-covered signature.
Then the domination polynomial of the cylinder $C_m \mathbin{\square} P_n$ is

$$\sum_\sigma (\bar A^n)_{\sigma, \sigma_\bullet},$$

the sum running over the signatures $\sigma$ of $C_m$ with no uncovered vertex.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 7
(`jis-2024-24.7.6-thm-7`). -/
public theorem_wanted dominationPolynomial_cylinder_eq_sum_transferMatrix_pow (m n : ℕ) :
    dominationPolynomial (cycleGraph m □ pathGraph n) =
      ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph m))).filter
          (fun σ => ∀ i, σ.1 i ≠ uncovered),
        (dominationTransferMatrix (cycleGraph m) ^ n) σ (allCoveredSignature _)

/-- **Transfer-matrix formula for the domination polynomial of the torus.** For all natural
numbers $m$ and $n$ with $n \ge 1$, let $C_k$ denote the cycle graph on the vertices
$0, \dots, k - 1$, in which distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod k$,
and let $\bar A$ be the domination transfer matrix of the row graph $C_m$. Then the domination
polynomial of the torus $C_m \mathbin{\square} C_n$ equals the trace of $\bar A^n$.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the trace counts the signatures of $C_m$, while
the torus $C_m \mathbin{\square} C_0$ has no vertices, so its domination polynomial is $1$. For
$n = 1$ and $n = 2$ the cycle $C_n$ is a single vertex and a single edge respectively.

Source: Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the
King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 8
(`jis-2024-24.7.6-thm-8`). -/
public theorem_wanted dominationPolynomial_torus_eq_trace_transferMatrix_pow (m n : ℕ)
    (hn : 1 ≤ n) :
    dominationPolynomial (cycleGraph m □ cycleGraph n) =
      Matrix.trace (dominationTransferMatrix (cycleGraph m) ^ n)

end

end MetaMathlibExt
