/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.GridDominationTransferMatrix
public import MathlibExt.Combinatorics.SimpleGraph.TorusDominationTransfer

/-!
# Transfer matrices for domination polynomials of grids and cylinders

Statements from Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the
Torus, and the King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Section 2.

A row of width `m` is the path graph `pathGraph m` (grid) or the cycle graph `cycleGraph m`
(cylinder); the `m × n` grid and cylinder are the box products
`pathGraph m □ pathGraph n` and `cycleGraph m □ pathGraph n`, with rows indexed by the second
coordinate. Signatures, compatibility and the transfer matrix are stated for an arbitrary row graph
`R`; for `R = pathGraph m` (resp. `R = cycleGraph m`) they are the paper's (cyclic) signatures,
Definitions 3, 5 and 6.
-/

open Polynomial SimpleGraph

namespace MetaMathlibExt

@[expose] public section

open DominationState

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

end

end MetaMathlibExt
