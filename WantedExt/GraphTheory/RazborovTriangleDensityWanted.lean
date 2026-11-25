/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Combinatorics.SimpleGraph.RazborovTriangleFunction

/-!
# Razborov's minimum triangle density theorem

For an edge density `a ∈ [0, 1]`, Razborov proved that the asymptotically minimal triangle
density `g₃(a)` of graphs with edge density `a` equals the function `h(a)`
(`razborovTriangleDensity`) given by complete multipartite graphs, settling the
Lovász-Simonovits form of a question of Erdős (1955). The proof was one of the first
major applications of flag algebras. The matching upper bound `g₃(a) ≤ h(a)` comes from the
construction described in `razborovTriangleDensity`; the statement below is the lower bound,
which is Razborov's contribution, in a finite `ε`-`N` form: for large `n`, every graph on `n`
vertices with at least `a C(n, 2)` edges has at least `(h(a) - ε) C(n, 3)` triangles. Because
`g₃(m, n)` is non-decreasing in the number of edges `m`, this form follows from `g₃(a) ≥ h(a)`.

Goodman's bound (`MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound.goodman`) gives
`g₃(a) ≥ a (2 a - 1)`, tight only at `a = 1 - 1/t`.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.RazborovTriangleDensityWanted

open Finset MathlibExt.Combinatorics.SimpleGraph.RazborovTriangleFunction

/-- **Razborov's minimum triangle density theorem.** For every edge density `a ∈ [0, 1]` and
every `ε > 0` there is `N` such that every simple graph on `n ≥ N` vertices with at least
`a C(n, 2)` edges has at least `(h(a) - ε) C(n, 3)` triangles, where `h` is
`razborovTriangleDensity`. Equivalently `g₃(a) ≥ h(a)` for the limit
`g₃(a) = lim_n g₃(⌊a C(n, 2)⌋, n) / C(n, 3)` (A. A. Razborov, *On the minimal density of
triangles in graphs*, Combin. Probab. Comput. 17 (2008), 603-618; the value of `g₃` and the
lower bound are restated in Pikhurko and Razborov, Combin. Probab. Comput. 26 (2017),
arXiv:1204.2846v2, equations (1)-(4) and the paragraph after (4)). -/
public theorem_wanted razborov_minimum_triangle_density (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      a * (n.choose 2 : ℝ) ≤ (#G.edgeFinset : ℝ) →
        (razborovTriangleDensity a - ε) * (n.choose 3 : ℝ) ≤ (#(G.cliqueFinset 3) : ℝ)

end MathlibExt.GraphTheory.RazborovTriangleDensityWanted
